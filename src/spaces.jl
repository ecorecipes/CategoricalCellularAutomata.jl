# Geometries beyond groups. A space is a finite set of cells, each with an ordered list of
# neighbours: a coalgebra of the list functor (of X ↦ X^k when every cell has k neighbour slots).
# Square and hexagonal tori are Cayley coalgebras of the same group with different generators;
# reflecting edges are quotients of a doubled torus by reflections; constant edges add pinned cells
# whose state never changes; graphs are lists of varying length. A map of spaces that preserves
# neighbours (up to a permutation of the slots of each cell) pulls configurations back, and pulling
# back commutes with every cellular automaton whose local rule is invariant under those
# permutations: a local rule is a natural transformation between configuration functors.

"""
    NeighbourhoodSpace(neighbours; pinned=Dict{Int,Any}())

A finite space: cells `1:n` (the free cells, in the order of a
CellularAutomataCore state, first axis fastest) followed by pinned cells, each
with its neighbours as an ordered list of cells. A pinned cell holds a fixed
value (`pinned[cell]`), the state beyond a `Constant` edge; its neighbours are
itself. Built with [`neighbourhood_space`](@ref); a configuration is a vector
over the free cells.

As a mathematical object, a space whose cells all have `k` neighbour slots is
a coalgebra of `X ↦ X^k`, and a space with lists of varying length (a graph)
a coalgebra of the list functor; [`SpaceMorphism`](@ref)s are the maps between
them.
"""
struct NeighbourhoodSpace
    neighbours::Vector{Vector{Int}}
    pinned::Dict{Int,Any}
    function NeighbourhoodSpace(neighbours::Vector{Vector{Int}};
                                pinned::AbstractDict=Dict{Int,Any}())
        n = length(neighbours)
        for (i, ns) in enumerate(neighbours), j in ns
            1 <= j <= n || throw(ArgumentError("cell $i has neighbour $j outside 1:$n"))
        end
        for (c, v) in pinned
            1 <= c <= n || throw(ArgumentError("pinned cell $c outside 1:$n"))
        end
        free = n - length(pinned)
        all(c -> c > free, keys(pinned)) ||
            throw(ArgumentError("pinned cells must come after the free cells"))
        return new(neighbours, Dict{Int,Any}(pinned))
    end
end

"""
    free_cells(S::NeighbourhoodSpace) -> Int

The number of cells of `S` that are not pinned: the length of a configuration.
"""
free_cells(S::NeighbourhoodSpace) = length(S.neighbours) - length(S.pinned)

function Base.show(io::IO, S::NeighbourhoodSpace)
    k = unique(length.(S.neighbours[1:free_cells(S)]))
    slots = length(k) == 1 ? "$(only(k)) neighbour slots" :
            "neighbour lists of $(extrema(k)) cells"
    pins = isempty(S.pinned) ? "" : ", $(length(S.pinned)) pinned"
    return print(io, "NeighbourhoodSpace(", free_cells(S), " cells, ", slots, pins, ")")
end
function Base.:(==)(S::NeighbourhoodSpace, T::NeighbourhoodSpace)
    return S.neighbours == T.neighbours &&
           S.pinned == T.pinned
end

# One axis of a lattice: the index read at position j, or `nothing` beyond a Constant edge.
_axis(::CAC.Periodic, j, n) = mod1(j, n)
function _axis(::CAC.Reflecting, j, n)
    m = mod(j - 1, 2n)
    return m < n ? m + 1 : 2n - m
end
_axis(::CAC.Constant, j, n) = 1 <= j <= n ? j : nothing

"""
    neighbourhood_space(space, neighbourhood=nothing) -> NeighbourhoodSpace
    neighbourhood_space(τ::CellularAutomaton) -> NeighbourhoodSpace

The cells of a CellularAutomataCore `space` (a lattice of any shape and edges,
or a `GraphSpace`) with the neighbours `neighbourhood` gives them (the space's
default if `nothing`), in the order the core passes them to a rule. Beyond a
`Periodic` edge a cell reads the opposite side, beyond a `Reflecting` edge
its mirror image, and beyond a `Constant` edge a pinned cell holding the
constant (one pinned cell for each constant; where several `Constant` axes are
crossed at once, the highest-numbered one's value, as in the core). On a
`GraphSpace` the neighbourhood must be `GraphNeighbours()` (or `nothing`).

The second form gives the Cayley space of a cellular automaton over a torus
or cyclic group: each cell's neighbours are the cells its memory set reads,
the identity left out.
"""
function neighbourhood_space(space::CAC.Lattice{N}, nbhd=nothing) where {N}
    nbhd = something(nbhd, CAC.default_neighbourhood(space))
    offs = collect(CAC.neighbourhood_offsets(nbhd, space))
    dims = size(space)
    bds = CAC.boundaries(space)
    lin = LinearIndices(dims)
    n = prod(dims)
    pinned = Dict{Int,Any}()
    pin_of = Dict{Any,Int}()
    pin(v) = get!(pin_of, v) do
        c = n + length(pin_of) + 1
        pinned[c] = v
        return c
    end
    neighbours = map(CartesianIndices(dims)) do I
        return map(offs) do o
            mapped = ntuple(d -> _axis(bds[d], I[d] + o[d], dims[d]), Val(N))
            outside = findlast(isnothing, mapped)
            outside === nothing && return lin[mapped...]
            return pin(bds[outside].value)
        end
    end
    lists = vec(collect(Vector{Int}, neighbours))
    for c in sort(collect(keys(pinned)))
        push!(lists, fill(c, length(offs)))
    end
    return NeighbourhoodSpace(lists; pinned)
end
function neighbourhood_space(space::CAC.GraphSpace, nbhd=nothing)
    nbhd === nothing || nbhd isa CAC.GraphNeighbours ||
        throw(ArgumentError("a GraphSpace reads its neighbours through GraphNeighbours(), not $nbhd"))
    return NeighbourhoodSpace([copy(ns) for ns in space.neighbours])
end
function neighbourhood_space(τ::CellularAutomaton{<:Union{CyclicGroup,TorusGroup}})
    G = group(τ)
    others = [m for m in τ.memory if m != identity_element(G)]
    return neighbourhood_space(torus_space(G), CAC.Offsets([_offset(G, g) for g in others]))
end

"""
    cayley_space(G, generators) -> NeighbourhoodSpace

The Cayley space of a cyclic or torus group `G` marked with `generators`
(group elements, as tuples for a torus group or integers for a cyclic one):
cell `g` reads `g + s` for each generator `s`, in order. A square torus with
von Neumann or Moore neighbours and a hexagonal torus are Cayley spaces of the
same group `Z_n × Z_m` with different generators.
"""
function cayley_space(G::Union{CyclicGroup,TorusGroup}, generators::AbstractVector)
    offs = [_offset(G, G isa CyclicGroup ? mod(s, G.n) : mod.(Tuple(s), G.dims))
            for s in generators]
    return neighbourhood_space(torus_space(G), CAC.Offsets(offs))
end

"""
    apply_local(f, S::NeighbourhoodSpace, x) -> Vector
    apply_local(rule, S, x; p=nothing) -> Vector

One synchronous step on the space `S` of the local rule `f(cell, neighbours)`
(`neighbours` a tuple in the order of each cell's list), or of a deterministic
CellularAutomataCore rule (called with parameters `p`, at time 0), from the
configuration `x` over the free cells. Pinned cells keep their values.
"""
function apply_local(f, S::NeighbourhoodSpace, x::AbstractVector)
    n = free_cells(S)
    length(x) == n ||
        throw(ArgumentError("the configuration has $(length(x)) cells, the space $n"))
    full = Vector{Any}(undef, length(S.neighbours))
    full[1:n] .= x
    for (c, v) in S.pinned
        full[c] = v
    end
    return [f(x[i], Tuple(full[j] for j in S.neighbours[i])) for i in 1:n]
end
function apply_local(rule::CAC.AbstractRule, S::NeighbourhoodSpace, x::AbstractVector;
                     p=nothing)
    out = apply_local(S, x) do c, nbrs
        ctx = CAC.CellContext(p, CartesianIndex(1), 0, 1, 0)
        return CAC.local_rule(rule, c, nbrs, ctx)
    end
    return convert(Vector{eltype(x)}, out)
end

"""
    SpaceMorphism(dom, codom, map, slots=nothing)

A map of spaces `φ: dom → codom` ([`NeighbourhoodSpace`](@ref)s): `map[y]` is
the cell of `codom` that free cell `y` of `dom` goes to, and `slots[y]` a
permutation of `y`'s neighbour slots (the identity if `slots` is `nothing`).
It preserves neighbours when the `i`-th neighbour of `y` goes to the
`slots[y][i]`-th neighbour of `φ(y)` (a pinned neighbour going to a pinned cell
with the same value): see [`is_morphism`](@ref).

Pulling configurations back along such a map ([`pullback`](@ref)) commutes
with every local rule invariant under the slot permutations: running the rule
on `codom` and pulling back gives the same as pulling back and running it on
`dom`. With identity permutations that is every rule (a morphism of
coalgebras); [`reflection_fold`](@ref) needs rules symmetric under reflection.
"""
struct SpaceMorphism
    dom::NeighbourhoodSpace
    codom::NeighbourhoodSpace
    map::Vector{Int}
    slots::Vector{Vector{Int}}
    function SpaceMorphism(dom::NeighbourhoodSpace, codom::NeighbourhoodSpace,
                           map::AbstractVector{<:Integer}, slots=nothing)
        length(map) == free_cells(dom) ||
            throw(ArgumentError("the map gives $(length(map)) images for $(free_cells(dom)) cells"))
        all(c -> 1 <= c <= free_cells(codom), map) ||
            throw(ArgumentError("the map sends a cell outside the free cells of the codomain"))
        σ = slots === nothing ?
            [collect(eachindex(dom.neighbours[y])) for y in eachindex(map)] :
            [collect(Int, s) for s in slots]
        length(σ) == length(map) ||
            throw(ArgumentError("slots has $(length(σ)) permutations for $(length(map)) cells"))
        return new(dom, codom, collect(Int, map), σ)
    end
end

function Base.show(io::IO, f::SpaceMorphism)
    return print(io, "SpaceMorphism(", f.dom, " → ", f.codom, ")")
end

# Where a cell of the domain, free or pinned, goes (0 if a pinned value has no counterpart).
function _image(f::SpaceMorphism, c)
    c <= free_cells(f.dom) && return f.map[c]
    v = f.dom.pinned[c]
    for (d, w) in f.codom.pinned
        w == v && return d
    end
    return 0
end

"""
    is_morphism(f::SpaceMorphism) -> Bool

Whether `f` preserves neighbours: for every free cell `y` of the domain and
slot `i`, the image of `y`'s `i`-th neighbour is the `slots[y][i]`-th neighbour
of the image of `y`, and every slot permutation is a permutation of `y`'s
slots of the right length.
"""
function is_morphism(f::SpaceMorphism)
    for y in 1:free_cells(f.dom)
        ny, nx = f.dom.neighbours[y], f.codom.neighbours[f.map[y]]
        σ = f.slots[y]
        (length(ny) == length(nx) == length(σ) && sort(σ) == eachindex(σ)) || return false
        for i in eachindex(ny)
            _image(f, ny[i]) == nx[σ[i]] || return false
        end
    end
    return true
end

"""
    pullback(f::SpaceMorphism, x) -> Vector

The configuration on the domain of `f` that reads, at each cell, the value of
`x` at its image: `x ∘ φ`. (A method of Catlab's `pullback`.)
"""
pullback(f::SpaceMorphism, x::AbstractVector) = x[f.map]

"""
    covering(big, small, neighbourhood=nothing) -> SpaceMorphism

The covering of a periodic lattice `small` by a periodic lattice `big` whose
sides are multiples of `small`'s: cell `I` goes to `mod1(I, size(small))`. It
preserves neighbours slot by slot, so a cellular automaton on `small` is the
one on `big` restricted to periodic configurations.
"""
function covering(big::CAC.Lattice, small::CAC.Lattice, nbhd=nothing)
    all(b -> b isa CAC.Periodic, CAC.boundaries(big)) &&
    all(b -> b isa CAC.Periodic, CAC.boundaries(small)) ||
        throw(ArgumentError("a covering needs two lattices with periodic edges"))
    db, ds = size(big), size(small)
    length(db) == length(ds) && all(iszero, db .% ds) ||
        throw(ArgumentError("the sides of $big must be multiples of those of $small"))
    lin = LinearIndices(ds)
    map = [lin[CartesianIndex(mod1.(Tuple(I), ds))] for I in CartesianIndices(db)]
    return SpaceMorphism(neighbourhood_space(big, nbhd), neighbourhood_space(small, nbhd),
                         vec(map))
end

"""
    reflection_fold(space, neighbourhood=nothing) -> SpaceMorphism

A lattice with `Reflecting` edges (and periodic ones) as a quotient of a torus:
the domain is the torus with each reflecting side doubled, and a cell `y` goes
to `y` on the first half of such an axis and to its mirror image `2n + 1 - y`
on the second. On the mirrored half neighbours lie in the opposite direction,
so the slots are permuted (an offset `o` to the offset with that axis's
component negated); the neighbourhood must contain those offsets. Only rules
symmetric under these reflections commute with pulling back along it.
"""
function reflection_fold(space::CAC.Lattice{N,CAC.Square}, nbhd=nothing) where {N}
    bds = CAC.boundaries(space)
    all(b -> b isa Union{CAC.Periodic,CAC.Reflecting}, bds) ||
        throw(ArgumentError("reflection_fold needs Reflecting or Periodic edges, got $bds"))
    mirrored = map(b -> b isa CAC.Reflecting, bds)
    any(mirrored) || throw(ArgumentError("$space has no Reflecting edge to fold"))
    nbhd = something(nbhd, CAC.default_neighbourhood(space))
    dims = size(space)
    big = CAC.Torus(ntuple(d -> mirrored[d] ? 2dims[d] : dims[d], Val(N))...)
    offs = collect(CAC.neighbourhood_offsets(nbhd, space))
    slot = Dict(o => i for (i, o) in enumerate(offs))
    lin = LinearIndices(dims)
    cells = CartesianIndices(size(big))
    image = [lin[ntuple(d -> mirrored[d] && Y[d] > dims[d] ? 2dims[d] + 1 - Y[d] : Y[d],
                        Val(N))...] for Y in cells]
    slots = map(cells) do Y
        flip = ntuple(d -> mirrored[d] && Y[d] > dims[d], Val(N))
        return map(offs) do o
            o2 = CartesianIndex(ntuple(d -> flip[d] ? -o[d] : o[d], Val(N)))
            haskey(slot, o2) ||
                throw(ArgumentError("the neighbourhood is not symmetric under reflection: it has $o but not $o2"))
            return slot[o2]
        end
    end
    return SpaceMorphism(neighbourhood_space(big, nbhd), neighbourhood_space(space, nbhd),
                         vec(image), vec(slots))
end

function Base.:(==)(f::SpaceMorphism, g::SpaceMorphism)
    return f.dom == g.dom && f.codom == g.codom &&
           f.map == g.map && f.slots == g.slots
end

function _space_id(S::NeighbourhoodSpace)
    return SpaceMorphism(S, S, collect(1:free_cells(S)))
end

# f then g: cells go through both maps, and slot permutations compose (the i-th neighbour of y
# goes to the f.slots[y][i]-th neighbour of f(y), and that to the g.slots[f(y)][…]-th of g(f(y))).
function _space_compose(f::SpaceMorphism, g::SpaceMorphism)
    f.codom == g.dom ||
        throw(DomainMismatchError("composing maps of spaces", f.codom, g.dom))
    slots = [g.slots[f.map[y]][f.slots[y]] for y in eachindex(f.map)]
    return SpaceMorphism(f.dom, g.codom, g.map[f.map], slots)
end

@instance ThCategory{NeighbourhoodSpace,SpaceMorphism} begin
    dom(f::SpaceMorphism) = f.dom
    codom(f::SpaceMorphism) = f.codom
    id(S::NeighbourhoodSpace) = _space_id(S)
    compose(f::SpaceMorphism, g::SpaceMorphism) = _space_compose(f, g)
end

"""
    compose(f::SpaceMorphism, g::SpaceMorphism) -> SpaceMorphism
    id(S::NeighbourhoodSpace) -> SpaceMorphism

Neighbourhood spaces and the maps between them form a category, an instance of
Catlab's `ThCategory`: `compose(f, g)` is `f` followed by `g` (cells go through
both maps and slot permutations compose), raising
[`DomainMismatchError`](@ref) unless the codomain of `f` is the domain of `g`;
`id(S)` is the identity of `S`. Composites of maps that preserve neighbours
preserve them, and pulling back along `compose(f, g)` is pulling back along
`g`, then `f`.
"""
compose(::SpaceMorphism, ::SpaceMorphism)
