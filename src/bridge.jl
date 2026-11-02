# To and from CellularAutomataCore. A periodic lattice of size (n1, …, nd) is the torus group
# Z_n1 × … × Z_nd (a hexagonal grid too, in axial coordinates); a neighbourhood offset o is the element
# o mod n, and an element g the centred offset in (-n/2, n/2]. A deterministic core rule that does not
# depend on the cell's position or the time is a cellular automaton over that group, and back.

"""
    torus_group(space) -> CyclicGroup or TorusGroup

The group of translations of a periodic CellularAutomataCore lattice (`Torus`,
or a `HexGrid` with periodic edges): `CyclicGroup(n)` in one dimension,
`TorusGroup(n1, …, nd)` otherwise. Raises `ArgumentError` for a lattice with
non-periodic edges, which is not a group.
"""
function torus_group(space::CAC.Lattice)
    all(b -> b isa CAC.Periodic, CAC.boundaries(space)) ||
        throw(ArgumentError("only a lattice with periodic edges is a group; got $space"))
    dims = size(space)
    return length(dims) == 1 ? CyclicGroup(dims[1]) : TorusGroup(dims)
end

"""
    torus_space(G) -> Torus

The CellularAutomataCore `Torus` whose cells are the elements of a cyclic or
torus group.
"""
torus_space(G::CyclicGroup) = CAC.Torus(G.n)
torus_space(G::TorusGroup) = CAC.Torus(G.dims...)

_element(G::CyclicGroup, o::CartesianIndex{1}) = mod(o[1], G.n)
_element(G::TorusGroup, o::CartesianIndex) = mod.(Tuple(o), G.dims)
_centred(g, n) = g <= n ÷ 2 ? g : g - n
_offset(G::CyclicGroup, g) = CartesianIndex(_centred(g, G.n))
_offset(G::TorusGroup, g) = CartesianIndex(_centred.(g, G.dims))

"""
    CellularAutomaton(rule, space; alphabet, codom=alphabet, p=nothing)

The cellular automaton over [`torus_group`](@ref)`(space)` given by a
CellularAutomataCore rule (`Life()`, `Wolfram(30)`, a `LocalRule`, ...) on a
periodic lattice: its memory set is the identity (the cell itself) followed by
the rule's neighbourhood, and its local rule calls the core rule with
parameters `p`. The rule must be deterministic and must not depend on the
position of the cell or on the time: those are what make a map of
configurations a cellular automaton over a group.
"""
function CellularAutomaton(rule::CAC.AbstractRule, space::CAC.Lattice{N};
                           alphabet::FinAlphabet, codom::FinAlphabet=alphabet,
                           p=nothing) where {N}
    G = torus_group(space)
    nbhd = something(CAC.neighbourhood(rule), CAC.default_neighbourhood(space))
    els = [_element(G, o) for o in CAC.neighbourhood_offsets(nbhd, space)]
    memory = unique([identity_element(G); els])
    pos = _positions(els, memory)
    ctx = CAC.CellContext(p, CartesianIndex(ntuple(_ -> 1, N)), 0, 1, 0)
    T = eltype(codom)
    μ = y -> convert(T, CAC.local_rule(rule, y[1], Tuple(y[i] for i in pos), ctx))
    return CellularAutomaton(G, memory, μ; dom=alphabet, codom)
end

"""
    LocalRule(τ::CellularAutomaton)

The CellularAutomataCore rule of a cellular automaton over a cyclic or torus
group whose domain and codomain agree: its neighbourhood holds the memory set
as centred offsets (the identity is the cell itself), so it runs on every core
backend. `CAProblem(τ, u0, tspan)` builds a problem from it directly.
"""
function CAC.LocalRule(τ::CellularAutomaton{<:Union{CyclicGroup,TorusGroup}})
    τ.dom == τ.codom ||
        throw(DomainMismatchError("a core rule from a cellular automaton", τ.dom, τ.codom))
    G = τ.group
    e = identity_element(G)
    others = filter(!=(e), τ.memory)
    # a neighbourhood cannot be empty: a rule of the cell alone reads one neighbour it ignores
    offsets = isempty(others) ? [_offset(G, last(elements(G)))] :
              [_offset(G, s) for s in others]
    src = [s == e ? 0 : findfirst(==(s), others) for s in τ.memory]
    μ = τ.rule
    return CAC.LocalRule((c, n, ctx) -> μ(Tuple(k == 0 ? c : n[k] for k in src)),
                         CAC.Offsets(offsets))
end

"""
    CAProblem(τ::CellularAutomaton, u0, tspan, p=NullParameters(); kwargs...)

A CellularAutomataCore problem that iterates the cellular automaton `τ` (over a
cyclic or torus group, with equal domain and codomain) from `u0`, a
[`Configuration`](@ref) or an array, on [`torus_space`](@ref)`(group(τ))`.
Other keywords are those of the core `CAProblem`; solve it with any backend.
"""
function CAC.CAProblem(τ::CellularAutomaton{<:Union{CyclicGroup,TorusGroup}}, u0, tspan,
                       args...; kwargs...)
    u = u0 isa Configuration ? parent(u0) : u0
    return CAC.CAProblem(CAC.LocalRule(τ), u, tspan, args...; space=torus_space(τ.group),
                         kwargs...)
end
