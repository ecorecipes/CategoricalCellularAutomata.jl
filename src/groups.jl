# Finite groups: the universes of cellular automata. A group fixes its elements, its multiplication and
# the array shape of a configuration over it, with `_cellindex` mapping an element to its position in
# that array, so that configurations over a torus group are exactly CellularAutomataCore states.

"""
    AbstractGroup

Supertype of groups: the finite groups that configurations live on
([`AbstractFiniteGroup`](@ref)), and infinite groups such as a
[`FreeProduct`](@ref), which appear as the domains of group homomorphisms and
generalised cellular automata.
"""
abstract type AbstractGroup end

"""
    AbstractFiniteGroup

Supertype of the finite groups that cellular automata live on:
[`CyclicGroup`](@ref), [`TorusGroup`](@ref) and [`FiniteGroup`](@ref). A group
provides [`elements`](@ref), [`mul`](@ref), [`identity_element`](@ref),
[`inverse`](@ref) and [`shape`](@ref), the size of the array that holds a
configuration; `length(G)` is its order.
"""
abstract type AbstractFiniteGroup <: AbstractGroup end

"""
    elements(G::AbstractFiniteGroup) -> AbstractVector

The elements of the group `G`, in the order of the cells of a configuration
array. (A method of Catlab's `elements`.)
"""
elements(::AbstractFiniteGroup)

"""
    mul(G, g, h)

The product `g h` in the group `G`.
"""
function mul end

"""
    identity_element(G)

The identity element `e` of the group `G`.
"""
function identity_element end

"""
    inverse(G, g)

The inverse of `g` in the group `G`.
"""
function inverse end

"""
    shape(G::AbstractFiniteGroup) -> Tuple

The size of the array that holds a configuration over `G`: `(n,)` for a cyclic
or abstract finite group, `(n1, …, nd)` for a torus group. (A method of
Catlab's `shape`.)
"""
shape(::AbstractFiniteGroup)

Base.length(G::AbstractFiniteGroup) = length(elements(G))
_cellindex(G::AbstractFiniteGroup, g) = findfirst(==(g), elements(G))
_ismember(G::AbstractFiniteGroup, g) = g in elements(G)

"""
    CyclicGroup(n)

The cyclic group `Z_n`: elements `0, …, n-1` under addition modulo `n`.
Configurations are vectors of length `n`, with the element `g` in position
`g + 1`, as on a one-dimensional `Torus(n)` of CellularAutomataCore.

```jldoctest
julia> G = CyclicGroup(5);

julia> mul(G, 3, 4), inverse(G, 2), identity_element(G)
(2, 3, 0)
```
"""
struct CyclicGroup <: AbstractFiniteGroup
    n::Int
    function CyclicGroup(n::Integer)
        n >= 1 || throw(ArgumentError("a cyclic group needs n ≥ 1, got $n"))
        return new(n)
    end
end
elements(G::CyclicGroup) = 0:(G.n - 1)
mul(G::CyclicGroup, g, h) = mod(g + h, G.n)
identity_element(::CyclicGroup) = 0
inverse(G::CyclicGroup, g) = mod(-g, G.n)
shape(G::CyclicGroup) = (G.n,)
_cellindex(::CyclicGroup, g::Integer) = g + 1
_ismember(G::CyclicGroup, g) = g isa Integer && 0 <= g < G.n
Base.show(io::IO, G::CyclicGroup) = print(io, "CyclicGroup(", G.n, ")")

"""
    TorusGroup(n1, …, nd)

The group `Z_n1 × … × Z_nd` of translations of a `d`-dimensional torus:
elements are tuples `(g1, …, gd)` with `0 ≤ gk < nk`, added componentwise
modulo the sizes. Configurations are arrays of size `(n1, …, nd)`, the element
`g` in position `CartesianIndex(g .+ 1)`, as on a `Torus(n1, …, nd)` of
CellularAutomataCore.

```jldoctest
julia> G = TorusGroup(4, 3);

julia> mul(G, (3, 1), (2, 2)), length(G)
((1, 0), 12)
```
"""
struct TorusGroup{N} <: AbstractFiniteGroup
    dims::NTuple{N,Int}
    function TorusGroup(dims::NTuple{N,Integer}) where {N}
        N >= 1 || throw(ArgumentError("a torus group needs at least one dimension"))
        all(>=(1), dims) ||
            throw(ArgumentError("torus sizes must be at least 1, got $dims"))
        return new{N}(Int.(dims))
    end
end
TorusGroup(dims::Integer...) = TorusGroup(dims)
elements(G::TorusGroup) = vec([Tuple(I) .- 1 for I in CartesianIndices(G.dims)])
mul(G::TorusGroup, g, h) = mod.(g .+ h, G.dims)
identity_element(G::TorusGroup{N}) where {N} = ntuple(_ -> 0, Val(N))
inverse(G::TorusGroup, g) = mod.(.-g, G.dims)
shape(G::TorusGroup) = G.dims
Base.length(G::TorusGroup) = prod(G.dims)
_cellindex(::TorusGroup, g::Tuple) = CartesianIndex(g .+ 1)
function _ismember(G::TorusGroup{N}, g) where {N}
    return g isa NTuple{N,Integer} && all(0 .<= g .< G.dims)
end
Base.show(io::IO, G::TorusGroup) = print(io, "TorusGroup", G.dims)

"""
    FiniteGroup(table; labels=1:n)
    FiniteGroup(elements, op)

An abstract finite group of order `n` given by its Cayley table: elements are
`1:n` and `mul(G, g, h) == table[g, h]`. The table is checked to define a group
(closure, associativity, an identity and inverses). The second form builds the
table from a vector of elements of any type and their multiplication
`op(a, b)`, and keeps the elements as `labels`; [`label`](@ref) gives the one
of an element. Configurations are vectors of length `n`.

```jldoctest
julia> S3 = FiniteGroup([[1, 2, 3], [2, 1, 3], [1, 3, 2], [3, 2, 1], [2, 3, 1], [3, 1, 2]],
                        (a, b) -> a[b]);   # permutations, composed

julia> length(S3), mul(S3, 2, 3) == mul(S3, 3, 2)
(6, false)
```
"""
struct FiniteGroup{L} <: AbstractFiniteGroup
    table::Matrix{Int}
    identity::Int
    inverses::Vector{Int}
    labels::Vector{L}
end
function FiniteGroup(table::AbstractMatrix{<:Integer}; labels=1:size(table, 1))
    n = size(table, 1)
    (n >= 1 && size(table, 2) == n) ||
        throw(ArgumentError("a Cayley table must be square and non-empty, got size $(size(table))"))
    length(labels) == n ||
        throw(ArgumentError("need $n labels, got $(length(labels))"))
    all(x -> 1 <= x <= n, table) ||
        throw(ArgumentError("Cayley table entries must lie in 1:$n"))
    for a in 1:n, b in 1:n, c in 1:n
        table[table[a, b], c] == table[a, table[b, c]] ||
            throw(ArgumentError("the table is not associative: ($a $b) $c ≠ $a ($b $c)"))
    end
    e = findfirst(i -> all(table[i, j] == j && table[j, i] == j for j in 1:n), 1:n)
    e === nothing && throw(ArgumentError("the table has no identity element"))
    inverses = map(1:n) do a
        b = findfirst(b -> table[a, b] == e && table[b, a] == e, 1:n)
        b === nothing && throw(ArgumentError("element $a has no inverse"))
        return b
    end
    return FiniteGroup(Matrix{Int}(table), e, inverses, collect(labels))
end
function FiniteGroup(elems::AbstractVector, op)
    allunique(elems) || throw(ArgumentError("group elements must be distinct"))
    function position(a, b)
        i = findfirst(==(op(a, b)), elems)
        i === nothing &&
            throw(ArgumentError("the elements are not closed under the operation: $(op(a, b))"))
        return i
    end
    return FiniteGroup([position(a, b) for a in elems, b in elems]; labels=elems)
end
elements(G::FiniteGroup) = 1:size(G.table, 1)
mul(G::FiniteGroup, g, h) = G.table[g, h]
identity_element(G::FiniteGroup) = G.identity
inverse(G::FiniteGroup, g) = G.inverses[g]
shape(G::FiniteGroup) = (size(G.table, 1),)
_cellindex(::FiniteGroup, g::Integer) = g
_ismember(G::FiniteGroup, g) = g isa Integer && 1 <= g <= size(G.table, 1)
Base.:(==)(G::FiniteGroup, H::FiniteGroup) = G.table == H.table
Base.hash(G::FiniteGroup, h::UInt) = hash(G.table, hash(:FiniteGroup, h))
function Base.show(io::IO, G::FiniteGroup)
    return print(io, "FiniteGroup of order ", size(G.table, 1))
end

"""
    label(G::FiniteGroup, g)

The element of the original group that `g` stands for, when `G` was built from
elements and an operation (otherwise `g` itself).
"""
label(G::FiniteGroup, g) = G.labels[g]

# Check that `g` is an element of `G`, naming `what` in the message.
function _check_member(G, g, what)
    _ismember(G, g) || throw(ArgumentError("$what: $g is not an element of $G"))
    return g
end
