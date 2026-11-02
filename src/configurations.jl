# Alphabets, configurations and full shifts. A configuration over G with values in A is a function
# G -> A, stored as an array of the group's shape; the full shift A^G is the object of CA(G).

"""
    FinAlphabet(values)

A finite alphabet: the set of states a cell can take, as a vector of distinct
values (`FinAlphabet(0:1)`, `FinAlphabet([:S, :I, :R])`).
"""
struct FinAlphabet{T}
    values::Vector{T}
    function FinAlphabet(values::AbstractVector{T}) where {T}
        allunique(values) || throw(ArgumentError("alphabet values must be distinct"))
        return new{T}(collect(values))
    end
end
FinAlphabet(values) = FinAlphabet(collect(values))
Base.length(A::FinAlphabet) = length(A.values)
Base.iterate(A::FinAlphabet, i...) = iterate(A.values, i...)
Base.eltype(::Type{FinAlphabet{T}}) where {T} = T
Base.in(a, A::FinAlphabet) = a in A.values
Base.:(==)(A::FinAlphabet, B::FinAlphabet) = A.values == B.values
Base.hash(A::FinAlphabet, h::UInt) = hash(A.values, hash(:FinAlphabet, h))
Base.show(io::IO, A::FinAlphabet) = print(io, "FinAlphabet(", A.values, ")")

"""
    Configuration(G, data)
    Configuration(f, G)

A configuration `x : G → A`, the state of a cellular automaton over the group
`G`, held in an array `data` of size [`shape`](@ref)`(G)`, or built from a
function `f(g)` of the elements. `x[g]` is the value at the element `g`, and
`parent(x)` the array, which for a torus group is a CellularAutomataCore state.
"""
struct Configuration{G<:AbstractFiniteGroup,D<:AbstractArray}
    group::G
    data::D
    function Configuration(G::AbstractFiniteGroup, data::AbstractArray)
        size(data) == shape(G) ||
            throw(ArgumentError("a configuration over $G needs an array of size $(shape(G)), got $(size(data))"))
        return new{typeof(G),typeof(data)}(G, data)
    end
end
function Configuration(f, G::AbstractFiniteGroup)
    data = similar(Array{Any}, shape(G))
    for g in elements(G)
        data[_cellindex(G, g)] = f(g)
    end
    return Configuration(G, [v for v in data])  # narrow the element type
end
Base.getindex(x::Configuration, g) = x.data[_cellindex(x.group, g)]
Base.parent(x::Configuration) = x.data
Base.:(==)(x::Configuration, y::Configuration) = x.group == y.group && x.data == y.data
Base.hash(x::Configuration, h::UInt) = hash(x.data, hash(x.group, h))
function Base.show(io::IO, x::Configuration)
    return print(io, "Configuration over ", x.group, ": ", x.data)
end

"""
    group(x)

The group of a configuration, full shift or cellular automaton.
"""
group(x::Configuration) = x.group

"""
    shift(x, g)

The configuration `g·x`, with `(g·x)(h) = x(h g)`: the left action of `G` on
configurations. On a torus group it is the translation that brings the value at
`g` to the identity.
"""
function shift(x::Configuration, g)
    G = x.group
    _check_member(G, g, "shift")
    return Configuration(h -> x[mul(G, h, g)], G)
end

"""
    restrict(x::Configuration, S) -> Tuple

The restriction `x|_S` of a configuration to a finite subset `S` of the group,
as the tuple of its values at the elements of `S`, in order. (A method of
Catlab's `restrict`.)
"""
restrict(x::Configuration, S) = Tuple(x[s] for s in S)

"""
    FullShift(A, G)

The full shift `A^G`: every configuration over the group `G` with values in the
alphabet `A`. The objects of the category of cellular automata over `G`.

The product of full shifts (`otimes`) is strictly associative: `(A ⊗ B) ⊗ C`
and `A ⊗ (B ⊗ C)` are one full shift, whose configurations hold flat tuples
`(a, b, c)`. The unit object `munit()` holds the single value `()` and belongs
to no particular group: it is a unit for `otimes` with any full shift.
"""
struct FullShift{G}
    factors::Vector{FinAlphabet}
    group::G
end
FullShift(A::FinAlphabet, G) = FullShift(FinAlphabet[A], G)
Base.:(==)(X::FullShift, Y::FullShift) = X.factors == Y.factors && X.group == Y.group
Base.hash(X::FullShift, h::UInt) = hash(X.factors, hash(X.group, h))
group(X::FullShift) = X.group

"""
    alphabet(X::FullShift) -> FinAlphabet

The alphabet `A` of the full shift `A^G`; for a product of full shifts, the
alphabet of flat tuples of the factors' values.
"""
function alphabet(X::FullShift)
    length(X.factors) == 1 && return only(X.factors)
    return FinAlphabet(vec(collect(Iterators.product((A.values for A in X.factors)...))))
end

_isunit(X::FullShift) = isempty(X.factors)
_nfactors(X::FullShift) = length(X.factors)
_show_factors(io, X::FullShift) = join(io, (A.values for A in X.factors), " ⊗ ")
function Base.show(io::IO, X::FullShift)
    _isunit(X) && return print(io, "munit()")
    print(io, "FullShift(")
    length(X.factors) == 1 ? print(io, only(X.factors)) : _show_factors(io, X)
    return print(io, ", ", X.group, ")")
end
