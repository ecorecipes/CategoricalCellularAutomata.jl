# Cellular automata over a group G: tau(x)(g) = mu((x(s g))_{s in S}) for a finite memory set S and a
# local rule mu. A CA is a morphism A^G -> B^G of the category CA(G).

"""
    CellularAutomaton(G, S, μ; dom, codom=dom)

The cellular automaton over the group `G` with memory set `S` (a vector of
distinct elements of `G`) and local rule `μ`, from configurations with values in
the alphabet `dom` to configurations with values in `codom` (alphabets, or
[`FullShift`](@ref)s such as products) [CastilloRamirez2025](@cite). It maps a configuration `x` to the configuration

    τ(x)(g) = μ((x(s g))_{s ∈ S}),

that is, `μ` is called with the tuple of the values of `x` at `s g` for the
elements `s` of `S`, in order. On a torus group `s g = s + g`, so `S` lists the
offsets of the neighbourhood, the identity being the cell itself. Apply it to a
[`Configuration`](@ref) as `τ(x)`.

Cellular automata over `G` form a cartesian category whose objects are the
[`FullShift`](@ref)s `A^G`: they compose (`compose(τ, σ)` is `σ ∘ τ`), pair
(`pair`), and have identities, projections, copies and deletions, the Catlab
operations of `ThCartesianCategory`. Two automata are equal (`==`) when
they are equal as maps, which holds exactly when their local rules agree on
every pattern over the union of their memory sets.

```jldoctest
julia> G = CyclicGroup(8); B = FinAlphabet(0:1);

julia> rule90 = CellularAutomaton(G, [7, 1], p -> xor(p...); dom=B);  # left and right

julia> parent(rule90(Configuration(G, [0, 0, 0, 1, 0, 0, 0, 0])))
8-element Vector{Int64}:
 0
 0
 1
 0
 1
 0
 0
 0
```
"""
struct CellularAutomaton{G,E,F,D<:FullShift,C<:FullShift}
    group::G
    memory::Vector{E}
    rule::F
    dom::D
    codom::C
end
function CellularAutomaton(G::AbstractFiniteGroup, S::AbstractVector, μ;
                           dom::Union{FinAlphabet,FullShift},
                           codom::Union{FinAlphabet,FullShift}=dom)
    foreach(s -> _check_member(G, s, "memory set"), S)
    allunique(S) || throw(ArgumentError("the memory set has repeated elements: $S"))
    return CellularAutomaton(G, collect(S), μ, _shift_over(dom, G), _shift_over(codom, G))
end
_shift_over(A::FinAlphabet, G) = FullShift(A, G)
function _shift_over(X::FullShift, G)
    (_isunit(X) || X.group == G) ||
        throw(GroupMismatchError("a cellular automaton's domain or codomain", G, X.group))
    return X
end

group(τ::CellularAutomaton) = τ.group

"""
    memory_set(τ) -> Vector

The memory set `S` of a cellular automaton, in the order its local rule reads
it.
"""
memory_set(τ::CellularAutomaton) = τ.memory

"""
    local_map(τ)

The local rule `μ : A^S → B` of a cellular automaton, a function of the tuple
of values on its memory set.
"""
local_map(τ::CellularAutomaton) = τ.rule

function (τ::CellularAutomaton)(x::Configuration)
    G = τ.group
    x.group == G || throw(GroupMismatchError("applying a cellular automaton", G, x.group))
    S = τ.memory
    return Configuration(g -> τ.rule(Tuple(x[mul(G, s, g)] for s in S)), G)
end

"""
    τ^n

The `n`-fold composite of a cellular automaton with itself (`n ≥ 1`); its
domain and codomain must agree.
"""
function Base.:^(τ::CellularAutomaton, n::Integer)
    n >= 1 || throw(ArgumentError("a power of a cellular automaton needs n ≥ 1, got $n"))
    τ.dom == τ.codom ||
        throw(DomainMismatchError("a power of a cellular automaton", τ.dom, τ.codom))
    return foldl((a, _) -> _compose(a, τ), 2:n; init=τ)
end

function Base.show(io::IO, τ::CellularAutomaton)
    print(io, "CellularAutomaton over ", τ.group, " with memory set ", τ.memory, ": ")
    _show_shift(io, τ.dom)
    print(io, " → ")
    return _show_shift(io, τ.codom)
end
function _show_shift(io, X::FullShift)
    _isunit(X) && return print(io, "munit()")
    return _show_factors(io, X)
end

# ------------------------------------------------------------------ equality through the identity cell

const PATTERN_LIMIT = 2^22

# Every pattern over `n` cells of an alphabet, as tuples; raises if there are too many to enumerate.
function _patterns(A::FinAlphabet, n::Integer, what)
    count = big(length(A))^n
    count <= PATTERN_LIMIT ||
        throw(ArgumentError("$what would enumerate $count patterns (|A|^|S| = $(length(A))^$n), more than $PATTERN_LIMIT"))
    return Iterators.product(ntuple(_ -> A.values, n)...)
end

# Positions of the elements of `S` in `U`.
_positions(S, U) = [findfirst(==(s), U) for s in S]

"""
    σ == τ

Whether two cellular automata are equal as maps of configurations. They are
equal when their local rules agree on every pattern over the union of their
memory sets, by evaluating both at the identity element, which suffices because
a cellular automaton commutes with the shifts [CastilloRamirez2026](@cite). The
check enumerates `|A|^|S ∪ T|` patterns and raises `ArgumentError` when there
are more than about four million.
"""
function Base.:(==)(σ::CellularAutomaton, τ::CellularAutomaton)
    (σ.group == τ.group && σ.dom == τ.dom && σ.codom == τ.codom) || return false
    U = union(σ.memory, τ.memory)
    iσ, iτ = _positions(σ.memory, U), _positions(τ.memory, U)
    for p in _patterns(alphabet(σ.dom), length(U), "comparing cellular automata")
        σ.rule(Tuple(p[i] for i in iσ)) == τ.rule(Tuple(p[i] for i in iτ)) || return false
    end
    return true
end
