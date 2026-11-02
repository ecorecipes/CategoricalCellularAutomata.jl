# The Curtis–Hedlund–Lyndon theorem in the form of [CastilloRamirez2026, Thm 3.12]: a map of
# configurations is a cellular automaton iff it commutes with the shifts and is uniform. Over a finite
# group every map is uniform (with memory set G), so equivariance is the whole test; the local rule is
# then the map read at the identity cell, and the minimal memory set the cells the rule depends on.

const CONFIGURATION_LIMIT = 2^16

# Every configuration of A over G when there are few enough, otherwise `samples` drawn with `rng`.
function _configurations(G, A::FinAlphabet, rng, samples)
    count = big(length(A))^length(G)
    if count <= CONFIGURATION_LIMIT
        return (Configuration(G, reshape(collect(p), shape(G)))
                for p in Iterators.product(ntuple(_ -> A.values, length(G))...))
    end
    rng === nothing &&
        throw(ArgumentError("there are $count configurations, too many to enumerate; pass `rng` to sample them"))
    return (Configuration(G, rand(rng, A.values, shape(G))) for _ in 1:samples)
end

"""
    is_equivariant(f, G, A; rng=nothing, samples=200) -> Bool

Whether the map `f` of configurations over the group `G` with values in the
alphabet `A` commutes with the shifts: `f(g·x) == g·f(x)` for every element
`g` and configuration `x` (see [`shift`](@ref)). Every configuration is tried
when there are at most 65536 of them; otherwise `samples` random
configurations drawn with the random number generator `rng`, which must then
be given. Over a finite group, an equivariant map is a cellular automaton
([`cellular_automaton`](@ref)).
"""
function is_equivariant(f, G::AbstractFiniteGroup, A::FinAlphabet; rng=nothing,
                        samples::Integer=200)
    for x in _configurations(G, A, rng, samples)
        fx = f(x)
        for g in elements(G)
            f(shift(x, g)) == shift(fx, g) || return false
        end
    end
    return true
end

"""
    cellular_automaton(f, G; dom, codom=dom) -> CellularAutomaton

The cellular automaton that agrees with the map `f` of configurations over the
finite group `G`, if `f` is one: its memory set is the whole of `G` and its
local rule reads `f` at the identity cell. By the Curtis–Hedlund–Lyndon theorem
[CastilloRamirez2026](@cite) the result equals `f` exactly when `f` commutes
with the shifts ([`is_equivariant`](@ref)). [`minimal_neighbourhood`](@ref)
then reduces the memory set to the cells the rule depends on.
"""
function cellular_automaton(f, G::AbstractFiniteGroup; dom::FinAlphabet,
                            codom::FinAlphabet=dom)
    e = identity_element(G)
    μ = p -> f(Configuration(G, reshape(collect(p), shape(G))))[e]
    return CellularAutomaton(G, collect(elements(G)), μ; dom, codom)
end

"""
    minimal_neighbourhood(τ) -> CellularAutomaton

The same cellular automaton with the smallest memory set: the elements of the
memory set on which the local rule actually depends, found by trying every
pattern. The result equals `τ` (`==`). Raises `ArgumentError` when there are
more than about four million patterns to try.
"""
function minimal_neighbourhood(τ::CellularAutomaton)
    A, S = alphabet(τ.dom), τ.memory
    n = length(S)
    depends = falses(n)
    for p in _patterns(A, n, "minimal_neighbourhood")
        v = τ.rule(p)
        for i in 1:n
            depends[i] && continue
            depends[i] = any(a -> a != p[i] && τ.rule(Base.setindex(p, a, i)) != v,
                             A.values)
        end
        all(depends) && break
    end
    keep = findall(depends)
    filler = first(A.values)
    slot = zeros(Int, n)
    slot[keep] .= eachindex(keep)
    μ = τ.rule
    rule = y -> μ(ntuple(i -> slot[i] == 0 ? filler : y[slot[i]], n))
    return CellularAutomaton(τ.group, S[keep], rule, τ.dom, τ.codom)
end
