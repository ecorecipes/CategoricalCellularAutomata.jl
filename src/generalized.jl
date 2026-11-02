# Generalised cellular automata [CastilloRamirez2025, CastilloRamirez2026, §4]: for a group
# homomorphism φ : H → G, a φ-cellular automaton T : A^G → B^H is T(x)(h) = μ((x(s φ(h)))_{s ∈ S})
# for a finite S ⊂ G. Every one factors as the pullback φ* after an ordinary CA τ over G (Lemma 4.5),
# and that is how it is stored: the homomorphism, and τ.

_factors(A::FinAlphabet) = FinAlphabet[A]
_factors(X::FullShift) = X.factors

"""
    GeneralizedCA(φ, S, μ; dom, codom=dom)
    GeneralizedCA(φ, τ)
    GeneralizedCA(τ)

A generalised cellular automaton between groups [CastilloRamirez2025](@cite):
for a group homomorphism `φ : H → G` ([`GroupHom`](@ref)), the map
`T : A^G → B^H` with

    T(x)(h) = μ((x(s φ(h)))_{s ∈ S})

for a finite memory set `S ⊂ G` and local rule `μ`. It is the pullback `φ*`
after the ordinary cellular automaton `τ` over `G` with the same memory set and
rule, and the second form builds it from `φ` and `τ`; the third treats an
ordinary cellular automaton as one over the identity homomorphism.
[`factorize`](@ref) returns `(φ, τ)`. Apply it as `T(x)` when `H` is finite, or
`T(x, h)` at one element of any `H`. Generalised automata compose (`compose`,
`∘`), with homomorphism `φ ∘ ψ`, and are equal (`==`) when equal as maps.
"""
struct GeneralizedCA{Φ<:GroupHom,T<:CellularAutomaton,C<:FullShift}
    hom::Φ
    ca::T
    codom::C
end
function GeneralizedCA(φ::GroupHom, τ::CellularAutomaton)
    τ.group == φ.codom ||
        throw(GroupMismatchError("a generalised cellular automaton", φ.codom, τ.group))
    return GeneralizedCA(φ, τ, FullShift(τ.codom.factors, φ.dom))
end
GeneralizedCA(τ::CellularAutomaton) = GeneralizedCA(GroupHom(τ.group), τ)
function GeneralizedCA(φ::GroupHom, S::AbstractVector, μ; dom::Union{FinAlphabet,FullShift},
                       codom::Union{FinAlphabet,FullShift}=dom)
    G = φ.codom
    τ = CellularAutomaton(G, S, μ; dom=FullShift(_factors(dom), G),
                          codom=FullShift(_factors(codom), G))
    return GeneralizedCA(φ, τ)
end

dom(T::GeneralizedCA) = T.ca.dom
codom(T::GeneralizedCA) = T.codom
memory_set(T::GeneralizedCA) = T.ca.memory
local_map(T::GeneralizedCA) = T.ca.rule

"""
    factorize(T::GeneralizedCA) -> (φ, τ)

The factorisation of a generalised cellular automaton `T : A^G → B^H` as the
pullback along `φ : H → G` after the ordinary cellular automaton
`τ : A^G → B^G`, so that `T == compose(τ, pullback(φ, codom(τ)))`
[CastilloRamirez2026](@cite). (A method of Catlab's `factorize`.)
"""
factorize(T::GeneralizedCA) = (T.hom, T.ca)

function (T::GeneralizedCA)(x::Configuration, h)
    G = T.ca.group
    x.group == G ||
        throw(GroupMismatchError("applying a generalised cellular automaton", G,
                                 x.group))
    g = T.hom(h)
    return T.ca.rule(Tuple(x[mul(G, s, g)] for s in T.ca.memory))
end
function (T::GeneralizedCA)(x::Configuration)
    H = T.hom.dom
    H isa AbstractFiniteGroup ||
        throw(ArgumentError("$H is infinite: evaluate at one element with T(x, h)"))
    return Configuration(h -> T(x, h), H)
end

function Base.show(io::IO, T::GeneralizedCA)
    print(io, "GeneralizedCA over ", T.hom, " with memory set ", T.ca.memory, ": ")
    _show_shift(io, dom(T))
    print(io, " → ")
    return _show_shift(io, T.codom)
end

# ------------------------------------------------------------------ pullback and pushforward

"""
    pullback(φ, x::Configuration)
    pullback(φ, A)

The pullback `φ* x = x ∘ φ` of a configuration over `G` along a homomorphism
`φ : H → G`: a configuration over `H`. The second form is the pullback as a
generalised cellular automaton `A^G → A^H` (memory set `{e}`) for an alphabet
or full shift `A`. (A method of Catlab's `pullback`.)
"""
function pullback(φ::GroupHom, x::Configuration)
    x.group == φ.codom || throw(GroupMismatchError("pullback", φ.codom, x.group))
    return Configuration(h -> x[φ(h)], φ.dom)
end
function pullback(φ::GroupHom, A::Union{FinAlphabet,FullShift})
    return GeneralizedCA(φ, _id(FullShift(_factors(A), φ.codom)))
end

"""
    pushforward(f, G; dom, codom)

The cellular automaton over `G` that applies the map of alphabets
`f : dom → codom` to every cell, with memory set `{e}`: the pushforward `f_*`,
a functor from alphabets to cellular automata over `G`. It commutes with
pullbacks along homomorphisms [CastilloRamirez2026](@cite).
"""
function pushforward(f, G::AbstractFiniteGroup; dom::FinAlphabet, codom::FinAlphabet)
    return CellularAutomaton(G, [identity_element(G)], p -> f(only(p)); dom, codom)
end

# ------------------------------------------------------------------ composition and equality

function _gcompose(T1::GeneralizedCA, T2::GeneralizedCA)
    T1.codom == dom(T2) ||
        throw(DomainMismatchError("composing generalised cellular automata", T1.codom,
                                  dom(T2)))
    φ, ψ = T1.hom, T2.hom
    G = T1.ca.group
    S, T = T1.ca.memory, T2.ca.memory
    U = unique(mul(G, s, φ(t)) for t in T for s in S)
    idx = [[findfirst(==(mul(G, s, φ(t))), U) for s in S] for t in T]
    μ, ν = T1.ca.rule, T2.ca.rule
    rule = y -> ν(Tuple(μ(Tuple(y[i] for i in row)) for row in idx))
    τ = CellularAutomaton(G, U, rule, T1.ca.dom, FullShift(T2.codom.factors, G))
    return GeneralizedCA(φ ∘ ψ, τ, T2.codom)
end

compose(T1::GeneralizedCA, T2::GeneralizedCA) = _gcompose(T1, T2)
compose(T1::GeneralizedCA, τ::CellularAutomaton) = _gcompose(T1, GeneralizedCA(τ))
compose(τ::CellularAutomaton, T2::GeneralizedCA) = _gcompose(GeneralizedCA(τ), T2)
Base.:∘(T2::Union{GeneralizedCA,CellularAutomaton}, T1::GeneralizedCA) = compose(T1, T2)
Base.:∘(T2::GeneralizedCA, τ::CellularAutomaton) = compose(τ, T2)

"""
    T1 == T2

Whether two generalised cellular automata are equal as maps. For each element
`h` of the (finite) codomain group, their local rules, read at `φ1(h)` and
`φ2(h)`, are compared on every pattern over the union of the cells they read.
Two automata over different homomorphisms can be equal.
"""
function Base.:(==)(T1::GeneralizedCA, T2::GeneralizedCA)
    (dom(T1) == dom(T2) && codom(T1) == codom(T2)) || return false
    H = T1.hom.dom
    H isa AbstractFiniteGroup ||
        throw(ArgumentError("cannot compare generalised cellular automata into the infinite group $H"))
    G = T1.ca.group
    A = alphabet(dom(T1))
    seen = Set{Any}()
    for h in elements(H)
        a, b = T1.hom(h), T2.hom(h)
        (a, b) in seen && continue
        push!(seen, (a, b))
        u1 = [mul(G, s, a) for s in T1.ca.memory]
        u2 = [mul(G, s, b) for s in T2.ca.memory]
        U = union(u1, u2)
        i1, i2 = _positions(u1, U), _positions(u2, U)
        for p in _patterns(A, length(U), "comparing generalised cellular automata")
            T1.ca.rule(Tuple(p[i] for i in i1)) == T2.ca.rule(Tuple(p[i] for i in i2)) ||
                return false
        end
    end
    return true
end
Base.:(==)(T::GeneralizedCA, τ::CellularAutomaton) = T == GeneralizedCA(τ)
Base.:(==)(τ::CellularAutomaton, T::GeneralizedCA) = GeneralizedCA(τ) == T

# ------------------------------------------------------------------ weak products

"""
    weak_product(X1, X2) -> FullShift

The weak product of full shifts `A1^G1` and `A2^G2` in the category of
generalised cellular automata: the full shift `(A1 × A2)^(G1 ∗ G2)` over the
[`FreeProduct`](@ref) of the groups [CastilloRamirez2025](@cite). See
[`weak_projections`](@ref) and [`weak_pair`](@ref).
"""
function weak_product(X1::FullShift, X2::FullShift)
    return FullShift(vcat(X1.factors, X2.factors), FreeProduct(X1.group, X2.group))
end

"""
    weak_projections(X1, X2) -> (π1, π2)

The projections of the [`weak_product`](@ref) onto its factors: `πᵢ` is the
generalised cellular automaton over the inclusion `ιᵢ : Gᵢ → G1 ∗ G2` that
reads the `i`-th component at the identity.
"""
function weak_projections(X1::FullShift, X2::FullShift)
    P = weak_product(X1, X2)
    F = P.group
    k = length(X1.factors)
    ranges = (1:k, (k + 1):length(P.factors))
    return ntuple(2) do i
        X = (X1, X2)[i]
        r = ranges[i]
        τ = CellularAutomaton(F, Tuple[()], p -> _fromtuple(only(p)[r]), P,
                              FullShift(X.factors, F))
        return GeneralizedCA(inclusion(F, i), τ, X)
    end
end

"""
    weak_pair(T1, T2) -> GeneralizedCA

The pairing of generalised cellular automata `T1 : X → A1^G1` (over
`φ1 : G1 → K`) and `T2 : X → A2^G2` (over `φ2 : G2 → K`) with a common domain
`X = B^K`: the generalised cellular automaton into the [`weak_product`](@ref)
over the homomorphism [`induced_hom`](@ref)`(G1 ∗ G2, φ1, φ2)`, whose local
rule pairs those of `T1` and `T2`. Composed with the [`weak_projections`](@ref)
it gives back `T1` and `T2`. It is not the only automaton that does: the
product is weak because an automaton can be a `φ`-automaton for several `φ`
[CastilloRamirez2025](@cite).
"""
function weak_pair(T1::GeneralizedCA, T2::GeneralizedCA)
    dom(T1) == dom(T2) || throw(DomainMismatchError("weak_pair", dom(T1), dom(T2)))
    F = FreeProduct(T1.hom.dom, T2.hom.dom)
    φ = induced_hom(F, T1.hom, T2.hom)
    return GeneralizedCA(φ, _pair(T1.ca, T2.ca), weak_product(T1.codom, T2.codom))
end
