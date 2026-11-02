# CA(G) as a cartesian category: composition (memory set {s t}), pairing (memory set S ∪ T), identities,
# projections, copies, deletions and braidings (memory set {e}). The Catlab instance below binds
# ThCartesianCategory's generic names to these operations. Products are strict, as in Catlab's free
# cartesian category: a full shift is a flat list of factor alphabets and its values flat tuples, so
# (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z), and the unit (no factors, no group) satisfies X ⊗ I = I ⊗ X = X.

function _same_group(what, X, Y)
    (G, H) = (group(X), group(Y))
    (G === nothing || H === nothing || G == H) || throw(GroupMismatchError(what, G, H))
    return G === nothing ? H : G
end

function _compose(τ::CellularAutomaton, σ::CellularAutomaton)
    G = _same_group("composing cellular automata", τ, σ)
    τ.codom == σ.dom ||
        throw(DomainMismatchError("composing cellular automata", τ.codom, σ.dom))
    S, T = τ.memory, σ.memory
    U = unique(mul(G, s, t) for t in T for s in S)
    idx = [[findfirst(==(mul(G, s, t)), U) for s in S] for t in T]
    μ, ν = τ.rule, σ.rule
    rule = y -> ν(Tuple(μ(Tuple(y[i] for i in row)) for row in idx))
    return CellularAutomaton(G, U, rule, τ.dom, σ.codom)
end

Base.:∘(σ::CellularAutomaton, τ::CellularAutomaton) = _compose(τ, σ)

function _shift_product(X::FullShift, Y::FullShift)
    _isunit(Y) && return X
    _isunit(X) && return Y
    G = _same_group("the product of full shifts", X, Y)
    return FullShift(vcat(X.factors, Y.factors), G)
end

_unit_shift() = FullShift(FinAlphabet[], nothing)

# A value of a full shift with `k` factors as a tuple of its factors' values, and back.
_astuple(v, k) = k == 1 ? (v,) : v
_fromtuple(t) = length(t) == 1 ? only(t) : t

function _single(X::FullShift, codom::FullShift, rule)
    G = X.group
    G === nothing && throw(ArgumentError("the unit object belongs to no group"))
    return CellularAutomaton(G, [identity_element(G)], rule, X, codom)
end

_id(X::FullShift) = _single(X, X, only)

function _pair(σ::CellularAutomaton, τ::CellularAutomaton)
    G = _same_group("pairing cellular automata", σ, τ)
    σ.dom == τ.dom || throw(DomainMismatchError("pairing cellular automata", σ.dom, τ.dom))
    _isunit(τ.codom) && return σ
    _isunit(σ.codom) && return τ
    U = union(σ.memory, τ.memory)
    iσ, iτ = _positions(σ.memory, U), _positions(τ.memory, U)
    μ, ν = σ.rule, τ.rule
    k, m = _nfactors(σ.codom), _nfactors(τ.codom)
    rule = y -> (_astuple(μ(Tuple(y[i] for i in iσ)), k)...,
                 _astuple(ν(Tuple(y[i] for i in iτ)), m)...)
    return CellularAutomaton(G, U, rule, σ.dom, _shift_product(σ.codom, τ.codom))
end

function _proj1(X::FullShift, Y::FullShift)
    _isunit(Y) && return _id(X)
    k = _nfactors(X)
    return _single(_shift_product(X, Y), X, p -> _fromtuple(only(p)[1:k]))
end
function _proj2(X::FullShift, Y::FullShift)
    _isunit(X) && return _id(Y)
    k = _nfactors(X)
    return _single(_shift_product(X, Y), Y, p -> _fromtuple(only(p)[(k + 1):end]))
end
function _braid(X::FullShift, Y::FullShift)
    (_isunit(X) || _isunit(Y)) && return _id(_shift_product(X, Y))
    k = _nfactors(X)
    return _single(_shift_product(X, Y), _shift_product(Y, X),
                   p -> (only(p)[(k + 1):end]..., only(p)[1:k]...))
end
function _mcopy(X::FullShift)
    k = _nfactors(X)
    return _single(X, _shift_product(X, X),
                   p -> (_astuple(only(p), k)..., _astuple(only(p), k)...))
end

function _otimes(σ::CellularAutomaton, τ::CellularAutomaton)
    X, Y = σ.dom, τ.dom
    return _pair(_compose(_proj1(X, Y), σ), _compose(_proj2(X, Y), τ))
end

@instance ThCartesianCategory{FullShift,CellularAutomaton} begin
    dom(τ::CellularAutomaton) = τ.dom
    codom(τ::CellularAutomaton) = τ.codom
    id(X::FullShift) = _id(X)
    compose(τ::CellularAutomaton, σ::CellularAutomaton) = _compose(τ, σ)
    otimes(X::FullShift, Y::FullShift) = _shift_product(X, Y)
    otimes(σ::CellularAutomaton, τ::CellularAutomaton) = _otimes(σ, τ)
    munit() = _unit_shift()
    braid(X::FullShift, Y::FullShift) = _braid(X, Y)
    mcopy(X::FullShift) = _mcopy(X)
    delete(X::FullShift) = _single(X, _unit_shift(), p -> ())
    pair(σ::CellularAutomaton, τ::CellularAutomaton) = _pair(σ, τ)
    proj1(X::FullShift, Y::FullShift) = _proj1(X, Y)
    proj2(X::FullShift, Y::FullShift) = _proj2(X, Y)
end

# The free cartesian category builds n-ary composites and products, which GATlab's functor calls.
function compose(τ::CellularAutomaton, σ::CellularAutomaton, ρ::CellularAutomaton...)
    return foldl(_compose, (τ, σ, ρ...))
end
function otimes(σ::CellularAutomaton, τ::CellularAutomaton, ρ::CellularAutomaton...)
    return foldl(_otimes, (σ, τ, ρ...))
end
otimes(X::FullShift, Y::FullShift, Z::FullShift...) = foldl(_shift_product, (X, Y, Z...))

"""
    realize(diagram, presentation; generators...)

Evaluate a Catlab wiring diagram, such as one built with `@program`, in the
category of cellular automata: each generator of the `presentation` named in
`generators` is given a [`FullShift`](@ref) (an object) or a
[`CellularAutomaton`](@ref) (a morphism), and the diagram's copies, deletions,
products and composites become those of cellular automata. Returns one
cellular automaton.

```julia
pres = @present P(FreeCartesianCategory) begin
    X::Ob
    step::Hom(X, X)
end
d = @program pres (x::X) begin
    y = step(x)
    return (y, step(y))
end
realize(d, pres; X=FullShift(B, G), step=rule90)  # x ↦ (τ(x), τ(τ(x)))
```
"""
function realize(diagram, presentation; generators...)
    gens = Dict(generator(presentation, k) => v for (k, v) in generators)
    expr = to_hom_expr(FreeCartesianCategory, diagram)
    return functor((FullShift, CellularAutomaton), expr; generators=gens)
end
