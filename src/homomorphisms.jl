# Group homomorphisms, and the free product of two groups, the universe of weak products of
# generalised cellular automata. Elements of a free product are reduced words: tuples of
# (factor, element) letters that alternate between the factors and hold no identity element.

"""
    GroupHom(f, H, G; check=true)

The group homomorphism `φ : H → G` given by the function `f`; apply it as
`φ(h)`. When `H` is finite, the homomorphism property `φ(a b) = φ(a) φ(b)` is
checked on every pair of elements unless `check=false`. `φ ∘ ψ` composes
homomorphisms, and `GroupHom(G)` is the identity of `G`.

```jldoctest
julia> φ = GroupHom(g -> g % 3, CyclicGroup(6), CyclicGroup(3));

julia> φ(5)
2
```
"""
struct GroupHom{F,H<:AbstractGroup,G<:AbstractGroup}
    f::F
    dom::H
    codom::G
    function GroupHom(f, H::AbstractGroup, G::AbstractGroup; check::Bool=true)
        if check && H isa AbstractFiniteGroup
            for a in elements(H)
                _check_member(G, f(a), "a group homomorphism's value")
                for b in elements(H)
                    f(mul(H, a, b)) == mul(G, f(a), f(b)) ||
                        throw(ArgumentError("not a homomorphism: φ($a $b) ≠ φ($a) φ($b)"))
                end
            end
        end
        return new{typeof(f),typeof(H),typeof(G)}(f, H, G)
    end
end
GroupHom(G::AbstractGroup) = GroupHom(identity, G, G; check=false)
(φ::GroupHom)(h) = φ.f(h)
function Base.:∘(φ::GroupHom, ψ::GroupHom)
    ψ.codom == φ.dom ||
        throw(GroupMismatchError("composing group homomorphisms", ψ.codom, φ.dom))
    return GroupHom(φ.f ∘ ψ.f, ψ.dom, φ.codom; check=false)
end
function Base.show(io::IO, φ::GroupHom)
    return print(io, "GroupHom(", φ.dom, " → ", φ.codom, ")")
end

# Two homomorphisms are equal if they agree on every element (finite domains only).
function Base.:(==)(φ::GroupHom, ψ::GroupHom)
    (φ.dom == ψ.dom && φ.codom == ψ.codom) || return false
    φ.dom isa AbstractFiniteGroup ||
        throw(ArgumentError("cannot compare homomorphisms on the infinite group $(φ.dom)"))
    return all(h -> φ(h) == ψ(h), elements(φ.dom))
end

# ------------------------------------------------------------------ free products

"""
    FreeProduct(G1, G2)

The free product `G1 ∗ G2` of two finite groups: the infinite group of reduced
words, alternating non-identity elements of `G1` and `G2`, multiplied by
concatenation and cancellation. A word is a tuple of letters `(i, g)`, with
`g` an element of factor `i`; the identity is the empty word `()`.
[`inclusion`](@ref) embeds each factor, [`induced_hom`](@ref) gives the
homomorphism out of the free product determined by one on each factor, and
[`ball`](@ref) lists the words up to a given length.
"""
struct FreeProduct{G1<:AbstractFiniteGroup,G2<:AbstractFiniteGroup} <: AbstractGroup
    left::G1
    right::G2
end
Base.:(==)(F::FreeProduct, E::FreeProduct) = F.left == E.left && F.right == E.right
Base.hash(F::FreeProduct, h::UInt) = hash(F.left, hash(F.right, h))
Base.show(io::IO, F::FreeProduct) = print(io, F.left, " ∗ ", F.right)

_factor(F::FreeProduct, i) = i == 1 ? F.left : F.right
identity_element(::FreeProduct) = ()

# Append a letter to a reduced word, merging with or cancelling the last letter of the same factor.
function _push_letter(F::FreeProduct, w::Tuple, (i, g))
    G = _factor(F, i)
    g == identity_element(G) && return w
    isempty(w) && return ((i, g),)
    j, h = last(w)
    j != i && return (w..., (i, g))
    gh = mul(G, h, g)
    rest = Base.front(w)
    return gh == identity_element(G) ? rest : (rest..., (i, gh))
end

mul(F::FreeProduct, v::Tuple, w::Tuple) = foldl((u, l) -> _push_letter(F, u, l), w; init=v)
function inverse(F::FreeProduct, w::Tuple)
    return Tuple((i, inverse(_factor(F, i), g)) for (i, g) in reverse(w))
end

function _ismember(F::FreeProduct, w)
    w isa Tuple || return false
    for (k, l) in enumerate(w)
        (l isa Tuple && length(l) == 2 && l[1] in (1, 2)) || return false
        i, g = l
        G = _factor(F, i)
        (_ismember(G, g) && g != identity_element(G)) || return false
        k > 1 && w[k - 1][1] == i && return false
    end
    return true
end

"""
    ball(F::FreeProduct, R) -> Vector

The reduced words of the free product `F` of length at most `R`, shortest
first. Configurations over a free product are infinite; a ball is the part of
one that a computation looks at.
"""
function ball(F::FreeProduct, R::Integer)
    R >= 0 || throw(ArgumentError("a ball needs a radius R ≥ 0, got $R"))
    words = Tuple[()]
    frontier = Tuple[()]
    for _ in 1:R
        next = Tuple[]
        for w in frontier, i in (1, 2)
            (!isempty(w) && last(w)[1] == i) && continue
            G = _factor(F, i)
            for g in elements(G)
                g == identity_element(G) || push!(next, (w..., (i, g)))
            end
        end
        append!(words, next)
        frontier = next
    end
    return words
end

"""
    inclusion(F::FreeProduct, i) -> GroupHom

The inclusion `ιᵢ` of the `i`-th factor (`1` or `2`) into the free product.
"""
function inclusion(F::FreeProduct, i::Integer)
    i in (1, 2) ||
        throw(ArgumentError("a free product of two groups has factors 1 and 2, got $i"))
    G = _factor(F, i)
    return GroupHom(g -> _push_letter(F, (), (i, g)), G, F; check=false)
end

"""
    induced_hom(F::FreeProduct, φ1, φ2) -> GroupHom

The unique homomorphism `φ : G1 ∗ G2 → K` that restricts to `φ1 : G1 → K` and
`φ2 : G2 → K` on the factors, the universal property of the free product: a
word is sent to the product of the images of its letters.
"""
function induced_hom(F::FreeProduct, φ1::GroupHom, φ2::GroupHom)
    (φ1.dom == F.left && φ2.dom == F.right) ||
        throw(ArgumentError("induced_hom needs homomorphisms out of $(F.left) and $(F.right)"))
    K = φ1.codom
    φ2.codom == K || throw(GroupMismatchError("induced_hom", K, φ2.codom))
    images = (φ1, φ2)
    f = w -> foldl((k, (i, g)) -> mul(K, k, images[i](g)), w; init=identity_element(K))
    return GroupHom(f, F, K; check=false)
end
