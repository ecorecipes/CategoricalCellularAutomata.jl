# Linear cellular automata over the field GF(p) on an abelian torus group: τ(x)(g) = Σ_s a_s x(s g) mod p,
# the cellular automata of the category of vector spaces over GF(p). One is a finitely supported
# coefficient function, an element of the group algebra GF(p)[G]; composition is the product there
# (a convolution), so composites and powers cost nothing like the generic composition of local rules.

const _AbelianGroup = Union{CyclicGroup,TorusGroup}

"""
    LinearCA(G, coefficients; p)

The linear cellular automaton over the prime field `GF(p)` on a cyclic or torus
group `G` with the given coefficients `s => a_s`:

    τ(x)(g) = Σ_s a_s x(s g)  (mod p),

on configurations with values in `0:p-1`. Linear automata compose and take
powers through their coefficients, as elements of the group algebra
`GF(p)[G]` (`compose`, `∘`, `^`), which is much faster than composing local
rules, and `inv` inverts one when it is a bijection. `CellularAutomaton(L)`
gives the same automaton as a general one.

```jldoctest
julia> rule90 = LinearCA(CyclicGroup(16), [15 => 1, 1 => 1]; p=2);

julia> rule90^4 == LinearCA(CyclicGroup(16), [12 => 1, 4 => 1]; p=2)
true
```
"""
struct LinearCA{G<:_AbelianGroup,E}
    group::G
    coeffs::Dict{E,Int}
    p::Int
    function LinearCA(G::_AbelianGroup, coefficients; p::Integer)
        (p >= 2 && all(d -> p % d != 0, 2:isqrt(p))) ||
            throw(ArgumentError("p must be a prime, got $p"))
        E = typeof(identity_element(G))
        c = Dict{E,Int}()
        for (s, a) in coefficients
            _check_member(G, s, "a linear cellular automaton's coefficients")
            c[s] = mod(get(c, s, 0) + a, p)
        end
        filter!(kv -> kv.second != 0, c)
        return new{typeof(G),E}(G, c, Int(p))
    end
end

"""
    coefficients(L::LinearCA) -> Dict

The non-zero coefficients `s => a_s` of a linear cellular automaton.
"""
coefficients(L::LinearCA) = L.coeffs

group(L::LinearCA) = L.group
_alphabet(L::LinearCA) = FinAlphabet(0:(L.p - 1))
function Base.:(==)(L::LinearCA, M::LinearCA)
    return L.group == M.group && L.p == M.p && L.coeffs == M.coeffs
end
function Base.show(io::IO, L::LinearCA)
    terms = sort!(collect(L.coeffs); by=first)
    return print(io, "LinearCA over ", L.group, " mod ", L.p, ": ",
                 join(("$a·x(s=$s)" for (s, a) in terms), " + "))
end

function (L::LinearCA)(x::Configuration)
    G = L.group
    x.group == G ||
        throw(GroupMismatchError("applying a linear cellular automaton", G, x.group))
    return Configuration(g -> mod(sum(a * x[mul(G, s, g)] for (s, a) in L.coeffs; init=0),
                                  L.p),
                         G)
end

function CellularAutomaton(L::LinearCA)
    S = sort!(collect(keys(L.coeffs)))
    a = [L.coeffs[s] for s in S]
    p = L.p
    return CellularAutomaton(L.group, S, y -> mod(sum(a .* collect(y); init=0), p);
                             dom=_alphabet(L))
end

function _same_field(L::LinearCA, M::LinearCA)
    L.group == M.group ||
        throw(GroupMismatchError("composing linear cellular automata", L.group, M.group))
    L.p == M.p || throw(ArgumentError("linear automata over GF($(L.p)) and GF($(M.p))"))
    return nothing
end

function compose(L::LinearCA, M::LinearCA)
    _same_field(L, M)
    G = L.group
    terms = (mul(G, s, t) => a * b for (s, a) in L.coeffs for (t, b) in M.coeffs)
    return LinearCA(G, terms; p=L.p)
end
Base.:∘(M::LinearCA, L::LinearCA) = compose(L, M)

_linear_identity(L::LinearCA) = LinearCA(L.group, [identity_element(L.group) => 1]; p=L.p)

function Base.:^(L::LinearCA, n::Integer)
    n >= 0 || throw(ArgumentError("a negative power needs inv(L)^n"))
    result, base = _linear_identity(L), L
    while n > 0
        isodd(n) && (result = compose(result, base))
        base = compose(base, base)
        n >>= 1
    end
    return result
end

# The matrix of L on GF(p)^|G|, rows and columns in the order of elements(G).
function _matrix(L::LinearCA)
    G = L.group
    E = elements(G)
    index = Dict(g => i for (i, g) in enumerate(E))
    M = zeros(Int, length(E), length(E))
    for (i, g) in enumerate(E), (s, a) in L.coeffs
        j = index[mul(G, s, g)]
        M[i, j] = mod(M[i, j] + a, L.p)
    end
    return M
end

_identity_matrix(n) = [i == j ? 1 : 0 for i in 1:n, j in 1:n]

# Gauss–Jordan elimination over GF(p); `nothing` if M is singular.
function _inverse_mod(M::Matrix{Int}, p::Int)
    n = size(M, 1)
    A = hcat(mod.(M, p), _identity_matrix(n))
    for c in 1:n
        r = findfirst(i -> A[i, c] != 0, c:n)
        r === nothing && return nothing
        r += c - 1
        A[[c, r], :] = A[[r, c], :]
        A[c, :] = mod.(A[c, :] .* invmod(A[c, c], p), p)
        for i in 1:n
            i != c && A[i, c] != 0 && (A[i, :] = mod.(A[i, :] .- A[i, c] .* A[c, :], p))
        end
    end
    return A[:, (n + 1):end]
end

"""
    isinvertible(L::LinearCA) -> Bool

Whether the linear cellular automaton is a bijection of configurations, so that
running it backwards is again a linear cellular automaton.
"""
isinvertible(L::LinearCA) = _inverse_mod(_matrix(L), L.p) !== nothing

"""
    inv(L::LinearCA) -> LinearCA

The inverse of an invertible linear cellular automaton, a linear cellular
automaton too; raises `ArgumentError` if `L` is not a bijection.
"""
function Base.inv(L::LinearCA)
    Minv = _inverse_mod(_matrix(L), L.p)
    Minv === nothing && throw(ArgumentError("$L is not invertible"))
    G = L.group
    E = elements(G)
    i = findfirst(==(identity_element(G)), E)
    return LinearCA(G, (E[j] => Minv[i, j] for j in eachindex(E)); p=L.p)
end
