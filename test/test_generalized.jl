# Homomorphisms, free products, generalised cellular automata (evaluation against the definition,
# factorisation, composition against sequential evaluation, pullback and pushforward commuting, the
# torus quotient square), weak products, and linear and monotone automata against generic ones.

@testset "homomorphisms and free products" begin
    G6, G3, G2 = CyclicGroup(6), CyclicGroup(3), CyclicGroup(2)
    φ = GroupHom(g -> g % 3, G6, G3)
    @test φ(5) == 2 && sprint(show, φ) == "GroupHom(CyclicGroup(6) → CyclicGroup(3))"
    @test_throws ArgumentError GroupHom(g -> g, G3, G6)          # not a homomorphism
    ψ = GroupHom(g -> 2g % 6, G3, G6)
    @test (φ ∘ ψ) == GroupHom(g -> 2g % 3, G3, G3) &&
          GroupHom(G3) == GroupHom(identity, G3, G3)
    @test_throws GroupMismatchError φ ∘ φ

    F = FreeProduct(G2, G3)
    @test length(ball(F, 0)) == 1 && length(ball(F, 1)) == 4 && length(ball(F, 3)) == 14
    @test sprint(show, F) == "CyclicGroup(2) ∗ CyclicGroup(3)"
    words = ball(F, 3)
    e = identity_element(F)
    for u in words
        @test mul(F, u, inverse(F, u)) == e == mul(F, inverse(F, u), u)
        @test mul(F, e, u) == u == mul(F, u, e)
        for v in words[1:7], w in words[1:7]
            @test mul(F, mul(F, u, v), w) == mul(F, u, mul(F, v, w))
        end
    end
    @test mul(F, ((1, 1), (2, 1)), ((2, 2), (1, 1))) == ()
    @test mul(F, ((2, 1),), ((2, 1),)) == ((2, 2),)
    ι1, ι2 = inclusion(F, 1), inclusion(F, 2)
    @test ι1(1) == ((1, 1),) && ι2(0) == ()
    K = CyclicGroup(6)
    φ1, φ2 = GroupHom(g -> 3g, G2, K), GroupHom(g -> 2g, G3, K)
    Φ = induced_hom(F, φ1, φ2)
    @test all(Φ(ι1(g)) == φ1(g) for g in elements(G2)) &&
          all(Φ(ι2(g)) == φ2(g) for g in elements(G3))
    @test all(Φ(mul(F, u, v)) == mul(K, Φ(u), Φ(v)) for u in words, v in words)
    @test_throws ArgumentError inclusion(F, 3)
    @test_throws ArgumentError ball(F, -1)
end

@testset "generalised cellular automata" begin
    rng = Random.Xoshiro(21)
    B = FinAlphabet(0:1)
    G, H = CyclicGroup(4), CyclicGroup(8)
    φ = GroupHom(h -> h % 4, H, G)
    μ = random_rule(rng, B, B, 2)
    T = GeneralizedCA(φ, [3, 1], μ; dom=B)
    x = random_config(rng, G, B)
    @test T(x) == Configuration(h -> μ((x[mul(G, 3, φ(h))], x[mul(G, 1, φ(h))])), H)
    @test T(x, 5) == T(x)[5]
    @test dom(T) == FullShift(B, G) && codom(T) == FullShift(B, H)
    # factorisation: T = φ* after τ
    φ0, τ = factorize(T)
    @test φ0 === T.hom && T == compose(τ, pullback(φ, codom(τ)))
    @test T(x) == pullback(φ, τ(x))
    # an ordinary CA is one over the identity
    @test GeneralizedCA(τ) == τ && τ == GeneralizedCA(τ)
    # composition against applying the two in turn, across three groups
    K = CyclicGroup(16)
    ψ = GroupHom(k -> k % 8, K, H)
    T2 = GeneralizedCA(ψ, [7, 0, 2], random_rule(rng, B, B, 3); dom=B)
    @test compose(T, T2)(x) == T2(T(x)) == (T2 ∘ T)(x)
    @test compose(T, T2).hom == φ ∘ ψ
    T3 = GeneralizedCA(GroupHom(K), [1, 15], random_rule(rng, B, B, 2); dom=B)
    @test compose(compose(T, T2), T3) == compose(T, compose(T2, T3))
    # pushforward and pullback commute (Lemma 4.6)
    C = FinAlphabet([:a, :b])
    f = v -> v == 0 ? :a : :b
    @test compose(pushforward(f, G; dom=B, codom=C), pullback(φ, C)) ==
          compose(pullback(φ, B), pushforward(f, H; dom=B, codom=C))
    @test pullback(φ, x) == Configuration(h -> x[h % 4], H)
    # the torus quotient square: Life on a 4 × 4 tile is Life on 8 × 8 periodic configurations
    B8 = FinAlphabet(Int8[0, 1])
    small = CellularAutomaton(Life(), Torus(4, 4); alphabet=B8)
    large = CellularAutomaton(Life(), Torus(8, 8); alphabet=B8)
    π = GroupHom(g -> mod.(g, 4), TorusGroup(8, 8), TorusGroup(4, 4))
    @test compose(small, pullback(π, B8)) == compose(pullback(π, B8), large)
    # two automata over different homomorphisms can be equal: a constant map
    const0(ϕ) = GeneralizedCA(ϕ, [0], p -> 0; dom=B)
    @test const0(φ) == const0(GroupHom(h -> 0, H, G))
    @test T != const0(φ)
    # errors
    @test_throws DomainMismatchError compose(T, T)
    @test_throws GroupMismatchError T(random_config(rng, H, B))
    @test_throws GroupMismatchError GeneralizedCA(φ, CellularAutomaton(H, [0], only; dom=B))
    @test occursin("GeneralizedCA over GroupHom(CyclicGroup(8) → CyclicGroup(4))",
                   sprint(show, T))
end

@testset "weak products" begin
    B = FinAlphabet(0:1)
    K = CyclicGroup(6)
    G2, G3 = CyclicGroup(2), CyclicGroup(3)
    φ1, φ2 = GroupHom(g -> 3g, G2, K), GroupHom(g -> 2g, G3, K)
    T1 = GeneralizedCA(φ1, [0, 1], p -> p[1] & p[2]; dom=B)
    T2 = GeneralizedCA(φ2, [0, 5], p -> xor(p...); dom=B)
    X1, X2 = codom(T1), codom(T2)
    P = weak_product(X1, X2)
    @test P.group == FreeProduct(G2, G3) && alphabet(P) == alphabet(otimes(X1, X1))
    π1, π2 = weak_projections(X1, X2)
    u = weak_pair(T1, T2)
    @test codom(u) == P
    @test compose(u, π1) == T1 && compose(u, π2) == T2
    x = Configuration(K, [1, 1, 0, 1, 0, 1])
    F = P.group
    w = mul(F, inclusion(F, 1)(1), inclusion(F, 2)(2))
    @test u(x, w) == (T1.ca(x)[mul(K, 3, 4)], T2.ca(x)[mul(K, 3, 4)])
    @test_throws ArgumentError u(x)  # the free product is infinite
    # not unique: if T1 is constant, another homomorphism on the first factor also works
    C1 = GeneralizedCA(φ1, [0], p -> 1; dom=B)
    v = weak_pair(C1, T2)
    v′ = weak_pair(GeneralizedCA(GroupHom(g -> 0, G2, K), [0], p -> 1; dom=B), T2)
    @test compose(v′, π1) == C1 && compose(v′, π2) == T2
    @test any(v(x, w) != v′(x, w) for w in ball(F, 2))
    @test_throws DomainMismatchError weak_pair(T1,
                                               GeneralizedCA(φ2, [0], only;
                                                             dom=FinAlphabet(0:2)))
end

@testset "linear cellular automata" begin
    rng = Random.Xoshiro(8)
    for (G, p) in ((CyclicGroup(9), 2), (CyclicGroup(7), 3), (TorusGroup(3, 4), 2))
        E = collect(elements(G))
        L = LinearCA(G, [E[rand(rng, eachindex(E))] => rand(rng, 0:(p - 1)) for _ in 1:3];
                     p)
        M = LinearCA(G, [E[rand(rng, eachindex(E))] => rand(rng, 1:(p - 1)) for _ in 1:2];
                     p)
        x = random_config(rng, G, FinAlphabet(0:(p - 1)))
        @test L(x) == CellularAutomaton(L)(x)
        # the fast composition agrees with the generic one
        @test CellularAutomaton(compose(L, M)) ==
              compose(CellularAutomaton(L), CellularAutomaton(M))
        @test compose(L, M)(x) == M(L(x)) == (M ∘ L)(x)
        @test CellularAutomaton(L^3) == CellularAutomaton(L)^3
        @test L^0 == LinearCA(G, [identity_element(G) => 1]; p)
    end
    Z = CyclicGroup(16)
    rule90 = LinearCA(Z, [15 => 1, 1 => 1]; p=2)
    @test rule90^8 == LinearCA(Z, [8 => 2]; p=2) == LinearCA(Z, []; p=2)  # x(g-8) = x(g+8) cancel
    @test coefficients(rule90^2) == Dict(14 => 1, 2 => 1)
    # rule 150 is invertible exactly when 3 does not divide the ring size
    rule150(n) = LinearCA(CyclicGroup(n), [n - 1 => 1, 0 => 1, 1 => 1]; p=2)
    @test isinvertible(rule150(10)) && !isinvertible(rule150(9)) && !isinvertible(rule90)
    L = rule150(10)
    @test compose(L, inv(L)) == L^0 == compose(inv(L), L)
    y = random_config(rng, CyclicGroup(10), FinAlphabet(0:1))
    @test inv(L)(L(y)) == y
    @test_throws ArgumentError inv(rule90)
    @test_throws ArgumentError LinearCA(Z, [0 => 1]; p=4)
    @test_throws ArgumentError rule90^-1
    @test_throws ArgumentError compose(rule90, LinearCA(Z, [0 => 1]; p=3))
    @test sprint(show, rule90) ==
          "LinearCA over CyclicGroup(16) mod 2: 1·x(s=1) + 1·x(s=15)"
end

@testset "monotone cellular automata" begin
    rng = Random.Xoshiro(13)
    B8 = FinAlphabet(Int8[0, 1])
    # bootstrap percolation: infested cells stay so, others become infested with two infested neighbours
    spread = LocalRule(VonNeumann(1)) do c, n, ctx
        return c == 1 || count(==(1), n) >= 2 ? Int8(1) : Int8(0)
    end
    τ = CellularAutomaton(spread, Torus(12, 12); alphabet=B8)
    @test is_monotone(τ)
    @test !is_monotone(CellularAutomaton(Life(), Torus(12, 12); alphabet=B8))
    @test !is_monotone(CellularAutomaton(CyclicGroup(5), [4, 1], p -> xor(p...);
                                         dom=FinAlphabet(0:1)))
    # monotone automata preserve the order of configurations
    G = TorusGroup(12, 12)
    for _ in 1:20
        lo = Int8.(rand(rng, 12, 12) .< 0.15)
        hi = max.(lo, Int8.(rand(rng, 12, 12) .< 0.15))
        a, b = Configuration(G, lo), Configuration(G, hi)
        for _ in 1:4
            a, b = τ(a), τ(b)
        end
        @test all(parent(a) .<= parent(b))
    end
    # a different order: the reversed one
    @test is_monotone(τ; leq=(>=))
end
