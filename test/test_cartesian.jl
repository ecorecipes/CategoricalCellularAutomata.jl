# Cellular automata and the cartesian category CA(G). Evaluation is checked against the definition
# written out by hand; composites and pairs against applying the automata one after the other; the
# category and product laws with random lookup-table rules on abelian and non-abelian groups.

# A random local rule over an alphabet, as a lookup table of every pattern on `k` cells.
function random_rule(rng, A, B, k)
    table = Dict(p => rand(rng, B.values)
                 for p in Iterators.product(ntuple(_ -> A.values, k)...))
    return p -> table[p]
end
function random_ca(rng, G, S, A, B=A)
    return CellularAutomaton(G, S, random_rule(rng, A, B, length(S)); dom=A, codom=B)
end
random_config(rng, G, A) = Configuration(G, rand(rng, A.values, shape(G)))

@testset "cellular automata and CA(G)" begin
    rng = Random.Xoshiro(11)
    A, B, C = FinAlphabet(0:1), FinAlphabet([:a, :b, :c]), FinAlphabet(1:2)
    S3 = FiniteGroup(PERMS3, (a, b) -> a[b])
    groups = [(CyclicGroup(7), [6, 0, 1], [0, 2]),
              (TorusGroup(3, 4), [(0, 0), (1, 0), (0, 3)],
               [(2, 1), (0, 0)]),
              (S3, [1, 2, 4], [3, 5])]

    @testset "evaluation on $G" for (G, S, T) in groups
        τ = random_ca(rng, G, S, A, B)
        x = random_config(rng, G, A)
        y = τ(x)
        @test all(y[g] == τ.rule(Tuple(x[mul(G, s, g)] for s in S)) for g in elements(G))
        # a cellular automaton commutes with the shifts
        @test all(τ(shift(x, g)) == shift(y, g) for g in elements(G))
        @test memory_set(τ) == S && local_map(τ) === τ.rule && group(τ) == G
        @test dom(τ) == FullShift(A, G) && codom(τ) == FullShift(B, G)
    end

    @testset "composition and its laws on $G" for (G, S, T) in groups
        τ, σ, ρ = random_ca(rng, G, S, A, B), random_ca(rng, G, T, B, C),
                  random_ca(rng, G, S, C, A)
        x = random_config(rng, G, A)
        @test compose(τ, σ)(x) == σ(τ(x)) == (σ ∘ τ)(x)
        @test compose(τ, σ) == σ ∘ τ
        @test compose(compose(τ, σ), ρ) == compose(τ, compose(σ, ρ)) == compose(τ, σ, ρ)
        @test compose(id(dom(τ)), τ) == τ == compose(τ, id(codom(τ)))
        @test sort(memory_set(compose(τ, σ))) ==
              sort(unique(mul(G, s, t) for s in S for t in T))
    end

    @testset "products on $G" for (G, S, T) in groups
        X, Y, Z = FullShift(A, G), FullShift(B, G), FullShift(C, G)
        f, g = random_ca(rng, G, S, A, B), random_ca(rng, G, T, A, C)
        x = random_config(rng, G, A)
        fg = pair(f, g)
        @test fg(x) == Configuration(h -> (f(x)[h], g(x)[h]), G)
        @test codom(fg) == otimes(Y, Z) && Set(memory_set(fg)) == Set(union(S, T))
        @test compose(fg, proj1(Y, Z)) == f && compose(fg, proj2(Y, Z)) == g
        # uniqueness: any h into a product is the pair of its projections
        YZ = otimes(Y, Z)
        h = CellularAutomaton(G, S, random_rule(rng, A, alphabet(YZ), length(S)); dom=A,
                              codom=YZ)
        @test pair(compose(h, proj1(Y, Z)), compose(h, proj2(Y, Z))) == h
        # the monoidal product, braiding, copying and deleting
        f2 = random_ca(rng, G, T, B, C)
        xy = Configuration(G,
                           [(a, b)
                            for (a, b) in zip(parent(x), rand(rng, B.values, shape(G)))])
        @test otimes(f, f2)(xy) ==
              Configuration(k -> (f(Configuration(h -> xy[h][1], G))[k],
                                  f2(Configuration(h -> xy[h][2], G))[k]),
                            G)
        @test otimes(f, f2) == pair(compose(proj1(X, Y), f), compose(proj2(X, Y), f2))
        @test compose(braid(X, Y), braid(Y, X)) == id(otimes(X, Y))
        @test compose(mcopy(X), proj1(X, X)) == id(X) == compose(mcopy(X), proj2(X, X))
        @test compose(f, mcopy(Y)) == pair(f, f)        # copying is natural for deterministic CA
        @test compose(f, delete(Y)) == delete(X)        # and so is deleting
        @test otimes(X, munit()) == X == otimes(munit(), X)
        @test pair(f, delete(X)) == f && pair(delete(X), g) == g
        @test proj1(X, munit()) == id(X) && proj2(munit(), X) == id(X)
        @test otimes(X, Y, Z) == otimes(otimes(X, Y), Z) == otimes(X, otimes(Y, Z))
        @test alphabet(otimes(X, Y, Z)).values[2] == (1, :a, 1)  # flat tuples
        # strict associativity of pairing, as the free cartesian category assumes
        @test pair(pair(f, g), f) == pair(f, pair(g, f))
        @test compose(pair(pair(f, g), f), proj2(otimes(Y, Z), Y)) == f
        @test otimes(f, f2, id(X)) == otimes(otimes(f, f2), id(X))
    end

    @testset "powers, equality and display" begin
        G = CyclicGroup(9)
        r90 = CellularAutomaton(G, [8, 1], p -> xor(p...); dom=A)
        @test r90^3 == compose(r90, r90, r90)
        @test r90 != CellularAutomaton(G, [8, 1], p -> p[1] | p[2]; dom=A)
        @test r90 != CellularAutomaton(CyclicGroup(8), [7, 1], p -> xor(p...); dom=A)
        @test sprint(show, r90) ==
              "CellularAutomaton over CyclicGroup(9) with memory set [8, 1]: [0, 1] → [0, 1]"
        @test sprint(show, munit()) == "munit()"
        @test sprint(show, FullShift(A, G)) ==
              "FullShift(FinAlphabet([0, 1]), CyclicGroup(9))"
        @test sprint(show, otimes(FullShift(A, G), FullShift(B, G))) ==
              "FullShift([0, 1] ⊗ [:a, :b, :c], CyclicGroup(9))"
        @test_throws ArgumentError r90^0
        big = CellularAutomaton(G, collect(0:8), p -> p[1]; dom=FinAlphabet(1:6))
        @test_throws ArgumentError big == big  # 6^9 patterns
    end

    @testset "errors" begin
        G, H = CyclicGroup(5), CyclicGroup(6)
        τ = CellularAutomaton(G, [0], only; dom=A)
        @test_throws GroupMismatchError compose(τ, CellularAutomaton(H, [0], only; dom=A))
        @test_throws GroupMismatchError pair(τ, CellularAutomaton(H, [0], only; dom=A))
        @test_throws GroupMismatchError τ(Configuration(H, zeros(Int, 6)))
        @test_throws GroupMismatchError otimes(FullShift(A, G), FullShift(A, H))
        @test_throws DomainMismatchError compose(τ, CellularAutomaton(G, [0], only; dom=B))
        @test_throws DomainMismatchError pair(τ, CellularAutomaton(G, [0], only; dom=B))
        @test_throws DomainMismatchError CellularAutomaton(G, [0], p -> :a; dom=A, codom=B)^2
        @test_throws ArgumentError CellularAutomaton(G, [0, 7], only; dom=A)
        @test_throws ArgumentError CellularAutomaton(G, [1, 1], only; dom=A)
        @test_throws ArgumentError id(munit())
        @test occursin("CyclicGroup(5) and CyclicGroup(6)",
                       sprint(showerror, GroupMismatchError("x", G, H)))
        @test occursin("expected", sprint(showerror, DomainMismatchError("x", 1, 2)))
    end

    @testset "wiring diagrams" begin
        G = CyclicGroup(10)
        X = FullShift(A, G)
        r90 = CellularAutomaton(G, [9, 1], p -> xor(p...); dom=A)
        r150 = CellularAutomaton(G, [9, 0, 1], p -> xor(p...); dom=A)
        pres = @present P(FreeCartesianCategory) begin
            X::Ob
            f::Hom(X, X)
            g::Hom(X, X)
        end
        d = @program pres (x::X) begin
            y = f(x)
            return (g(y), f(y), x)
        end
        h = realize(d, pres; X, f=r90, g=r150)
        x = random_config(rng, G, A)
        y = r90(x)
        @test h(x) == Configuration(k -> (r150(y)[k], r90(y)[k], x[k]), G)
        @test h == pair(pair(compose(r90, r150), compose(r90, r90)), id(X))
        @test codom(h) == otimes(X, X, X)
    end
end
