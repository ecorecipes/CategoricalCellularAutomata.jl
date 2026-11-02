# The Curtis–Hedlund–Lyndon checks, and the bridge to CellularAutomataCore: a core rule turned into a
# cellular automaton over its torus group, and back, must give the core's own result exactly.

@testset "Curtis–Hedlund–Lyndon" begin
    A = FinAlphabet(0:1)
    G = CyclicGroup(8)
    r110 = CellularAutomaton(G, [7, 0, 1], p -> (110 >> (4p[1] + 2p[2] + p[3])) & 1; dom=A)
    @test is_equivariant(r110, G, A)
    # flipping one fixed cell is not equivariant
    flip = x -> Configuration(g -> g == 0 ? 1 - x[g] : x[g], G)
    @test !is_equivariant(flip, G, A)
    τ = cellular_automaton(r110, G; dom=A)
    @test memory_set(τ) == collect(0:7) && τ == r110
    m = minimal_neighbourhood(τ)
    @test sort(memory_set(m)) == [0, 1, 7] && m == r110
    # rule 90 composed with itself does not depend on the centre cell
    r90 = CellularAutomaton(G, [7, 1], p -> xor(p...); dom=A)
    @test memory_set(r90^2) == [6, 0, 2] &&
          sort(memory_set(minimal_neighbourhood(r90^2))) == [2, 6]
    # a constant rule depends on nothing
    @test isempty(memory_set(minimal_neighbourhood(CellularAutomaton(G, [0, 1], p -> 1;
                                                                     dom=A))))
    # on a non-abelian group
    S3 = FiniteGroup(PERMS3, (a, b) -> a[b])
    σ = CellularAutomaton(S3, [2, 3], p -> p[1] & p[2]; dom=A)
    @test is_equivariant(σ, S3, A)
    @test minimal_neighbourhood(cellular_automaton(σ, S3; dom=A)) == σ
    # too many configurations to enumerate: sampled with an rng, or refused without one
    H = TorusGroup(5, 5)
    life = CellularAutomaton(Life(), Torus(5, 5); alphabet=FinAlphabet([0, 1]))
    @test is_equivariant(life, H, FinAlphabet([0, 1]); rng=Random.Xoshiro(1), samples=5)
    @test_throws ArgumentError is_equivariant(life, H, FinAlphabet([0, 1]))
end

@testset "bridge to CellularAutomataCore" begin
    rng = Random.Xoshiro(5)
    B = FinAlphabet(Int8[0, 1])
    @test torus_group(Torus(7)) == CyclicGroup(7) &&
          torus_group(Torus(3, 4)) == TorusGroup(3, 4)
    @test torus_space(TorusGroup(3, 4)) == Torus(3, 4) &&
          torus_space(CyclicGroup(5)) == Torus(5)
    @test_throws ArgumentError torus_group(Grid(4, 4))

    cases = [(Life(), Torus(8, 9)), (Wolfram(110), Torus(20)),
             (Life("B2/S34"), HexGrid(6, 8)),
             (Life("B3/S23"; neighbourhood=VonNeumann(2)), Torus(5, 6)),
             (Totalistic(52; radius=2), Torus(13))]
    for (rule, space) in cases
        τ = CellularAutomaton(rule, space; alphabet=B)
        G = torus_group(space)
        u0 = Int8.(rand(rng, 0:1, size(space)...))
        core = solve(CAProblem(rule, u0, 6; space))
        x = Configuration(G, u0)
        for t in 1:6
            x = τ(x)
            @test parent(x) == core.u[t + 1]
        end
        # and back: the automaton as a core rule, on two backends
        @test solve(CAProblem(τ, u0, 6)).u == core.u
        @test solve(CAProblem(τ, Configuration(G, u0), 6); backend=ReferenceBackend()).u ==
              core.u
    end
    # a rule of the cell alone still makes a core rule
    G = TorusGroup(4, 4)
    flip = CellularAutomaton(G, [(0, 0)], p -> Int8(1) - p[1]; dom=B)
    u0 = Int8.(rand(rng, 0:1, 4, 4))
    @test solve(CAProblem(flip, u0, 1)).u[end] == 1 .- u0
    # composites run on the core: Life twice is one step of a radius-2 rule
    life = CellularAutomaton(Life(), Torus(10, 10); alphabet=B)
    u0 = Int8.(rand(rng, 0:1, 10, 10))
    @test solve(CAProblem(life^2, u0, 3)).u[end] == solve(CAProblem(Life(), u0, 6)).u[end]
    @test_throws DomainMismatchError LocalRule(CellularAutomaton(G, [(0, 0)], p -> :a;
                                                                 dom=B,
                                                                 codom=FinAlphabet([:a])))
end
