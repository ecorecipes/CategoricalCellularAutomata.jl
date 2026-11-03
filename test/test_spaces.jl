# Geometries: neighbourhood spaces built from core spaces must step exactly as the core does, the
# maps between them must preserve neighbours, and pulling back along them must commute with local
# rules (all rules for coverings, reflection-symmetric ones for folds). Composites built with
# oapply must run on hexagonal lattices and graphs as the same model written by hand.

function core_step(rule, space, u)
    return solve(CAProblem(rule, u, 1; space); backend=ReferenceBackend()).u[end]
end

@testset "neighbourhood spaces" begin
    rng = Xoshiro(1)
    for (space, rule) in
        ((Torus(9, 7), Life()), (Grid(9, 7; boundary=Reflecting()), Life()),
         (Grid(9, 7; boundary=Constant(1)), Life()),
         (Grid(9, 7; boundary=(Periodic(), Constant(0))), Life()),
         (Grid(6, 5; boundary=(Constant(0), Constant(1))), Life()),
         (HexGrid(8, 6), Life()),
         (Grid(30; boundary=Reflecting()), Wolfram(110)),
         (Torus(30), Totalistic(52; radius=2)))
        S = neighbourhood_space(space, CellularAutomataCore.neighbourhood(rule))
        for _ in 1:3
            u = rand(rng, 0:1, size(space)...)
            @test apply_local(rule, S, vec(u)) == vec(core_step(rule, space, u))
        end
    end
    # a pinned cell for each constant, holding it; its neighbours are itself
    S = neighbourhood_space(Grid(6, 5; boundary=(Constant(0), Constant(1))), Moore(1))
    @test free_cells(S) == 30 && sort(collect(values(S.pinned))) == [0, 1]
    @test all(c -> all(==(c), S.neighbours[c]), keys(S.pinned))
    @test occursin("2 pinned", sprint(show, S))
    # graphs: lists of varying length, read in the graph's order
    g = GraphSpace(12, [(i, mod1(i + k, 12)) for i in 1:12 for k in (1, 5)])
    g2 = GraphSpace([[2, 3], [1], [1, 2, 4], [3]])
    maj = LocalRule(GraphNeighbours()) do c, n, ctx
        k = 2count(==(1), n)
        return k > length(n) ? 1 : k < length(n) ? 0 : c
    end
    for space in (g, g2), _ in 1:3
        u = rand(rng, 0:1, length(space))
        @test apply_local(maj, neighbourhood_space(space), u) == core_step(maj, space, u)
    end
    @test neighbourhood_space(g2).neighbours == [[2, 3], [1], [1, 2, 4], [3]]
    @test_throws ArgumentError neighbourhood_space(g, Moore(1))
    @test_throws ArgumentError NeighbourhoodSpace([[2], [5]])
    @test_throws ArgumentError NeighbourhoodSpace([[1], [2]]; pinned=Dict(1 => 0))
    @test_throws ArgumentError apply_local(maj, neighbourhood_space(g2), [0, 1])

    # square and hexagonal tori are Cayley spaces of the same group with different generators
    G = TorusGroup(8, 6)
    hexes = [Tuple(o)
             for o in
                 CellularAutomataCore.neighbourhood_offsets(Hexagonal(1), HexGrid(8, 6))]
    @test cayley_space(G, hexes) == neighbourhood_space(HexGrid(8, 6), Hexagonal(1))
    vn = [(1, 0), (-1, 0), (0, 1), (0, -1)]
    @test cayley_space(G, vn) ==
          neighbourhood_space(Torus(8, 6), Offsets(CartesianIndex.(vn)))
    @test cayley_space(CyclicGroup(7), [1, -1]).neighbours[1] == [2, 7]
    # a cellular automaton over a group is a local rule on its Cayley space
    A = FinAlphabet(0:1)
    τ = CellularAutomaton(Life(), Torus(6, 5); alphabet=A)
    S = neighbourhood_space(τ)
    for _ in 1:3
        x = Configuration(TorusGroup(6, 5), rand(rng, 0:1, 6, 5))
        @test vec(parent(τ(x))) == apply_local(Life(), S, vec(parent(x)))
    end
end

@testset "maps of spaces" begin
    rng = Xoshiro(2)
    # coverings preserve neighbours slot by slot, so every rule commutes with pulling back
    function lookup(k)
        table = rand(rng, 0:1, 2^(k + 1))
        return (c, nb) -> table[1 + c + 2sum(nb[i] << (i - 1) for i in eachindex(nb))]
    end
    for (big, small, nbhd) in ((Torus(12, 8), Torus(6, 4), Moore(1)),
                               (Torus(9, 9), Torus(3, 9), VonNeumann(1)),
                               (Torus(20), Torus(5),
                                Offsets([CartesianIndex(-1), CartesianIndex(2)])))
        f = covering(big, small, nbhd)
        @test is_morphism(f)
        k = length(f.dom.neighbours[1])
        for _ in 1:4
            rule = lookup(k)
            x = rand(rng, 0:1, free_cells(f.codom))
            @test apply_local(rule, f.dom, pullback(f, x)) ==
                  pullback(f, apply_local(rule, f.codom, x))
        end
    end
    @test_throws ArgumentError covering(Torus(10, 8), Torus(6, 4))
    @test_throws ArgumentError covering(Grid(12, 8), Torus(6, 4))
    # reflecting edges: the quotient of a doubled torus by reflections, with slots permuted on the
    # mirrored half; rules symmetric under reflection commute
    life = (c, nb) -> (s=sum(nb); s == 3 || (c == 1 && s == 2) ? 1 : 0)
    for (space, nbhd, mirrored) in
        ((Grid(7, 5; boundary=Reflecting()), Moore(1), 2),
         (Grid(6, 4; boundary=(Reflecting(), Periodic())), Moore(1), 1),
         (Grid(9; boundary=Reflecting()), Offsets([CartesianIndex(-1), CartesianIndex(1)]),
          1))
        f = reflection_fold(space, nbhd)
        @test is_morphism(f) && free_cells(f.dom) == 2^mirrored * free_cells(f.codom)
        for _ in 1:4
            x = rand(rng, 0:1, free_cells(f.codom))
            @test apply_local(life, f.dom, pullback(f, x)) ==
                  pullback(f, apply_local(life, f.codom, x))
        end
    end
    # many steps: a reflecting run is the doubled torus's run from the mirrored state, restricted
    space = Grid(10, 7; boundary=Reflecting())
    f = reflection_fold(space, Moore(1))
    u = rand(rng, 0:1, 10, 7)
    sol = solve(CAProblem(Life(), u, 12; space))
    big = solve(CAProblem(Life(), reshape(pullback(f, vec(u)), 20, 14), 12;
                          space=Torus(20, 14)))
    @test all(t -> vec(big.u[t]) == pullback(f, vec(sol.u[t])), eachindex(sol.u))
    # an anisotropic rule (copy one neighbour) does not descend along the fold
    copyone = (c, nb) -> nb[4]
    fv = reflection_fold(Grid(7, 5; boundary=Reflecting()), VonNeumann(1))
    x = rand(rng, 0:1, 35)
    @test apply_local(copyone, fv.dom, pullback(fv, x)) !=
          pullback(fv, apply_local(copyone, fv.codom, x))
    @test_throws ArgumentError reflection_fold(Torus(5, 5))
    @test_throws ArgumentError reflection_fold(Grid(5, 5; boundary=Constant(0)))
    @test_throws ArgumentError reflection_fold(Grid(5, 5; boundary=Reflecting()),
                                               Offsets([CartesianIndex(1, 0)]))
    # spaces and their maps form a category: coverings compose to coverings, identities are units,
    # composites preserve neighbours, and pulling back along a composite pulls back along each map
    a = covering(Torus(24, 16), Torus(12, 8), Moore(1))
    b = covering(Torus(12, 8), Torus(6, 4), Moore(1))
    @test compose(a, b) == covering(Torus(24, 16), Torus(6, 4), Moore(1))
    @test compose(id(dom(a)), a) == a && compose(a, id(codom(a))) == a
    fold = reflection_fold(Grid(6, 4; boundary=Reflecting()), Moore(1))
    h = compose(a, fold)
    @test is_morphism(h) && dom(h) == dom(a) && codom(h) == codom(fold)
    x = rand(rng, 0:1, 24)
    @test pullback(h, x) == pullback(a, pullback(fold, x))
    @test apply_local(life, dom(h), pullback(h, x)) ==
          pullback(h, apply_local(life, codom(h), x))
    @test compose(compose(a, b), id(codom(b))) == compose(a, compose(b, id(codom(b))))
    @test_throws DomainMismatchError compose(b, a)
    # maps that do not preserve neighbours
    S = neighbourhood_space(Torus(4), Offsets([CartesianIndex(1)]))
    @test is_morphism(SpaceMorphism(S, S, [2, 3, 4, 1]))
    @test !is_morphism(SpaceMorphism(S, S, [1, 1, 2, 2]))
    @test !is_morphism(SpaceMorphism(S, S, [2, 3, 4, 1], [[2], [1], [1], [1]]))
    @test_throws ArgumentError SpaceMorphism(S, S, [1, 2])
    @test_throws ArgumentError SpaceMorphism(S, S, [1, 2, 3, 9])
    @test occursin("SpaceMorphism", sprint(show, SpaceMorphism(S, S, [2, 3, 4, 1])))
end

@testset "composites on other geometries" begin
    # the crop and aphid composite, with hexagonal neighbourhoods and on a graph
    for (space, nbhd) in ((HexGrid(16, 12), Hexagonal(1)),
                          (GraphSpace(40, [(i, mod1(i + k, 40)) for i in 1:40 for k in (1, 9)]),
                           GraphNeighbours()))
        croprule = LocalRule(nbhd) do c, n, ctx
            return (host=c.host == 1 || c.aphid >= 2 ? Int8(1) : Int8(0), aphid=c.aphid)
        end
        aphidrule = LocalRule(nbhd) do c, n, ctx
            a = c.host == 1 ? Int8(3) :
                Int8(max(0, max(c.aphid, maximum(m.aphid for m in n)) - 1))
            return (host=c.host, aphid=a)
        end
        crop = CAModel(croprule; name=:crop, states=(host=Int8(0), aphid=Int8(0)))
        aphids = CAModel(aphidrule; name=:aphids, states=(host=Int8(0), aphid=Int8(0)))
        d = @relation (host, aphid) begin
            crop(host, aphid)
            aphids(host, aphid)
        end
        model = oapply(d,
                       (crop=OpenCAModel(crop; reads=[:aphid]),
                        aphids=OpenCAModel(aphids; reads=[:host])); space)
        byhand = LocalRule(nbhd) do c, n, ctx
            a = c.host == 1 ? Int8(3) :
                Int8(max(0, max(c.aphid, maximum(m.aphid for m in n)) - 1))
            return (host=c.host == 1 || c.aphid >= 2 ? Int8(1) : Int8(0), aphid=a)
        end
        host = zeros(Int8, size(space)...)
        host[1] = 1
        u0 = (host=host, aphid=zeros(Int8, size(space)...))
        composite = solve(CAProblem(model, (host=host,), 10; space))
        @test composite.u == solve(CAProblem(byhand, u0, 10; space)).u
        @test count(==(1), composite.u[end].host) > 1
    end
    keep = CAModel(LocalRule((c, n, ctx) -> c, Hexagonal(1)); name=:a,
                   states=(x=Int8(0), y=Int8(0)))
    sq = CAModel(LocalRule((c, n, ctx) -> c, Moore(1)); name=:b,
                 states=(x=Int8(0), y=Int8(0)))
    d = @relation (x, y) begin
        a(x, y)
        b(x, y)
    end
    boxes = (a=OpenCAModel(keep; reads=[:y]), b=OpenCAModel(sq; reads=[:x]))
    ring = GraphSpace(6, [(i, mod1(i + 1, 6)) for i in 1:6])
    @test_throws ArgumentError oapply(d, boxes; space=ring)
    @test_throws ArgumentError oapply(d, boxes; space=:hex)
end
