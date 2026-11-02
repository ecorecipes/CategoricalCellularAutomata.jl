# The research extensions: stochastic cellular automata (exact distributions against their definition
# and against sampling on CellularAutomataCore; couplings; copying), and composition of core models with
# undirected wiring diagrams (against hand-written layered rules).

function same_distribution(a, b)
    return Set(keys(a)) == Set(keys(b)) &&
           all(isapprox(a[k], b[k]; atol=1e-12) for k in keys(b))
end

@testset "stochastic cellular automata" begin
    G = CyclicGroup(4)
    B = FinAlphabet(0:1)
    κ = p -> (q=0.1 + 0.25 * sum(p); [1 - q, q])
    noisy = StochasticCA(G, [3, 0, 1], κ; dom=B)
    x = Configuration(G, [1, 0, 0, 1])
    d = distribution(noisy, x)
    @test sum(values(d)) ≈ 1 && length(d) == 16
    # cells are independent given the input, each with its kernel
    for g in elements(G)
        q = κ((x[mod(g - 1, 4)], x[g], x[mod(g + 1, 4)]))
        @test marginal(d, y -> y[g])[1] ≈ q[2]
    end
    y0 = Configuration(G, [1, 1, 0, 0])
    @test d[y0] ≈
          prod(κ((x[mod(g - 1, 4)], x[g], x[mod(g + 1, 4)]))[y0[g] + 1] for g in 0:3)
    @test distribution(noisy, Dict(x => 1.0)) == d
    @test sprint(show, noisy) ==
          "StochasticCA over CyclicGroup(4) with memory set [3, 0, 1]: [0, 1] → [0, 1]"
    # a deterministic automaton is a kernel of point masses
    r90 = CellularAutomaton(G, [3, 1], p -> xor(p...); dom=B)
    @test distribution(StochasticCA(r90), x) == Dict(r90(x) => 1.0)

    # sampling on CellularAutomataCore agrees with the exact distribution
    runs = [solve(CAProblem(noisy, x, 1; seed=s)).u[end] for s in 1:4000]
    for (pattern, p) in marginal(d, y -> (y[0], y[1]))
        freq = count(u -> (u[1], u[2]) == pattern, runs) / length(runs)
        @test abs(freq - p) < 4 * sqrt(p * (1 - p) / length(runs))
    end

    # two steps: the composite's cells are no longer independent
    two = distribution(noisy, d)
    @test sum(values(two)) ≈ 1
    joint = marginal(two, y -> (y[0], y[1]))
    m0, m1 = marginal(two, y -> y[0]), marginal(two, y -> y[1])
    @test !(joint[(1, 1)] ≈ m0[1] * m1[1])

    # copying is not natural: a copied run against two independent runs
    copied = marginal(d, y -> (y, y))
    @test sum(p for ((a, b), p) in copied if a == b) ≈ 1
    @test sum(p^2 for p in values(d)) < 0.5

    # pairs with the same marginals, different couplings
    other = StochasticCA(G, [0], p -> (q=0.2 + 0.5 * p[1]; [1 - q, q]); dom=B)
    for coupling in (:independent, :shared)
        P = stochastic_pair(noisy, other; coupling)
        dp = distribution(P, x)
        @test same_distribution(marginal(dp, y -> Configuration(G, first.(parent(y)))), d)
        @test same_distribution(marginal(dp, y -> Configuration(G, last.(parent(y)))),
                                distribution(other, x))
    end
    differ(P) = sum((p for (y, p) in distribution(P, x) if y[0][1] != y[0][2]); init=0.0)
    @test differ(stochastic_pair(noisy, other; coupling=:shared)) <
          differ(stochastic_pair(noisy, other; coupling=:independent))
    @test differ(stochastic_pair(noisy, noisy; coupling=:shared)) ≈ 0 atol = 1e-12

    @test_throws ArgumentError stochastic_pair(noisy, other; coupling=:copula)
    @test_throws ArgumentError distribution(StochasticCA(G, [0], p -> [0.5, 0.6]; dom=B), x)
    @test_throws ArgumentError distribution(StochasticCA(CyclicGroup(20), [0],
                                                         p -> [0.5, 0.5];
                                                         dom=B),
                                            Configuration(CyclicGroup(20), zeros(Int, 20)))
    @test_throws DomainMismatchError LocalRule(StochasticCA(G, [0], p -> [1.0];
                                                            dom=B, codom=FinAlphabet([:a])))
end

@testset "composing core models" begin
    crop = @camodel Crop begin
        @states host::Int8 = 0 aphid::Int8 = 0
        @neighbourhood VonNeumann(1)
        @rule (host=cell.host == 1 || cell.aphid >= 2 ? Int8(1) : Int8(0), aphid=cell.aphid)
    end
    aphids = @camodel Aphids begin
        @states host::Int8 = 0 aphid::Int8 = 0
        @parameters loss = 1
        @neighbourhood VonNeumann(1)
        @rule begin
            a = cell.host == 1 ? Int8(3) :
                Int8(max(0, max(cell.aphid, maximum(n.aphid for n in nbrs)) - loss))
            (host=cell.host, aphid=a)
        end
    end
    d = @relation (host, aphid) begin
        crop(host, aphid)
        aphids(host, aphid)
    end
    model = oapply(d,
                   (crop=OpenCAModel(crop; reads=[:aphid]),
                    aphids=OpenCAModel(aphids; reads=[:host])); name=:CropAphid)
    @test [s.name for s in states(model)] == [:host, :aphid]
    @test occursin("crop + aphids", sprint(show, MIME"text/plain"(), model))
    @test defaults(model) == (crop=(;), aphids=(loss=1,))
    # against the same model written by hand
    byhand = LocalRule(VonNeumann(1)) do c, n, ctx
        a = c.host == 1 ? Int8(3) :
            Int8(max(0, max(c.aphid, maximum(m.aphid for m in n)) - 1))
        return (host=c.host == 1 || c.aphid >= 2 ? Int8(1) : Int8(0), aphid=a)
    end
    space = Torus(20, 20)
    u0 = (host=zeros(Int8, 20, 20), aphid=zeros(Int8, 20, 20))
    u0.host[10, 10] = 1
    composite = solve(CAProblem(model, (host=u0.host,), 15; space))
    @test composite.u == solve(CAProblem(byhand, u0, 15; space)).u
    @test count(==(1), composite.u[end].host) > 1
    # box parameters by name
    slow = solve(CAProblem(model, (host=u0.host,), 15, (aphids=(loss=2,),); space))
    @test count(==(1), slow.u[end].host) < count(==(1), composite.u[end].host)

    # random numbers: per box by default, shared on request
    coin(name) = CAModel(LocalRule((c, n, ctx) -> Int8(bernoulli(ctx, 0.5)), VonNeumann(1));
                         name, states=(coin=Int8(0),))
    pair_d = @relation (a, b) begin
        first(a)
        second(b)
    end
    boxes = (first=OpenCAModel(coin(:first)), second=OpenCAModel(coin(:second)))
    independent = solve(CAProblem(oapply(pair_d, boxes), (), 1; space, seed=4)).u[end]
    shared = solve(CAProblem(oapply(pair_d, boxes; shared_randomness=true), (), 1; space,
                             seed=4)).u[end]
    @test shared.a == shared.b
    @test 0.3 < count(independent.a .!= independent.b) / 400 < 0.7

    # internal layers, unowned layers, conflicts and mistakes
    tracker = CAModel(LocalRule((c, n, ctx) -> (host=Int8(9), age=c.age + 1),
                                VonNeumann(1));
                      name=:tracker, states=(host=Int8(0), age=0))
    d2 = @relation (host,) begin
        watch(host)
        idle(host)
    end
    idle = CAModel(LocalRule((c, n, ctx) -> Int8(7), VonNeumann(1)); name=:idle,
                   states=(host=Int8(0),))
    m2 = oapply(d2,
                (watch=OpenCAModel(tracker; ports=[:host], reads=[:host]),
                 idle=OpenCAModel(idle; reads=[:host])))
    @test [s.name for s in states(m2)] == [:host, :watch_age]
    s2 = solve(CAProblem(m2, (), 3; space=Torus(4, 4)))
    @test all(==(0), s2.u[end].host) && all(==(3), s2.u[end].watch_age)  # nobody owns host
    @test_throws LayerConflictError oapply(d,
                                           (crop=OpenCAModel(crop; reads=[:aphid]),
                                            aphids=OpenCAModel(aphids)))
    @test occursin("crop and aphids",
                   sprint(showerror, LayerConflictError(:host, [:crop, :aphids])))
    @test_throws ArgumentError oapply(d,
                                      (crop=OpenCAModel(crop; ports=[:host]),
                                       aphids=OpenCAModel(aphids)))
    @test_throws ArgumentError OpenCAModel(crop; ports=[:pest])
    @test_throws ArgumentError OpenCAModel(crop; ports=[:host], reads=[:aphid])
    nohood = CAModel(LocalRule((c, n, ctx) -> c); name=:x, states=(host=Int8(0), b=0))
    @test_throws ArgumentError oapply(d2,
                                      (watch=OpenCAModel(nohood; ports=[:host]),
                                       idle=OpenCAModel(idle; reads=[:host])))
    @test sprint(show, OpenCAModel(crop; reads=[:aphid])) ==
          "OpenCAModel Crop with ports (host, aphid), reading (aphid)"
end
