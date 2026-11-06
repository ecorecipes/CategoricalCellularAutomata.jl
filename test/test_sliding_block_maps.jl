@testset "sliding block maps" begin
    rng = Xoshiro(23)
    bit() = [StateVariable(:x, 0; domain=(0, 1))]
    eca(n) = CAModel(Wolfram(n); name=Symbol("rule", n), states=bit())
    models = [eca(n) for n in 0:255]
    rule(n) = models[n + 1]
    # whether a boundary lies between a cell and the next
    kink_code(c, nbrs) = xor(c, nbrs[1])
    right = Offsets((1,))
    kink(F, G) = SlidingBlockMap(rule(F), rule(G), kink_code, right)
    table(n) = [(n >> k) & 1 for k in 0:7]
    bits(n) = rand(rng, 0:1, n)

    @testset "every pair of elementary rules" begin
        found = [(F, G)
                 for F in 0:255, G in 0:255
                 if is_model_map(kink(F, G); dims=1, contexts=1)]
        # The map forgets exactly a global complement, so a rule has a partner when it respects
        # that: complementing all three inputs leaves the output alone or complements it.
        respects(F) = (t=table(F);
                       all(k -> t[k + 1] == t[7 - k + 1], 0:3) ||
                           all(k -> t[k + 1] != t[7 - k + 1], 0:3))
        @test length(found) == 32
        @test sort(unique(first.(found))) == filter(respects, 0:255)
        # and the partner is unique
        @test allunique(first.(found))
        @test (126, 18) in found
        @test (90, 90) in found
        @test !((30, 30) in found)

        # the same answers from the composition of cellular automata, compared by enumeration
        space = Torus(9)
        alphabet = FinAlphabet(0:1)
        automaton(n) = CellularAutomaton(Wolfram(n), space; alphabet)
        square(F, G) = compose(automaton(F),
                               CellularAutomaton(kink(F, G), space; alphabet)) ==
                       compose(CellularAutomaton(kink(F, G), space; alphabet), automaton(G))
        @test all(p -> square(p...), found)
        others = [(rand(rng, 0:255), rand(rng, 0:255)) for _ in 1:40]
        for (F, G) in others
            @test square(F, G) == ((F, G) in found)
        end
    end

    @testset "runs map to runs" begin
        for (F, G) in ((126, 18), (129, 18), (90, 90), (105, 150), (60, 60), (232, 132))
            f = kink(F, G)
            prob = CAProblem(rule(F), (; x=bits(64)), 40; space=Torus(64), seed=3)
            @test is_model_map(f, prob)
            sol, other = solve(prob), solve(pushforward(f, prob))
            @test length(sol.u) == 41
            @test all(t -> pushforward(f, sol.u[t], prob.space) == other.u[t],
                      eachindex(sol.u))
            # each saved state, by hand
            @test other.u[end] ==
                  [xor(sol.u[end][i], sol.u[end][mod1(i + 1, 64)]) for i in 1:64]
        end
        # a pair that is not a map, on a state that shows it
        @test !is_model_map(kink(126, 90),
                            CAProblem(rule(126), (; x=bits(64)), 40;
                                      space=Torus(64), seed=3))
        # saveat is respected
        prob = CAProblem(rule(126), (; x=bits(32)), 12; space=Torus(32))
        @test is_model_map(kink(126, 18), prob; saveat=3)
        # the window may be on the other side, or two wide
        left = SlidingBlockMap(rule(126), rule(18), kink_code, Offsets((-1,)))
        @test is_model_map(left; dims=1)
        @test is_model_map(left, prob)
        wide = SlidingBlockMap(rule(90), rule(90), (c, n) -> xor(n[1], c, n[2]),
                               Offsets((-1,), (1,)))
        @test is_model_map(wide; dims=1)
    end

    @testset "edges are read as a rule reads them" begin
        u = [1, 0, 0, 1]
        f = kink(90, 90)
        @test pushforward(f, u, Torus(4)) == [1, 0, 1, 0]
        @test pushforward(f, u, Grid(4; boundary=Constant(0))) == [1, 0, 1, 1]
        @test pushforward(f, u, Grid(4; boundary=Constant(1))) == [1, 0, 1, 0]
        # the code at an edge reads a constant, and so does the rule, but their constants disagree
        u0 = (; x=bits(32))
        @test !is_model_map(f,
                            CAProblem(rule(90), u0, 30;
                                      space=Grid(32; boundary=Constant(0))))
        @test is_model_map(f, CAProblem(rule(90), u0, 30; space=Torus(32)))
    end

    # Two species compete by copying: each cell takes the state of its left or right neighbour
    # on a coin. The boundaries between them move on the coins of the two cells beside them.
    n = 40
    coin(ctx) = uniform(ctx, 1) < 0.5 ? -1 : 1
    voter = CAModel(LocalRule((c, nbrs, ctx) -> coin(ctx) < 0 ? nbrs[1] : nbrs[2],
                              Offsets((-1,), (1,))); name=:voter, states=bit())
    function wall_rule(N)
        return (c, nbrs, ctx) -> begin
            next = CellContext(ctx.p, ctx.index, ctx.t, mod(ctx.cellid, N) + 1, ctx.seed)
            a, b = coin(ctx), coin(next)
            a < 0 && b < 0 && return nbrs[1]
            a > 0 && b > 0 && return nbrs[2]
            return a < 0 ? xor(nbrs[1], c, nbrs[2]) : c
        end
    end
    walls = CAModel(LocalRule(wall_rule(n), Offsets((-1,), (1,))); name=:walls,
                    states=bit())
    # the same rule that looks only at the cell's own coin: it cannot be a map
    own_coin = CAModel(LocalRule((c, nbrs, ctx) -> coin(ctx) < 0 ? nbrs[1] : nbrs[2],
                                 Offsets((-1,), (1,))); name=:own_coin, states=bit())

    @testset "a stochastic map needs the random numbers of its window" begin
        f = SlidingBlockMap(voter, walls, kink_code, right)
        prob = CAProblem(voter, (; x=bits(n)), 200; space=Torus(n), seed=5)
        @test is_model_map(f, prob)
        @test is_model_map(f; space=Torus(n), contexts=64)
        # another seed, stored or given to the problem, carries through
        @test is_model_map(f, remake(prob; seed=77))
        @test pushforward(f, remake(prob; seed=77)).seed == 77 % UInt64
        bad = SlidingBlockMap(voter, own_coin, kink_code, right)
        @test !is_model_map(bad; space=Torus(n))
        @test !is_model_map(bad, prob)
        # a longer run ends the same both ways, and a ring always has an even number of boundaries
        longer = remake(prob; tspan=(0, 4000))
        counts = sum.(solve(pushforward(f, longer)).u)
        @test solve(pushforward(f, longer)).u[end] ==
              pushforward(f, solve(longer).u[end], Torus(n))
        @test all(iseven, counts)
        # Copying at once, a boundary can split: one block gains boundaries. One cell at a time, each
        # copy moves or removes boundaries, so their number never rises.
        start = zeros(Int, n)
        start[15:25] .= 1
        block = CAProblem(voter, (; x=start), 300; space=Torus(n), seed=1)
        walls_of(sol) = [sum(pushforward(f, u, Torus(n))) for u in sol.u]
        @test maximum(walls_of(solve(block))) > 2
        @test all(<=(0), diff(walls_of(solve(block, RandomSequential()))))
        # perfect alternation and a single species are the two ways to end
        @test all(==(1), pushforward(f, repeat([0, 1], n ÷ 2), Torus(n)))
        alternating = CAProblem(voter, (; x=repeat([0, 1], n ÷ 2)), 5; space=Torus(n))
        @test all(u -> all(==(1), pushforward(f, u, Torus(n))), solve(alternating).u)
        uniform_state = CAProblem(voter, (; x=ones(Int, n)), 5; space=Torus(n))
        @test all(u -> all(==(0), pushforward(f, u, Torus(n))), solve(uniform_state).u)
    end

    @testset "layers, two dimensions and parameters" begin
        # a linear rule commutes with a linear code, whatever the shape of the window
        linear(name) = CAModel(LocalRule((c, nbrs, ctx) -> begin
                                             (a=reduce(xor, map(m -> m.a, nbrs)),
                                              b=xor(c.b, ctx.p.flip))
                                         end, VonNeumann(1)); name,
                               states=[StateVariable(:a, 0; domain=(0, 1)),
                                       StateVariable(:b, 0; domain=(0, 1))],
                               parameters=[Parameter(:flip, 0)])
        L, M = linear(:L), linear(:M)
        code = SlidingBlockMap(L, M, (c, nbrs) -> (a=xor(c.a, nbrs[1].a, nbrs[2].a), b=c.b),
                               Offsets((1, 0), (0, 1)))
        u0 = (a=rand(rng, 0:1, 12, 10), b=rand(rng, 0:1, 12, 10))
        prob = CAProblem(L, u0, 15, (; flip=1); space=Torus(12, 10), seed=1)
        @test is_model_map(code, prob)
        @test solve(pushforward(code, prob)).u[end].b == solve(prob).u[end].b
        @test is_model_map(code; p=(; flip=1), samples=300, dims=2)
        @test !is_model_map(SlidingBlockMap(L, M,
                                            (c, nbrs) -> (a=c.a & nbrs[1].a, b=c.b),
                                            Offsets((1, 0))), prob)

        # parameters go through their map
        scaled = CAModel(LocalRule((c, nbrs, ctx) -> Int(uniform(ctx, 1) < ctx.p.q) *
                                                     xor(nbrs...),
                                   Offsets((-1,), (1,))); name=:scaled, states=bit(),
                         parameters=[Parameter(:q, 1.0)])
        thin = CAModel(LocalRule((c, nbrs, ctx) -> Int(uniform(ctx, 1) < ctx.p.r) *
                                                   xor(nbrs...),
                                 Offsets((-1,), (1,))); name=:thin, states=bit(),
                       parameters=[Parameter(:r, 1.0)])
        # the identity code in a window: it reads a neighbour it ignores
        same = SlidingBlockMap(scaled, thin, (c, nbrs) -> c, right;
                               parameters=p -> (; r=p.q))
        pr = CAProblem(scaled, (; x=bits(30)), 20, (; q=0.4); space=Torus(30), seed=2)
        @test pushforward(same, pr).p == (; r=0.4)
        @test is_model_map(same, pr)
        @test is_model_map(same; p=(; q=0.4), dims=1)
    end

    @testset "graphs: a window of the graph's neighbours" begin
        parity = CAModel(LocalRule((c, nbrs, ctx) -> isempty(nbrs) ? 0 : reduce(xor, nbrs),
                                   GraphNeighbours()); name=:parity, states=bit())
        # adjacency commutes with itself plus the identity, on any graph
        code = SlidingBlockMap(parity, parity,
                               (c, nbrs) -> isempty(nbrs) ? c : xor(c, reduce(xor, nbrs)),
                               GraphNeighbours())
        for g in (GraphSpace(8, [(i, mod1(i + 1, 8)) for i in 1:8]),
                  GraphSpace(9, [(1, 2), (2, 3), (3, 1), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8)]))
            prob = CAProblem(parity, (; x=bits(length(g.neighbours))), 12; space=g)
            @test is_model_map(code, prob)
            @test is_model_map(code; space=g)
        end
    end

    @testset "maps form a category with ModelMaps" begin
        same_action(f, g, u, space) = pushforward(f, u, space) == pushforward(g, u, space)
        u = bits(16)
        space = Torus(16)
        φ = kink(90, 90)
        twice = compose(φ, φ)
        @test twice isa SlidingBlockMap
        @test dom(twice) === rule(90)
        @test codom(twice) === rule(90)
        @test pushforward(twice, u, space) ==
              pushforward(φ, pushforward(φ, u, space), space) ==
              [xor(u[i], u[mod1(i + 2, 16)]) for i in 1:16]
        @test is_model_map(twice; dims=1)
        @test is_model_map(twice, CAProblem(rule(90), (; x=u), 20; space))
        thrice = compose(twice, φ)
        @test same_action(thrice, compose(φ, twice), u, space)
        @test is_model_map(thrice; dims=1)

        # identities, and ModelMaps on either side, keep the window
        i90 = id(rule(90))
        @test same_action(compose(i90, φ), φ, u, space)
        @test same_action(compose(φ, i90), φ, u, space)
        @test compose(i90, φ).window === φ.window

        # A cell-by-cell map composes. Complementing is not a map from rule 90 to itself, since the
        # parity of two complements is the parity of the originals, and complementing the result of
        # the boundary map is not one either. Complementing first is, as the boundaries cannot see it.
        swap = ModelMap(rule(90), rule(90), c -> 1 - c; parameters=identity)
        @test !is_model_map(swap; dims=1)
        before = compose(swap, φ)
        after = compose(φ, swap)
        @test is_model_map(before; dims=1)
        @test !is_model_map(after; dims=1)
        # complementing is what the boundary map cannot see
        @test same_action(before, φ, u, space)
        @test !same_action(after, φ, u, space)
        @test pushforward(after, u, space) == 1 .- pushforward(φ, u, space)
        # a composite through windows on both sides agrees with doing it in two steps
        back_one = SlidingBlockMap(rule(90), rule(90), kink_code, Offsets((-1,)))
        wider = compose(back_one, φ)
        @test pushforward(wider, u, space) ==
              pushforward(φ, pushforward(back_one, u, space), space)

        # A presentation on pairs: a sliding map with a cell-by-cell inverse.
        pair_rule(F) = (c, nbrs, ctx) -> begin
            next(l, m, r) = (F >> (4l + 2m + r)) & 1
            (a=next(nbrs[1].a, c.a, c.b), b=next(c.a, c.b, nbrs[2].b))
        end
        pairs = CAModel(LocalRule(pair_rule(110), Offsets((-1,), (1,))); name=:pairs,
                        states=[StateVariable(:a, 0; domain=(0, 1)),
                                StateVariable(:b, 0; domain=(0, 1))])
        up = SlidingBlockMap(rule(110), pairs, (c, nbrs) -> (a=c, b=nbrs[1]), right)
        down = ModelMap(pairs, rule(110), c -> c.a)
        @test is_model_map(up; dims=1)
        prob = CAProblem(rule(110), (; x=bits(48)), 30; space=Torus(48), seed=4)
        @test is_model_map(up, prob)
        # forgetting is not a map on every pair, as a cell's pair can disagree with its neighbour's,
        # only on the states that come from the original
        @test !is_model_map(down; dims=1)
        @test is_model_map(down, pushforward(up, prob))
        back = compose(up, down)
        @test same_action(back, SlidingBlockMap(rule(110), rule(110), (c, _) -> c, right),
                          prob.u0, prob.space)
        @test is_model_map(back; dims=1)

        @test_throws DomainMismatchError compose(φ, kink(126, 18))
        @test_throws DomainMismatchError compose(swap, kink(126, 18))
        @test_throws DomainMismatchError compose(kink(126, 18), swap)
        moore = SlidingBlockMap(rule(90), rule(90), (c, n) -> c, Moore(1))
        @test_throws "needs each window as `Offsets`" compose(moore, φ)
        @test_throws "needs each window as `Offsets`" compose(φ, moore)
        # with a ModelMap no sum of windows is needed
        @test compose(i90, moore).window === moore.window
    end

    @testset "maps of spaces" begin
        cover = covering(Torus(40), Torus(20), Offsets((-1,), (1,)))
        f = kink(126, 18)
        base = CAProblem(rule(126), (; x=bits(20)), 30; space=Torus(20), seed=9)
        up = pullback(cover, base; space=Torus(40))
        @test is_model_map(f, up)
        # the square: pushing the pulled-back problem forward is pulling the pushed-forward one back
        one_way = solve(pushforward(f, up))
        other_way = solve(pullback(cover, pushforward(f, base); space=Torus(40)))
        @test one_way.u == other_way.u
    end

    @testset "what the problem keeps" begin
        mask = rand(rng, Bool, 20)
        prob = CAProblem(rule(90), (; x=bits(20)), 10; space=Torus(20), seed=11, mask)
        new = pushforward(kink(90, 90), prob)
        @test new.mask == prob.mask
        @test new.seed == prob.seed
        @test new.tspan == prob.tspan
        @test new.space == prob.space
    end

    @testset "a quotient whose section reads neighbours" begin
        # pairs of neighbouring cells, forgetting the second: the section rebuilds it from the next
        # cell, and the quotient's rule is rule 110 again, on every configuration
        step110(l, m, r) = (110 >> (4l + 2m + r)) & 1
        pair_states = [StateVariable(:a, 0; domain=(0, 1)),
                       StateVariable(:b, 0; domain=(0, 1))]
        pairs = CAModel(LocalRule((c, nbrs, ctx) -> (a=step110(nbrs[1].a, c.a, c.b),
                                                     b=step110(c.a, c.b, nbrs[2].b)),
                                  Offsets((-1,), (1,))); name=:pairs, states=pair_states)
        q = quotient(pairs, c -> c.a, (a, nbrs) -> (a=a, b=nbrs[1]), Offsets((1,));
                     states=bit(), dims=1)
        @test q isa SlidingBlockMap
        @test q.window === nothing
        @test q.parameters === identity
        @test sprint(show, q.codom.rule) == "sliding quotient of $(pairs.rule)"
        rebuilt = q.codom
        same_rule = SlidingBlockMap(rebuilt, rule(110), (c, _) -> c, nothing)
        @test is_model_map(same_rule; dims=1)
        # A map from states that agree with the section, and not from others. Not on every pair.
        u = bits(32)
        agree = (a=u, b=circshift(u, -1))
        good = CAProblem(pairs, agree, 25; space=Torus(32), seed=1)
        @test is_model_map(q, good)
        @test !is_model_map(q; dims=1)
        disagree = (a=u, b=1 .- circshift(u, -1))
        @test !is_model_map(q, CAProblem(pairs, disagree, 25; space=Torus(32), seed=1))
        # lifting a mapped state returns a state that agrees
        down = pushforward(q, agree, Torus(32))
        @test down == u
        @test CategoricalCellularAutomata._lift_state(q, down, Torus(32)) == agree

        # Stochastic: the rule's own random numbers, since `h` reads one cell. A layer that holds
        # what the neighbours say at the last step would change, so this one is static.
        inside(c, nbrs) = c.here ? count(n -> n.here, nbrs) : 0
        cell_states = [StateVariable(:x, 0; domain=(0, 1)),
                       StateVariable(:here, false; domain=(false, true)),
                       StateVariable(:degree, 0; domain=0:4)]
        grown = CAModel(LocalRule((c, nbrs, ctx) -> begin
                                      c.here || return c
                                      live = sum(n -> n.x, nbrs)
                                      x = uniform(ctx, 1) < (live + c.x) / (c.degree + 1) ?
                                          1 : 0
                                      return (; c..., x)
                                  end, VonNeumann(1)); name=:grown, states=cell_states)
        forget = forget_layers(grown, :degree;
                               rebuild=(c, nbrs) -> (; degree=inside(c, nbrs)),
                               window=VonNeumann(1))
        @test forget isa SlidingBlockMap
        @test Tuple(s.name for s in forget.codom.states) == (:x, :here)
        m = 9
        here = fill(true, m, m)
        grid = Grid(m, m)
        degree = [count(o -> checkbounds(Bool, here, i + o[1], j + o[2]),
                        ((-1, 0), (1, 0), (0, -1), (0, 1)))
                  for i in 1:m, j in 1:m]
        u0 = (x=rand(rng, 0:1, m, m), here, degree)
        run = CAProblem(grown, u0, 30; space=grid, seed=8)
        @test is_model_map(forget, run)
        @test is_model_map(forget, remake(run; seed=9))
        # the layer feeds back: without the rebuild, or with a wrong count, the map fails
        @test !is_model_map(forget_layers(grown, :degree), run)
        wrong = (x=u0.x, here, degree=fill(4, m, m))
        @test !is_model_map(forget, CAProblem(grown, wrong, 30; space=grid, seed=8))

        # a callback that reads the layer moves with it, in either form
        edge_cull = PeriodicCallback(3) do integ
            integ.u.x .*= integ.u.degree .== 4
            u_modified!(integ, true)
        end
        with_cull = CAProblem(grown, u0, 30; space=grid, seed=8, callback=edge_cull)
        @test solve(with_cull).u[end] != solve(run).u[end]
        @test is_model_map(forget, with_cull; callback=:lift)
        @test is_model_map(forget, with_cull; callback=:lift_step)
        @test solve(pushforward(forget, with_cull; callback=:lift)).u ==
              solve(pushforward(forget, with_cull; callback=:lift_step)).u
        # without the rebuild the callback sees the default, and it shows
        @test !is_model_map(forget_layers(grown, :degree), with_cull; callback=:lift)

        # a map with a window and a section lifts as well
        up = SlidingBlockMap(rule(110), pairs, (c, nbrs) -> (a=c, b=nbrs[1]), right;
                             parameters=identity, section=(c, _) -> c.a,
                             section_window=right)
        cull = PeriodicCallback(integ -> nothing, 2)
        lifted = CAProblem(rule(110), (; x=bits(24)), 8; space=Torus(24), callback=cull)
        @test is_model_map(up, lifted; callback=:lift)
        @test is_model_map(up, lifted; callback=:lift_step)

        @test_throws "`rebuild` and `window` go together" forget_layers(grown, :degree;
                                                                        window=VonNeumann(1))
        @test_throws "`rebuild` and `window` go together" forget_layers(grown, :degree;
                                                                        rebuild=inside)
        @test_throws "`section` and `section_window` go together" SlidingBlockMap(pairs,
                                                                                  pairs,
                                                                                  (c, n) -> c,
                                                                                  nothing;
                                                                                  section=(c, n) -> c)
        blocks = CAModel(BlockRule((block, ctx) -> block); name=:blocks, states=bit())
        @test_throws "event or block rule" quotient(blocks, identity, (c, n) -> c, right;
                                                    states=bit(), dims=1)
        kernel = CAModel(LocalRule((c, nbrs, ctx) -> c, right); name=:kernel, states=bit(),
                         fields=(;
                                 dust=KernelField(GaussianKernel(1.0; radius=2),
                                                  c -> Float64(c))))
        @test_throws "kernel fields" quotient(kernel, identity, (c, n) -> c, right;
                                              states=bit(),
                                              dims=1)
        @test_throws "needs a lattice" quotient(rule(90), identity, (c, n) -> c, right;
                                                states=bit(), space=GraphSpace(3, [(1, 2)]))
    end

    @testset "callbacks and refusals" begin
        f = kink(126, 18)
        prob = CAProblem(rule(126), (; x=bits(16)), 6; space=Torus(16),
                         callback=PeriodicCallback(integ -> nothing, 2))
        @test_throws "has a callback" pushforward(f, prob)
        @test_throws "has a callback" is_model_map(f, prob)
        @test_throws "no section" pushforward(f, prob; callback=:lift)
        @test_throws "no section" pushforward(f, prob; callback=:lift_step)
        @test_throws "no section" is_model_map(f, prob; callback=:lift_step)
        @test is_model_map(f, prob; callback=nothing)
        @test is_model_map(f, prob; callback=PeriodicCallback(integ -> nothing, 2))
        @test !haskey(pushforward(f, prob; callback=nothing).kwargs, :callback)
        # a callback that really acts on one side only
        act = PeriodicCallback(integ -> (integ.u.=0; u_modified!(integ, true)), 3)
        plain = CAProblem(rule(126), (; x=bits(16)), 9; space=Torus(16), callback=act)
        @test !is_model_map(f, plain; callback=nothing)

        other = CAProblem(rule(30), (; x=bits(16)), 3; space=Torus(16))
        @test_throws DomainMismatchError pushforward(f, other)
        narrow = CAModel(Wolfram(18); name=:narrow,
                         states=[StateVariable(:x, 0; domain=(0,))])
        alternating = CAProblem(rule(126), (; x=[0, 1, 0, 1]), 2; space=Torus(4))
        @test_throws CellularAutomataCore.InvalidStateError pushforward(SlidingBlockMap(rule(126),
                                                                                        narrow,
                                                                                        kink_code,
                                                                                        right),
                                                                        alternating)
        wide_rule = CAModel(LocalRule((c, nbrs, ctx) -> c, Moore(3)); name=:wide,
                            states=bit())
        unchanged = SlidingBlockMap(wide_rule, wide_rule, (c, n) -> c, Moore(3))
        @test_throws "PATTERN_LIMIT" is_model_map(unchanged)
        @test is_model_map(unchanged; samples=30, contexts=2)
        needs_covariate = CAModel(LocalRule((c, nbrs, ctx) -> c, Offsets((1,))); name=:cov,
                                  states=bit(), covariates=[:rain])
        @test_throws "check it by running" is_model_map(SlidingBlockMap(needs_covariate,
                                                                        rule(90), kink_code,
                                                                        right); dims=1)
        blocks = CAModel(BlockRule((block, ctx) -> block); name=:blocks, states=bit())
        @test_throws "check it by running" is_model_map(SlidingBlockMap(blocks, blocks,
                                                                        kink_code, right);
                                                        dims=1)
        unnamed = CAModel(LocalRule((c, nbrs, ctx) -> c, nothing); name=:unnamed,
                          states=bit())
        @test_throws "must name its neighbourhood" is_model_map(SlidingBlockMap(unnamed,
                                                                                unnamed,
                                                                                kink_code,
                                                                                right);
                                                                dims=1)
        unbounded = CAModel(Wolfram(90); name=:free, states=[StateVariable(:x, 0)])
        @test_throws "has no domain" is_model_map(SlidingBlockMap(unbounded, unbounded,
                                                                  kink_code,
                                                                  right); dims=1)
        @test sprint(show, f) == "SlidingBlockMap(rule126 → rule18, window Offsets((1,),))"
    end
end
