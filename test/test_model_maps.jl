@testset "maps between models" begin
    rng = Xoshiro(17)
    # every saved state of `sol` mapped by `f` is the state of `other` at that time
    mapped_runs(f, sol, other) = length(sol.u) == length(other.u) &&
                                 all(t -> pushforward(f, sol.u[t]) == other.u[t],
                                     eachindex(sol.u))

    # Life, and the immigration game: live cells have one of two colours, and a birth takes
    # the colour most of its three live neighbours have. Forgetting colours gives Life.
    life = @camodel Life begin
        @states alive::Int = 0 ∈ (0, 1)
        @neighbourhood Moore(1)
        @rule begin
            n = sum(nbrs)
            cell == 1 ? Int(n == 2 || n == 3) : Int(n == 3)
        end
    end
    immigration = @camodel Immigration begin
        @states colour::Int = 0 ∈ (0, 1, 2)
        @neighbourhood Moore(1)
        @rule begin
            n = count(!=(0), nbrs)
            if cell != 0
                n == 2 || n == 3 ? cell : 0
            elseif n == 3
                count(==(1), nbrs) >= 2 ? 1 : 2
            else
                0
            end
        end
    end
    forget = ModelMap(immigration, life, c -> Int(c != 0))
    @test dom(forget) === immigration && codom(forget) === life
    @test is_model_map(forget; contexts=1)
    @test !is_model_map(ModelMap(immigration, life, c -> Int(c == 1)); contexts=1)
    prob = CAProblem(immigration, (; colour=rand(rng, 0:2, 24, 20)), 25;
                     space=Torus(24, 20))
    sol = solve(prob)
    pushed = pushforward(forget, prob)
    @test pushed.rule === life.rule && pushed.u0 == pushforward(forget, prob.u0)
    @test eltype(pushed.u0) == Int
    @test mapped_runs(forget, sol, solve(pushed))
    @test any(t -> sol.u[t] != sol.u[1], eachindex(sol.u))
    @test sprint(show, forget) == "ModelMap(Immigration → Life)"

    # A stochastic SIR model, and the same model tracing which introduction each case
    # descends from: a newly infected cell takes the label of an infected neighbour chosen
    # with its own draw number, so the infection itself draws exactly as in SIR.
    sir = @camodel SIR begin
        @states state::Symbol = :S ∈ (:S, :I, :R)
        @parameters β = 0.4 γ = 0.2
        @neighbourhood VonNeumann(1)
        @rule begin
            if cell == :S
                bernoulli(ctx, 1 - (1 - β)^count(==(:I), nbrs), 1) ? :I : :S
            elseif cell == :I
                bernoulli(ctx, γ, 2) ? :R : :I
            else
                cell
            end
        end
    end
    traced = @camodel TracedSIR begin
        @states state::Symbol = :S ∈ (:S, :I, :R) lineage::Int = 0 ∈ 0:3
        @parameters β = 0.4 γ = 0.2
        @neighbourhood VonNeumann(1)
        @rule begin
            if cell.state == :S
                k = count(n -> n.state == :I, nbrs)
                if bernoulli(ctx, 1 - (1 - β)^k, 1)
                    j = clamp(ceil(Int, uniform(ctx, 3) * k), 1, k)
                    source = nbrs[findall(n -> n.state == :I, collect(nbrs))[j]]
                    (state=:I, lineage=source.lineage)
                else
                    cell
                end
            elseif cell.state == :I
                bernoulli(ctx, γ, 2) ? (state=:R, lineage=cell.lineage) : cell
            else
                cell
            end
        end
    end
    untrace = ModelMap(traced, sir, c -> c.state)
    @test is_model_map(untrace)
    seeds = Dict(CartesianIndex(4, 4) => 1, CartesianIndex(15, 6) => 2,
                 CartesianIndex(9, 16) => 3)
    u0map = (; state=I -> haskey(seeds, I) ? :I : :S, lineage=I -> get(seeds, I, 0))
    prob = CAProblem(traced, u0map, 30, (; β=0.5); space=Torus(18, 18), seed=5)
    sol = solve(prob)
    pushed = pushforward(untrace, prob)
    @test pushed.p == (β=0.5, γ=0.2) && pushed.seed == prob.seed
    @test mapped_runs(untrace, sol, solve(pushed))
    @test count(==(:S), sol.u[end].state) < count(==(:S), sol.u[1].state)
    @test sort(unique(sol.u[end].lineage[sol.u[end].state .!= :S])) == [1, 2, 3]
    # the same as solving the plain model from the mapped initial state
    plain = solve(CAProblem(sir, (; state=pushforward(untrace, prob.u0)), 30, (; β=0.5);
                            space=Torus(18, 18), seed=5))
    @test mapped_runs(untrace, sol, plain)

    # a label that feeds back is not forgotten so simply: lineage 3 transmits more
    virulent = @camodel VirulentSIR begin
        @states state::Symbol = :S ∈ (:S, :I, :R) lineage::Int = 0 ∈ 0:3
        @parameters β = 0.4 γ = 0.2
        @neighbourhood VonNeumann(1)
        @rule begin
            if cell.state == :S
                escape = prod((n.state == :I ? (n.lineage == 3 ? 0.2 : 1 - β) : 1.0
                               for n in nbrs); init=1.0)
                bernoulli(ctx, 1 - escape, 1) ? (state=:I, lineage=1) : cell
            elseif cell.state == :I
                bernoulli(ctx, γ, 2) ? (state=:R, lineage=cell.lineage) : cell
            else
                cell
            end
        end
    end
    @test !is_model_map(ModelMap(virulent, sir, c -> c.state))
    vprob = CAProblem(virulent, u0map, 30; space=Torus(18, 18), seed=5)
    vmap = ModelMap(virulent, sir, c -> c.state)
    @test !mapped_runs(vmap, solve(vprob), solve(pushforward(vmap, vprob)))

    # the category: identities, composites, associativity, and Catlab's generic operations
    merge3 = ModelMap(traced, traced, c -> (state=c.state, lineage=min(c.lineage, 2)))
    @test is_model_map(merge3)
    both = compose(merge3, untrace)
    @test dom(both) === traced && codom(both) === sir && is_model_map(both)
    @test mapped_runs(both, sol, solve(pushforward(untrace, prob)))
    @test pushforward(both, prob).u0 == pushforward(untrace, pushforward(merge3, prob)).u0
    @test mapped_runs(merge3, sol, solve(pushforward(merge3, prob)))
    for u in sol.u
        @test pushforward(compose(id(traced), untrace), u) == pushforward(untrace, u)
        @test pushforward(compose(untrace, id(sir)), u) == pushforward(untrace, u)
        @test pushforward(compose(compose(merge3, merge3), untrace), u) ==
              pushforward(compose(merge3, compose(merge3, untrace)), u)
    end
    @test_throws DomainMismatchError compose(untrace, merge3)

    # a map of parameters: a composite of SIR and a box that counts days infected projects
    # onto SIR when the boxes share random numbers (otherwise SIR's box draws its own)
    counter = @camodel Counter begin
        @states state::Symbol = :S ∈ (:S, :I, :R) days::Int = 0
        @neighbourhood VonNeumann(1)
        @rule (state=cell.state, days=cell.days + (cell.state == :I))
    end
    d = @relation (state,) begin
        sir(state)
        counter(state)
    end
    boxes = (sir=OpenCAModel(sir),
             counter=OpenCAModel(counter; ports=[:state],
                                 reads=[:state]))
    names = [s.name for s in CellularAutomataCore.states(oapply(d, boxes))]
    cells = [NamedTuple{Tuple(names)}((s, n)) for s in (:S, :I, :R), n in 0:2]
    for shared in (true, false)
        comp = oapply(d, boxes; shared_randomness=shared, space=Torus(5, 5))
        proj = ModelMap(comp, sir, c -> c.state; parameters=p -> p.sir)
        @test is_model_map(proj; cells) == shared
        cprob = CAProblem(comp, (; state=u0map.state), 25,
                          (; sir=(β=0.6, γ=0.1), counter=(;)); space=Torus(18, 18), seed=3)
        csol = solve(cprob)
        @test pushforward(proj, cprob).p == (β=0.6, γ=0.1)
        @test mapped_runs(proj, csol, solve(pushforward(proj, cprob))) == shared
        shared && @test maximum(csol.u[end].counter_days) > 0
    end

    # maps of models and maps of spaces commute: pull back then push forward, or push
    # forward then pull back, give the same problem and the same run
    φ = covering(Torus(15, 12), Torus(5, 4), VonNeumann(1))
    small = CAProblem(traced,
                      (; state=I -> I == CartesianIndex(2, 2) ? :I : :S,
                       lineage=I -> Int(I == CartesianIndex(2, 2))), 20;
                      space=Torus(5, 4), seed=9)
    one = pushforward(untrace, pullback(φ, small; space=Torus(15, 12)))
    two = pullback(φ, pushforward(untrace, small); space=Torus(15, 12))
    @test one.u0 == two.u0 && one.p == two.p
    @test solve(one).u == solve(two).u
    big = solve(pullback(φ, small; space=Torus(15, 12)))
    @test mapped_runs(untrace, big, solve(one))

    # errors
    @test_throws DomainMismatchError pushforward(untrace,
                                                 CAProblem(sir, (;), 3;
                                                           space=Torus(4, 4)))
    bad = ModelMap(traced, sir, c -> :X)
    @test_throws CellularAutomataCore.InvalidStateError pushforward(bad, prob)
    @test_throws ArgumentError is_model_map(ModelMap(counter, sir, c -> c.state))
    @test_throws ArgumentError is_model_map(untrace; contexts=10^4)
    needs = CAModel(LocalRule((c, nb, ctx) -> c, VonNeumann(1)); name=:needs,
                    states=(; state=:S), covariates=(:heat,))
    @test_throws ArgumentError is_model_map(ModelMap(sir, needs, identity))
    @test_throws ArgumentError pushforward(ModelMap(sir, needs, identity),
                                           CAProblem(sir, (;), 3; space=Torus(4, 4)))
end
