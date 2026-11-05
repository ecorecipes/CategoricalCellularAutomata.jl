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

    # a quotient needs no rule of its own: the traced model's rule, lifted and mapped down, runs
    # the plain SIR exactly, and forgetting a label that feeds back does not give a map
    q = quotient(traced, c -> c.state, s -> (state=s, lineage=0);
                 states=[StateVariable(:state, :S; domain=(:S, :I, :R))],
                 name=:QuotientSIR)
    @test codom(q).name == :QuotientSIR && dom(q) === traced && is_model_map(q)
    qsol = solve(pushforward(q, prob))
    @test qsol.u == solve(pushforward(untrace, prob)).u
    @test sprint(show, codom(q).rule) == "quotient of " * sprint(show, traced.rule)
    forgot = forget_layers(traced, :lineage)
    @test [s.name for s in CellularAutomataCore.states(codom(forgot))] == [:state]
    @test codom(forgot).name == :TracedSIR_without_lineage && is_model_map(forgot)
    @test is_model_map(forgot, prob)
    @test solve(pushforward(forgot, prob)).u == qsol.u
    @test !is_model_map(forget_layers(virulent, :lineage))
    @test !is_model_map(forget_layers(virulent, :lineage), vprob)
    # forgetting the state instead: the lineage reads it, so this is not a map
    @test !is_model_map(forget_layers(traced, :state))
    # several layers, keeping several: a record of the step each cell was reached
    records = @camodel Records begin
        @states state::Symbol = :S ∈ (:S, :I) load::Int = 0 reached::Int = -1 seen::Bool = false
        @neighbourhood VonNeumann(1)
        @rule begin
            cell.state == :I && return (; cell..., load=cell.load + 1)
            any(n -> n.state == :I, nbrs) || return cell
            return (; cell..., state=:I, reached=ctx.t, seen=true)
        end
    end
    rec = forget_layers(records, :reached, :seen)
    @test [s.name for s in CellularAutomataCore.states(codom(rec))] == [:state, :load]
    rprob = CAProblem(records, (; state=I -> I == CartesianIndex(3, 3) ? :I : :S), 8;
                      space=Torus(7, 7))
    @test is_model_map(rec, rprob)
    @test maximum(solve(rprob).u[end].reached) > 0
    @test keys(pushforward(rec, rprob).u0) == (:state, :load)

    # sampling local configurations: finds a failure among too many to enumerate, and agrees
    # with the exhaustive check where both can run
    many = (; cells=[(state=s, lineage=l) for s in (:S, :I, :R) for l in 0:3])
    @test is_model_map(untrace; many..., samples=2000)
    @test !is_model_map(vmap; many..., samples=2000)
    @test_throws ArgumentError is_model_map(untrace; contexts=10^4)
    @test is_model_map(untrace; contexts=10^4, samples=5)

    # a run check sees what a local check cannot: a callback that reads the forgotten label
    # acts on the whole state, so the rule alone commutes and the problem does not
    cull = DiscreteCallback((u, t, integ) -> t == 3,
                            function (integ)
                                integ.u.state[integ.u.lineage .== 3] .= :R
                                return nothing
                            end; save_positions=(false, false))
    culled = remake(prob; kwargs=(; callback=cull))
    @test_throws ArgumentError pushforward(untrace, culled)
    @test_throws ArgumentError is_model_map(untrace, culled)
    @test is_model_map(untrace) && !is_model_map(untrace, culled; callback=nothing)
    @test get(pushforward(untrace, culled; callback=nothing).kwargs, :callback, nothing) ===
          nothing
    # a callback that reads only what is kept can be given to the codomain too, and commutes
    clear(state) = (state.=map(s -> s == :I ? :R : s, state); nothing)
    all_of(u::NamedTuple) = u.state
    all_of(u::AbstractArray) = u
    stop = () -> DiscreteCallback((u, t, integ) -> t == 5,
                                  integ -> clear(all_of(integ.u));
                                  save_positions=(false, false))
    stopped = remake(prob; kwargs=(; callback=stop()))
    moved = pushforward(untrace, stopped; callback=stop())
    @test haskey(moved.kwargs, :callback)
    @test is_model_map(untrace, stopped; callback=stop())
    @test solve(stopped).u[end] != sol.u[end]
    # other solver keywords move with the problem, and the check passes them to both solves
    saved = remake(prob; kwargs=(; saveat=5))
    @test pushforward(untrace, saved).kwargs == (; saveat=5)
    @test is_model_map(untrace, saved)
    @test is_model_map(untrace, prob; saveat=10)
    # the callback is not moved by a map of spaces either: its action on the state need not
    # commute with the map, so the caller says what it is
    cprob = remake(small; kwargs=(; callback=stop()))
    @test_throws ArgumentError pullback(φ, cprob; space=Torus(15, 12))
    @test get(pullback(φ, cprob; space=Torus(15, 12), callback=nothing).kwargs, :callback,
              nothing) === nothing
    @test haskey(pullback(φ, cprob; space=Torus(15, 12), callback=stop()).kwargs, :callback)
    bigsol = solve(pullback(φ, cprob; space=Torus(15, 12), callback=stop()))
    smallsol = solve(cprob)
    @test all(t -> bigsol.u[t] == pullback(φ, smallsol.u[t]; space=Torus(15, 12)),
              eachindex(smallsol.u))

    # callbacks on a quotient: lifted, run on the original's state, and mapped down
    lifted_prob = remake(prob; kwargs=(; callback=stop()))
    plainq = forget_layers(traced, :lineage)
    @test is_model_map(plainq, lifted_prob; callback=:lift)
    # against the same action written by hand for the quotient's state
    byhand = solve(pushforward(plainq, lifted_prob; callback=stop()))
    @test solve(pushforward(plainq, lifted_prob; callback=:lift)).u == byhand.u
    @test byhand.u != solve(pushforward(plainq, prob)).u
    # a callback that reads what is forgotten: the section gives lineage 0, so it never fires
    @test !is_model_map(plainq, culled; callback=:lift)
    @test solve(pushforward(plainq, culled; callback=:lift)).u ==
          solve(pushforward(plainq, prob)).u
    # it sees the time, the seed of the original problem and its parameters, and may reassign them
    seen = Ref{Any}(nothing)
    spy = DiscreteCallback((u, t, integ) -> t == 2,
                           function (integ)
                               seen[] = (integ.t, integ.prob.seed, integ.p.β,
                                         keys(integ.u), integ.prob === lifted_spy[])
                               return nothing
                           end; save_positions=(false, false))
    lifted_spy = Ref{Any}(nothing)
    spied = remake(prob; kwargs=(; callback=spy))
    lifted_spy[] = spied
    solve(pushforward(plainq, spied; callback=:lift))
    @test seen[] == (2, spied.seed, spied.p.β, (:state, :lineage), true)
    # reassigning the parameters at a callback changes the run from then on, on both sides
    quiet = () -> DiscreteCallback((u, t, integ) -> t == 4,
                                   function (integ)
                                       integ.p = merge(integ.p, (; β=0.0))
                                       return nothing
                                   end; save_positions=(false, false))
    quieted = remake(prob; kwargs=(; callback=quiet()))
    @test is_model_map(plainq, quieted; callback=:lift)
    @test solve(quieted).u[end] != sol.u[end]
    # it may stop the run, and both sides stop at the same step
    halt = DiscreteCallback((u, t, integ) -> t == 6, integ -> terminate!(integ);
                            save_positions=(false, false))
    halted = remake(prob; kwargs=(; callback=halt))
    hq = solve(pushforward(plainq, halted; callback=:lift))
    @test hq.t[end] == 6 && is_model_map(plainq, halted; callback=:lift)
    # sets and collections of callbacks, and the core's periodic and preset ones
    sets = (CallbackSet(stop(), quiet()), (stop(), quiet()), [stop(), quiet()])
    for cb in sets
        @test is_model_map(plainq, remake(prob; kwargs=(; callback=cb)); callback=:lift)
    end
    bump! = integ -> (integ.u.state[1, 1]=:R; nothing)
    for cb in
        (PeriodicCallback(bump!, 5), PeriodicCallback(bump!, 5; initial_affect=true),
         PresetTimeCallback([2, 7], bump!))
        p2 = remake(prob; kwargs=(; callback=cb))
        @test is_model_map(plainq, p2; callback=:lift)
        @test solve(p2).u[end].state[1, 1] == :R
    end
    # a problem without a callback needs no lifting
    @test is_model_map(plainq, prob; callback=:lift)
    # a composite of quotients keeps a section; a hand-written codomain can give its own
    fine = quotient(traced, c -> (state=c.state, lineage=min(c.lineage, 2)),
                    b -> (state=b.state, lineage=b.lineage);
                    states=CellularAutomataCore.states(traced), name=:Merged)
    coarse = forget_layers(codom(fine), :lineage)
    chain = compose(fine, coarse)
    @test chain.parameters === identity && chain.section(:I) == (state=:I, lineage=0)
    @test is_model_map(chain, lifted_prob; callback=:lift)
    written = ModelMap(traced, sir, c -> c.state; parameters=identity,
                       section=s -> (state=s, lineage=0))
    @test is_model_map(written, lifted_prob; callback=:lift)
    # and a map that cannot lift says why
    @test_throws ArgumentError pushforward(untrace, lifted_prob; callback=:lift)
    nosection = ModelMap(traced, sir, c -> c.state; section=s -> (state=s, lineage=0))
    @test_throws ArgumentError pushforward(nosection, lifted_prob; callback=:lift)

    # kernel fields read the lift, so forgetting a layer the field reads gives a false answer
    # rather than a crash, and forgetting another layer leaves the field alone
    fielded = @camodel Fielded begin
        @states infected::Bool = false record::Int = 0
        @parameters β = 0.05
        @neighbourhood VonNeumann(1)
        @fields pressure = KernelField(GaussianKernel(1.5; radius=3),
                                       c -> Float64(c.infected))
        @rule begin
            i = cell.infected || bernoulli(ctx, min(1.0, β * field(ctx, :pressure)), 1)
            (infected=i, record=cell.record + i)
        end
    end
    fprob = CAProblem(fielded, (; infected=I -> I == CartesianIndex(6, 6)), 12;
                      space=Torus(12, 12), seed=2)
    @test count(solve(fprob).u[end].infected) > 1
    @test is_model_map(forget_layers(fielded, :record), fprob)
    @test !is_model_map(forget_layers(fielded, :infected), fprob)
    @test_throws ArgumentError is_model_map(forget_layers(fielded, :record))
    # a field given with the problem, not the model, is lifted in the same way
    extra = CAProblem(fielded, (; infected=I -> I == CartesianIndex(6, 6)), 12; seed=2,
                      space=Torus(12, 12),
                      fields=(;
                              more=KernelField(GaussianKernel(1.0; radius=2),
                                               c -> Float64(c.infected))))
    @test is_model_map(forget_layers(fielded, :record), extra)

    # block rules: particles of two colours, each block turning at random, against the same
    # particles written by hand without colours
    turn(b) = (b[3], b[1], b[4], b[2])  # a quarter turn of (top left, bottom left, ...)
    colours = CAModel(BlockRule((b, ctx) -> uniform(ctx, 1) < 0.5 ? turn(b) : b);
                      name=:Colours,
                      states=[StateVariable(:c, 0; domain=(0, 1, 2))])
    bare = CAModel(BlockRule((b, ctx) -> uniform(ctx, 1) < 0.5 ? turn(b) : b); name=:Bare,
                   states=[StateVariable(:c, 0; domain=(0, 1))])
    colourless = ModelMap(colours, bare, c -> Int(c != 0))
    @test is_model_map(colourless)
    cprob = CAProblem(colours, (; c=rand(rng, 0:2, 10, 8)), 30; space=Torus(10, 8), seed=4)
    @test is_model_map(colourless, cprob; alg=Margolus())
    @test solve(cprob, Margolus()).u[end] != cprob.u0
    # the run needs the scheme, and the core says so
    @test_throws ArgumentError is_model_map(colourless, cprob)
    # the quotient is a block rule, needs no rule of its own, and equals the one written by hand
    bq = quotient(colours, c -> Int(c != 0), b -> b; name=:BlockQuotient,
                  states=[StateVariable(:c, 0; domain=(0, 1))])
    @test codom(bq).rule isa BlockRule
    @test sprint(show, codom(bq).rule) == "BlockRule(quotient)"
    @test is_model_map(bq) && is_model_map(bq, cprob; alg=Margolus())
    @test solve(pushforward(bq, cprob), Margolus()).u ==
          solve(pushforward(colourless, cprob), Margolus()).u
    # colour 2 sticks, so forgetting colours is no longer a map: both checks see it
    sticky = CAModel(BlockRule((b, ctx) -> 2 in b ? b :
                                           (uniform(ctx, 1) < 0.5 ? turn(b) : b));
                     name=:Sticky, states=[StateVariable(:c, 0; domain=(0, 1, 2))])
    sq = quotient(sticky, c -> Int(c != 0), b -> b; name=:StickyQuotient,
                  states=[StateVariable(:c, 0; domain=(0, 1))])
    @test !is_model_map(sq)
    @test !is_model_map(sq,
                        CAProblem(sticky, (; c=rand(rng, 0:2, 10, 8)), 30;
                                  space=Torus(10, 8), seed=4); alg=Margolus())
    # layers: a record that does not feed back, with sampled blocks and a lifted callback
    layered = CAModel(BlockRule((b, ctx) -> uniform(ctx, 1) < 0.5 ? turn(b) : b);
                      name=:Layered,
                      states=[StateVariable(:x, 0; domain=(0, 1)),
                              StateVariable(:mark, 0; domain=0:2)])
    fl = forget_layers(layered, :mark)
    @test codom(fl).rule isa BlockRule && is_model_map(fl)
    @test is_model_map(fl; samples=200, contexts=4)
    lprob = CAProblem(layered, (x=rand(rng, 0:1, 8, 8), mark=rand(rng, 0:2, 8, 8)), 12;
                      space=Torus(8, 8), seed=6)
    @test is_model_map(fl, lprob; alg=Margolus())
    empty = () -> DiscreteCallback((u, t, integ) -> t == 5,
                                   integ -> (integ.u.x[1:2, :].=0; nothing);
                                   save_positions=(false, false))
    lcb = remake(lprob; kwargs=(; callback=empty()))
    @test is_model_map(fl, lcb; alg=Margolus(), callback=:lift)
    @test solve(lcb, Margolus()).u[end] != solve(lprob, Margolus()).u[end]
    # mixing a block rule with a rule stepped cell by cell has no local comparison
    @test_throws ArgumentError is_model_map(ModelMap(colours, life, c -> Int(c != 0)))
    # an event rule gives rates, not a next state
    events = CAModel(EventRule((c, nb, ctx) -> (1.0 => c,), VonNeumann(1)); name=:Events,
                     states=[StateVariable(:x, 0)])
    @test_throws ArgumentError quotient(events, identity, identity;
                                        states=[StateVariable(:x, 0)])
    @test_throws ArgumentError is_model_map(ModelMap(events, events, identity))

    # a rule and its callback as one step. `scratch` is written by the rule, read by the callback
    # in the same step, and overwritten by the next rule, so it lives only inside a step
    scratchy = @camodel Scratchy begin
        @states level::Int = 0 scratch::Int = 0
        @parameters gain = 1
        @neighbourhood VonNeumann(1)
        @rule begin
            n = sum(x -> x.level, nbrs)
            (level=cell.level, scratch=(cell.level + n + gain) % 5)
        end
    end
    settle = () -> DiscreteCallback((u, t, integ) -> true,
                                    function (integ)
                                        integ.u.level .= integ.u.scratch
                                        return nothing
                                    end; save_positions=(false, false))
    start = (level=rand(rng, 0:4, 12, 10), scratch=rand(rng, 0:4, 12, 10))
    sprob = CAProblem(scratchy, start, 20, (; gain=2); space=Torus(12, 10), seed=8,
                      callback=settle())
    noscratch = forget_layers(scratchy, :scratch)
    # the rule does not read it, so the rules commute, yet the separate quotient loses it
    @test is_model_map(noscratch; cells=[(level=l, scratch=s) for l in 0:1, s in 0:1],
                       p=(; gain=2))
    @test !is_model_map(noscratch, sprob; callback=:lift)
    @test is_model_map(noscratch, sprob; callback=:lift_step)
    whole = pushforward(noscratch, sprob; callback=:lift_step)
    @test occursin("whole step of", sprint(show, whole.rule))
    orig = solve(sprob)
    @test orig.u[end].level != start.level
    @test solve(whole).u == [u.level for u in orig.u]
    @test whole.u0 == start.level && !haskey(whole.kwargs, :backend)
    # the lift does not hide a dependence: the first step starts from the lift, not the original
    # state, and a value that stays between steps still breaks the map
    @test !is_model_map(forget_layers(scratchy, :level), sprob; callback=:lift_step)
    carried = @camodel Carried begin
        @states level::Int = 0 memory::Int = 0
        @neighbourhood VonNeumann(1)
        @rule (level=cell.level, memory=cell.memory)
    end
    fromlast = DiscreteCallback((u, t, integ) -> true,
                                function (integ)
                                    integ.u.level .= integ.u.memory
                                    return nothing
                                end; save_positions=(false, false))
    cprob2 = CAProblem(carried, (level=zeros(Int, 6, 6), memory=ones(Int, 6, 6)), 3;
                       space=Torus(6, 6), callback=fromlast)
    @test !is_model_map(forget_layers(carried, :memory), cprob2; callback=:lift_step)
    # with a map under `:lift` the whole step is the same run
    @test is_model_map(plainq, lifted_prob; callback=:lift_step)
    @test solve(pushforward(plainq, lifted_prob; callback=:lift_step)).u ==
          solve(pushforward(plainq, lifted_prob; callback=:lift)).u
    @test is_model_map(plainq, prob; callback=:lift_step)  # stochastic, no callback
    @test !is_model_map(plainq, culled; callback=:lift_step)
    # sets, periodic and preset callbacks, solver keywords stored and given
    for cb in
        (CallbackSet(stop(), quiet()), [stop(), quiet()], PeriodicCallback(bump!, 5),
         PeriodicCallback(bump!, 5; initial_affect=true),
         PresetTimeCallback([2, 7], bump!))
        @test is_model_map(plainq, remake(prob; kwargs=(; callback=cb));
                           callback=:lift_step)
    end
    @test is_model_map(noscratch, sprob; callback=:lift_step, saveat=5)
    @test solve(whole; saveat=5).t == 0:5:20
    stored = remake(sprob; kwargs=(; callback=settle(), saveat=4))
    @test solve(pushforward(noscratch, stored; callback=:lift_step)).t == 0:4:20
    # the callback sees the original state, time, seed and parameters; it may reassign and stop
    seen2 = Ref{Any}(nothing)
    spy2 = DiscreteCallback((u, t, integ) -> t == 2,
                            function (integ)
                                seen2[] = (integ.t, integ.prob.seed, integ.p.gain,
                                           keys(integ.u))
                                return nothing
                            end; save_positions=(false, false))
    solve(pushforward(noscratch, remake(sprob; kwargs=(; callback=spy2));
                      callback=:lift_step))
    @test seen2[] == (2, sprob.seed, 2, (:level, :scratch))
    regain = DiscreteCallback((u, t, integ) -> t == 4,
                              function (integ)
                                  integ.p = merge(integ.p, (; gain=4))
                                  return nothing
                              end; save_positions=(false, false))
    both = remake(sprob; kwargs=(; callback=CallbackSet(settle(), regain)))
    @test is_model_map(noscratch, both; callback=:lift_step)
    @test solve(both).u[end] != orig.u[end]
    halted2 = remake(sprob;
                     kwargs=(;
                             callback=CallbackSet(settle(),
                                                  DiscreteCallback((u, t, integ) -> t == 6,
                                                                   integ -> terminate!(integ);
                                                                   save_positions=(false,
                                                                                   false)))))
    hs = solve(pushforward(noscratch, halted2; callback=:lift_step))
    @test hs.t[end] == 6 && hs.retcode == solve(halted2).retcode
    @test is_model_map(noscratch, halted2; callback=:lift_step)
    # finalize runs once, and a callback given to the new problem acts between whole steps
    finished = Ref(0)
    closing = DiscreteCallback((u, t, integ) -> false, integ -> nothing;
                               finalize=(c, u, t, integ) -> (finished[] += 1; nothing),
                               save_positions=(false, false))
    solve(pushforward(noscratch, remake(sprob; kwargs=(; callback=closing));
                      callback=:lift_step))
    @test finished[] == 1
    outer = DiscreteCallback((u, t, integ) -> t == 3,
                             function (integ)
                                 integ.u .= 0
                                 return nothing
                             end; save_positions=(false, false))
    after = solve(whole; callback=outer)
    @test after.u[4] == zeros(Int, 12, 10) && after.u[5] != orig.u[5].level
    # a new start, a new seed and an ensemble each run their own whole steps, without sharing
    integ = init(whole)
    step!(integ, 7)
    reinit!(integ)
    @test solve!(integ).u == solve(whole).u
    noisy = @camodel Noisy begin
        @states level::Int = 0 scratch::Int = 0
        @neighbourhood VonNeumann(1)
        @rule (level=cell.level, scratch=uniform(ctx, 1) < 0.5 ? 1 : 0)
    end
    nprob = CAProblem(noisy, (level=zeros(Int, 8, 8), scratch=zeros(Int, 8, 8)), 6;
                      space=Torus(8, 8), seed=2, callback=settle())
    nf = forget_layers(noisy, :scratch)
    @test !is_model_map(nf, nprob; callback=:lift)
    @test is_model_map(nf, nprob; callback=:lift_step)
    nwhole = pushforward(nf, nprob; callback=:lift_step)
    @test solve(remake(nwhole; seed=3)).u ==
          [u.level for u in solve(remake(nprob; seed=3)).u]
    @test solve(remake(nwhole; seed=3)).u != solve(nwhole).u
    ens = solve(EnsembleProblem(nwhole), Synchronous(), EnsembleThreads(); trajectories=6)
    @test all(i -> ens.u[i].u == [u.level
                                  for u in solve(remake(nprob; seed=nprob.seed + i)).u],
              1:6)
    # another scheme or a stored backend for the original, and a problem moved along a map of spaces
    @test is_model_map(noscratch,
                       remake(sprob;
                              kwargs=(; callback=settle(),
                                      backend=ReferenceBackend()));
                       callback=:lift_step)
    moved_space = pullback(covering(Torus(24, 20), Torus(12, 10), VonNeumann(1)), sprob;
                           space=Torus(24, 20), callback=settle())
    @test is_model_map(noscratch, moved_space; callback=:lift_step)
    @test is_model_map(noscratch, sprob; alg=RandomSequential(), callback=:lift_step)
    # a block rule with a callback that reads what the block rule just wrote
    blocky = CAModel(BlockRule((b, ctx) -> map(c -> (x=c.x, mark=1 - c.x), b));
                     name=:Blocky,
                     states=[StateVariable(:x, 0; domain=(0, 1)),
                             StateVariable(:mark, 0; domain=(0, 1))])
    flip = DiscreteCallback((u, t, integ) -> true,
                            function (integ)
                                integ.u.x .= integ.u.mark
                                return nothing
                            end; save_positions=(false, false))
    bprob = CAProblem(blocky, (x=rand(rng, 0:1, 8, 8), mark=zeros(Int, 8, 8)), 5;
                      space=Torus(8, 8), callback=flip)
    fb = forget_layers(blocky, :mark)
    @test !is_model_map(fb, bprob; alg=Margolus(), callback=:lift)
    @test is_model_map(fb, bprob; alg=Margolus(), callback=:lift_step)
    # what it refuses, and why
    @test_throws ArgumentError pushforward(noscratch, sprob; alg=Synchronous())
    @test_throws ArgumentError pushforward(noscratch, sprob; callback=:lift, alg=Margolus())
    @test_throws ArgumentError pushforward(untrace, lifted_prob; callback=:lift_step)
    @test_throws ArgumentError pushforward(nosection, lifted_prob; callback=:lift_step)
    @test_throws ArgumentError pushforward(noscratch, sprob; callback=:lift_step,
                                           alg=Gillespie())
    @test_throws DomainMismatchError pushforward(noscratch, prob; callback=:lift_step)
    @test_throws ArgumentError solve(whole; backend=ReferenceBackend())
    @test_throws ArgumentError solve(whole, RandomSequential())
    @test_throws CellularAutomataCore.InvalidStateError pushforward(ModelMap(traced, sir,
                                                                             c -> :X;
                                                                             parameters=identity,
                                                                             section=s -> (state=s,
                                                                                           lineage=0)),
                                                                    prob;
                                                                    callback=:lift_step)

    # errors
    @test_throws ArgumentError forget_layers(traced, :nothing)
    @test_throws ArgumentError forget_layers(traced, :state, :lineage)
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
