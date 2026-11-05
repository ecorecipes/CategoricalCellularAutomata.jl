# Maps between models. A map from a CellularAutomataCore model M to a model N is a map `h` of cell
# states (applied cell by cell) with a map of parameters, such that one step of N from `h` of a
# state is `h` of one step of M: `h(F_M(c, nbrs, ctx)) == F_N(h(c), h.(nbrs), ctx')`, where `ctx'`
# has the mapped parameters and the same cell, time and seed. Such a map sends runs of M to runs of
# N, step by step, and for stochastic models pathwise: both models draw the same counter-based
# random numbers. Models and these maps form a category; pulling back along a map of spaces is a
# functor on it, so maps of models and maps of spaces commute.

"""
    ModelMap(dom, codom, h; parameters=nothing, section=nothing)

A map from the CellularAutomataCore `CAModel` `dom` to the model `codom`: `h`
sends a cell state of `dom` (a value, or a `NamedTuple` with one field per
state variable if `dom` has several) to a cell state of `codom`, and
`parameters` sends the parameters of a problem of `dom` to those of `codom`
(by default, each parameter of `codom` takes the value of the parameter of the
same name, or its default). `section`, if given, lifts a cell state of `codom` to
one of `dom` (`h(section(b)) == b`), which a callback needs in order to move with
the map (see [`pushforward`](@ref pushforward(::ModelMap, ::Any))). A research
extension, beyond the papers.

It is a map of models when it commutes with the rules: for every cell, its
neighbours and its `CellularAutomataCore.CellContext`, the next state of
`dom` mapped by `h` is the next state of `codom` from the mapped cell and
neighbours, with the mapped parameters and the same cell id, time and seed,
so the same random numbers ([`is_model_map`](@ref)). Then every run of `dom`
mapped by `h` is the run of `codom` from the mapped initial state
([`pushforward`](@ref pushforward(::ModelMap, ::Any))), exactly, for deterministic and stochastic models. Such
maps forget what does not feed back on the rest: a label carried along (which
introduction a case descends from, the colours of the immigration game), or a
layer that only records.

Models and the maps between them form a category
([`compose`](@ref compose(::ModelMap, ::ModelMap))).
"""
struct ModelMap{H,P,S}
    dom::CAC.CAModel
    codom::CAC.CAModel
    h::H
    parameters::P
    section::S
end
function ModelMap(dom::CAC.CAModel, codom::CAC.CAModel, h; parameters=nothing,
                  section=nothing)
    π = parameters === nothing ? _shared_parameters(codom) : parameters
    return ModelMap(dom, codom, h, π, section)
end

function Base.show(io::IO, f::ModelMap)
    return print(io, "ModelMap(", f.dom.name, " → ", f.codom.name, ")")
end

# The default map of parameters: each parameter of the codomain by name, or its default.
struct _SharedParameters
    names::Vector{Symbol}
    defaults::NamedTuple
end
function _shared_parameters(m::CAC.CAModel)
    return _SharedParameters([p.name for p in m.parameters],
                             CAC.defaults(m))
end
function (s::_SharedParameters)(p)
    isempty(s.names) && return CAC.NullParameters()
    given = p isa NamedTuple ? p : (;)
    return NamedTuple{Tuple(s.names)}(Tuple(get(given, n, getfield(s.defaults, n))
                                            for n in s.names))
end

# The cells of a state of `model` as an array of cell values, and back.
_names(m::CAC.CAModel) = Tuple(s.name for s in m.states)
function _cell_values(m::CAC.CAModel, u)
    length(m.states) == 1 && return u
    names = _names(m)
    return map((xs...) -> NamedTuple{names}(xs), (getfield(u, n) for n in names)...)
end
function _from_cell_values(m::CAC.CAModel, cells::AbstractArray)
    if length(m.states) == 1
        T = typeof(only(m.states).default)
        return convert(Array{T}, map(c -> convert(T, c), cells))
    end
    layers = map(m.states) do s
        T = typeof(s.default)
        return convert(Array{T}, map(c -> convert(T, getfield(c, s.name)), cells))
    end
    return NamedTuple{_names(m)}(Tuple(layers))
end

"""
    pushforward(f::ModelMap, u)
    pushforward(f::ModelMap, prob::CAProblem; callback, alg) -> CAProblem

The state `u` of a problem of `f`'s domain mapped by `f`, cell by cell: a
state of its codomain. The second form maps a problem of the domain (built
from it with `CAProblem(model, ...)`, possibly pulled back along maps of spaces
since) to the problem of the codomain on the same space, from the mapped
initial state, with the mapped parameters and the same seed, time span,
covariates, mask and solver keywords. When `f` is a map of models
([`is_model_map`](@ref)), the solution of the new problem is the original
solution mapped by `f`, state by state.

A callback stored with `prob` acts on the domain's whole state, and belongs to
the domain: a problem with one raises `ArgumentError` unless `callback` says
what the new problem has: its own callback, `nothing` for none, or `:lift`. With
`:lift` the original callback runs on the codomain, for a map with a `section`
and identity parameters (every [`quotient`](@ref) has both): after each step
the state is lifted, the callback acts on the lifted state, and the result is
mapped down. It sees `integ.u`, `t`, `p`, `alg`, `backend` and `retcode`, and
`integ.prob` is the original problem, whose seed the new one shares; it may
reassign `integ.p` and call `terminate!`, `u_modified!` and `add_tstop!`. What
`h` forgets is filled back in by the section each time, so a callback that
depends on it, or keeps something there for later, changes the run. A map of
models says nothing about callbacks, so check the pair by running both with
[`is_model_map`](@ref).

`:lift` maps down between the rule and the callback, so a layer that the rule
writes and the callback reads in the same step is gone before it is read.
`callback=:lift_step` treats the rule and the callback as one step, under the same
conditions on `f`: the state is lifted, the original problem takes a whole step
with the scheme `alg` (by default `Synchronous()`, and the only use of `alg`), and
the result is mapped down. So `f` may forget what lives only inside a step, and
when `:lift` gives a map the two give the same run. The new problem is solved
with `solve(new)`, on the default backend and scheme whatever the original uses,
since its rule and callback are the original's whole step and run on the
original's own backend. Callbacks given to it act between whole steps.

A problem whose rule is not the domain's raises [`DomainMismatchError`](@ref);
a mapped initial state outside a state variable's domain raises
`CellularAutomataCore.InvalidStateError`, and a missing covariate of the
codomain an `ArgumentError`.
"""
function pushforward(f::ModelMap, u)
    cells = _cell_values(f.dom, u)
    return _from_cell_values(f.codom, map(f.h, cells))
end

# The codomain's rule in place of the domain's, inside any pullbacks along maps of spaces.
function _retarget(rule, f::ModelMap)
    rule === f.dom.rule && return f.codom.rule
    rule isa _PulledBackRule &&
        return _PulledBackRule(_retarget(rule.rule, f), rule.map, rule.order)
    return throw(DomainMismatchError("pushing a problem forward along a map of models (the problem's rule)",
                                     f.dom.rule, rule))
end

# The state of the codomain from the domain's, checked against its state variables' domains.
function _mapped_initial_state(f::ModelMap, prob::CAC.CAProblem)
    u0 = pushforward(f, prob.u0)
    layers = length(f.codom.states) == 1 ? (u0,) : values(u0)
    for (s, a) in zip(f.codom.states, layers)
        s.domain === nothing && continue
        i = findfirst(x -> !(x in s.domain), a)
        i === nothing ||
            throw(CAC.InvalidStateError("model $(f.codom.name)", i, a[i],
                                        "state $(s.name) must lie in $(s.domain)"))
    end
    return u0
end

function pushforward(f::ModelMap, prob::CAC.CAProblem; callback=_UNSET, alg=nothing)
    callback === :lift_step &&
        return _whole_step_problem(f, prob, alg === nothing ? CAC.Synchronous() : alg)
    alg === nothing ||
        throw(ArgumentError("pushforward uses `alg` only with `callback=:lift_step`; otherwise give the scheme to `solve`"))
    callback === :lift && (callback = _lift_callback(f, prob))
    keywords = _moved_keywords(prob, callback,
                               "pushing a problem forward along a map of models")
    rule = _retarget(prob.rule, f)
    u0 = _mapped_initial_state(f, prob)
    for c in f.codom.covariates
        haskey(prob.covariates, c) ||
            throw(ArgumentError("model $(f.codom.name) needs covariate $c, which the problem does not have"))
    end
    user = Base.structdiff(prob.field_specs, merge(CAC.fields(prob.rule), f.dom.fields))
    f.section === nothing || (user = map(k -> _lift_field(k, f.section), user))
    return CAC.CAProblem(rule, u0, prob.tspan, f.parameters(prob.p); space=prob.space,
                         seed=prob.seed, covariates=prob.covariates,
                         fields=merge(f.codom.fields, user), mask=prob.mask, keywords...)
end

# The cell values of a model with a finite domain for every state variable.
function _domain_values(m::CAC.CAModel)
    for s in m.states
        s.domain === nothing &&
            throw(ArgumentError("state $(s.name) of model $(m.name) has no domain; give the cell values to check with `cells`"))
    end
    length(m.states) == 1 && return collect(only(m.states).domain)
    names = _names(m)
    return vec([NamedTuple{names}(Tuple(c))
                for c in Iterators.product((s.domain for s in m.states)...)])
end

# The numbers of neighbours a model's cells have on `space`.
function _neighbour_counts(m::CAC.CAModel, space, dims)
    n = CAC.neighbourhood(m.rule)
    n === nothing &&
        throw(ArgumentError("the rule of $(m.name) must name its neighbourhood to be checked"))
    if n isa CAC.GraphNeighbours
        space isa CAC.GraphSpace ||
            throw(ArgumentError("model $(m.name) reads a graph; give the GraphSpace with `space`"))
        return sort(unique(length.(space.neighbours)))
    end
    lattice = space === nothing ? CAC.Torus(ntuple(_ -> 201, dims)...) : _large(space)
    return [length(CAC.neighbourhood_offsets(n, lattice))]
end

"""
    is_model_map(f::ModelMap; cells=nothing, p=nothing, contexts=8, samples=nothing,
                 space=nothing, dims=2) -> Bool
    is_model_map(f::ModelMap, prob::CAProblem; alg=Synchronous(), callback, kwargs...) -> Bool

Whether `f` commutes with the rules of its domain and codomain: for every cell
state and every list of neighbour states drawn from `cells` (by default every
combination of the values in the domains of `f.dom`'s state variables), and
for `contexts` cell contexts (cell ids, times and seeds `1:contexts`, with the
domain's parameters `p`, by default its defaults, and the codomain's
`f.parameters(p)`), the domain's next state mapped by `f` equals the
codomain's next state from the mapped cell and neighbours. This is a check of
every local configuration, so for a deterministic rule that does not read the
cell context a `true` proves that `f` is a map of models; for a stochastic
rule it checks the random numbers on those contexts.

The number of neighbours comes from the domain's neighbourhood on a square
lattice of `dims` dimensions, or on `space` (a `GraphSpace` for a model that
reads a graph: every degree that occurs is checked). For a block rule the local
configurations are the blocks, and the new blocks are compared. The number of local
configurations checked must stay below `PATTERN_LIMIT`, or `ArgumentError` is
raised; with `samples` set, that many configurations are drawn at random from
`cells` for each context instead, which can find a failure but proves nothing.

This form sees only the rules, not what a problem adds to them. The second form
checks one problem by running it: it solves `prob` and
[`pushforward(f, prob; callback)`](@ref pushforward(::ModelMap, ::Any)) with the
scheme `alg` (and `kwargs`, such as `saveat`), and compares every saved state,
exactly. It is the check for models that read covariates or kernel fields,
which the first form refuses, and for callbacks; a block rule needs
`alg=Margolus()`. `callback` is
as for `pushforward`, so `callback=:lift` checks a quotient with the original's
callback and `callback=:lift_step` one that treats the rule and the callback as
one step. A `false` disproves the map; a `true` holds for that problem and span
only, since a run may not reach what would tell them apart.
"""
function is_model_map(f::ModelMap; cells=nothing, p=nothing, contexts::Integer=8,
                      samples::Union{Nothing,Integer}=nothing, space=nothing,
                      dims::Integer=2)
    for m in (f.dom, f.codom)
        isempty(m.covariates) && isempty(m.fields) ||
            throw(ArgumentError("model $(m.name) reads covariates or kernel fields; check it by running a problem: is_model_map(f, prob)"))
        m.rule isa CAC.EventRule &&
            throw(ArgumentError("model $(m.name) has an event rule; check it by running a problem: is_model_map(f, prob)"))
    end
    blocks = f.dom.rule isa CAC.BlockRule
    blocks == (f.codom.rule isa CAC.BlockRule) ||
        throw(ArgumentError("$f maps between a block rule and a rule stepped cell by cell, which no local configuration can compare"))
    vals = cells === nothing ? _domain_values(f.dom) : collect(cells)
    # a block rule's local configuration is its block: read as a cell and three "neighbours"
    ks = blocks ? [3] : _neighbour_counts(f.dom, space, dims)
    if samples === nothing
        total = sum(k -> big(length(vals))^(k + 1), ks) * contexts
        total <= PATTERN_LIMIT ||
            throw(ArgumentError("checking $f needs $total local configurations, more than PATTERN_LIMIT = $PATTERN_LIMIT; give `samples` to sample them"))
    end
    pdom = p === nothing ?
           (isempty(f.dom.parameters) ? CAC.NullParameters() :
            CAC.defaults(f.dom)) : p
    pcod = f.parameters(pdom)
    for i in 1:contexts, k in ks
        cdom = CAC.CellContext(pdom, CartesianIndex(1, 1), i, i, UInt64(i))
        ccod = CAC.CellContext(pcod, CartesianIndex(1, 1), i, i, UInt64(i))
        patterns = samples === nothing ?
                   Iterators.product(ntuple(_ -> vals, k + 1)...) :
                   (_sampled_pattern(vals, k, i, s) for s in 1:samples)
        for pattern in patterns
            if blocks
                next = map(f.h, f.dom.rule.f(pattern, cdom))
                other = f.codom.rule.f(map(f.h, pattern), ccod)
            else
                cell, nbrs = first(pattern), Base.tail(pattern)
                next = f.h(CAC.local_rule(f.dom.rule, cell, nbrs, cdom))
                other = CAC.local_rule(f.codom.rule, f.h(cell), map(f.h, nbrs), ccod)
            end
            isequal(next, other) || return false
        end
    end
    return true
end

# A local configuration drawn from `vals` with the core's counter-based random numbers.
function _sampled_pattern(vals, k, i, s)
    ctx = CAC.CellContext(nothing, CartesianIndex(1, 1), s, i, UInt64(0x6d6f64656c))
    return ntuple(j -> vals[1 + floor(Int, CAC.uniform(ctx, j) * length(vals))], k + 1)
end

function is_model_map(f::ModelMap, prob::CAC.CAProblem; alg=CAC.Synchronous(),
                      callback=_UNSET, kwargs...)
    sol = CAC.solve(prob, alg; kwargs...)
    other = callback === :lift_step ?
            CAC.solve(pushforward(f, prob; callback, alg); kwargs...) :
            CAC.solve(pushforward(f, prob; callback), alg; kwargs...)
    return sol.t == other.t &&
           all(t -> isequal(pushforward(f, sol.u[t]), other.u[t]), eachindex(sol.u))
end

# What a callback of the domain sees when it runs on the codomain. It holds nothing that outlives
# one call, so one lifted callback can serve the threads of an ensemble.
mutable struct _LiftedIntegrator{O,U,Pr}
    const outer::O
    u::U
    t::Any
    p::Any
    const prob::Pr
end
function Base.getproperty(i::_LiftedIntegrator, name::Symbol)
    name in fieldnames(_LiftedIntegrator) && return getfield(i, name)
    return getproperty(getfield(i, :outer), name)
end
CAC.terminate!(i::_LiftedIntegrator, args...) = CAC.terminate!(i.outer, args...)
CAC.u_modified!(i::_LiftedIntegrator, modified::Bool) = nothing
CAC.SciMLBase.add_tstop!(i::_LiftedIntegrator, t) = CAC.SciMLBase.add_tstop!(i.outer, t)
CAC.SciMLBase.derivative_discontinuity!(::_LiftedIntegrator, ::Bool) = nothing

function _lift_state(f::ModelMap, u)
    return _from_cell_values(f.dom, map(f.section, _cell_values(f.codom, u)))
end
function _lifted(f::ModelMap, integ, prob)
    return _LiftedIntegrator(integ, _lift_state(f, integ.u), integ.t, integ.p, prob)
end
function _lower!(f::ModelMap, integ, lifted)
    integ.u = pushforward(f, lifted.u)
    integ.p = lifted.p
    return nothing
end

_lift_one(::ModelMap, ::Nothing, prob) = nothing
function _lift_one(f::ModelMap, cb::CAC.DiscreteCallback, prob)
    condition = (u, t, integ) -> cb.condition(_lift_state(f, u), t, _lifted(f, integ, prob))
    affect! = function (integ)
        lifted = _lifted(f, integ, prob)
        cb.affect!(lifted)
        _lower!(f, integ, lifted)
        return nothing
    end
    initialize = function (c, u, t, integ)
        lifted = _lifted(f, integ, prob)
        cb.initialize(cb, lifted.u, t, lifted)
        _lower!(f, integ, lifted)
        return nothing
    end
    finalize = function (c, u, t, integ)
        lifted = _lifted(f, integ, prob)
        cb.finalize(cb, lifted.u, t, lifted)
        return nothing
    end
    return CAC.DiscreteCallback(condition, affect!; initialize, finalize,
                                save_positions=cb.save_positions)
end
function _lift_one(f::ModelMap, cb::CAC.CallbackSet, prob)
    return CAC.CallbackSet((_lift_one(f, c, prob) for c in cb.discrete_callbacks)...)
end
function _lift_one(f::ModelMap, cb::Union{Tuple,AbstractVector}, prob)
    return map(c -> _lift_one(f, c, prob), cb)
end

function _check_liftable(f::ModelMap, how)
    f.section === nothing &&
        throw(ArgumentError("$f has no section to lift the state with; give one with `section=`, or use `quotient`"))
    f.parameters === identity ||
        throw(ArgumentError("$f maps parameters, and a lifted callback reads the domain's: `callback=$how` needs `parameters=identity`"))
    return nothing
end

function _lift_callback(f::ModelMap, prob::CAC.CAProblem)
    _check_liftable(f, ":lift")
    return _lift_one(f, get(prob.kwargs, :callback, nothing), prob)
end

# The rule of a problem moved with `callback=:lift_step`. It has no local form: one step of the
# new problem lifts the state, takes a whole step of the original problem with its own integrator,
# and maps the result down. That integrator belongs to one run (it lives in the backend's state,
# made by `init`), so callbacks keep what they keep from step to step, and ensembles can share the
# problem.
struct _WholeStepRule{F<:ModelMap,P<:CAC.CAProblem,A} <: CAC.AbstractRule
    map::F
    problem::P
    alg::A
end
Base.show(io::IO, r::_WholeStepRule) = print(io, "whole step of ", r.problem.rule)
CAC.neighbourhood(::_WholeStepRule) = nothing
function CAC.local_rule(::_WholeStepRule, cell, nbrs, ctx)
    return throw(ArgumentError("a problem moved with `callback=:lift_step` has no local rule: solve it with `solve(prob)`, on the default backend and scheme, and give the original's scheme to `pushforward` as `alg`"))
end

mutable struct _WholeStepState{U,I}
    u::U
    const inner::I
end

function CAC.allocate_state(::CAC.ArrayBackend, prob::CAC.CAProblem{<:_WholeStepRule},
                            ::CAC.Synchronous)
    r = prob.rule
    start = CAC.remake(r.problem; u0=_lift_state(r.map, prob.u0), tspan=prob.tspan,
                       p=prob.p, seed=prob.seed, covariates=prob.covariates,
                       mask=prob.mask)
    inner = CAC.init(start, r.alg; saveat=nothing, save_everystep=false, save_start=false,
                     save_end=false)
    return _WholeStepState(pushforward(r.map, inner.u), inner)
end

function CAC.advance!(::CAC.ArrayBackend, st::_WholeStepState, prob, ::CAC.Synchronous, p,
                      t)
    inner = st.inner
    inner.t = t
    inner.p = p
    inner.u = _lift_state(prob.rule.map, st.u)
    CAC.step!(inner)
    st.u = pushforward(prob.rule.map, inner.u)
    return nothing
end

CAC.current_state(::CAC.ArrayBackend, st::_WholeStepState) = st.u
function CAC.set_state!(::CAC.ArrayBackend, st::_WholeStepState, u)
    st.u = u isa NamedTuple ? map(copy, u) : copy(u)
    return nothing
end
function CAC._restart!(st::_WholeStepState, prob, p, t0)
    CAC.reinit!(st.inner, _lift_state(prob.rule.map, st.u); t0)
    st.u = pushforward(prob.rule.map, st.inner.u)
    return nothing
end

# What the original's callbacks do to the run beyond the state: reassign the parameters, stop it,
# and finish.
function _whole_step_callback()
    affect! = function (integ)
        inner = integ.state.inner
        integ.p = inner.p
        inner.retcode == CAC.ReturnCode.Terminated && CAC.terminate!(integ)
        CAC.u_modified!(integ, false)
        return nothing
    end
    finalize = function (c, u, t, integ)
        inner = integ.state.inner
        foreach(cb -> cb.finalize(cb, inner.u, inner.t, inner), inner.callbacks)
        return nothing
    end
    return CAC.DiscreteCallback((u, t, integ) -> true, affect!; finalize,
                                save_positions=(false, false))
end

function _whole_step_problem(f::ModelMap, prob::CAC.CAProblem, alg)
    _check_liftable(f, ":lift_step")
    alg isa CAC.Gillespie &&
        throw(ArgumentError("`callback=:lift_step` needs a scheme with whole steps, not $alg"))
    _retarget(prob.rule, f)
    u0 = _mapped_initial_state(f, prob)
    keywords = Base.structdiff(prob.kwargs, (; callback=nothing, backend=nothing))
    return CAC.CAProblem(_WholeStepRule(f, prob, alg), u0, prob.tspan, prob.p;
                         space=prob.space, seed=prob.seed, covariates=prob.covariates,
                         mask=prob.mask, callback=_whole_step_callback(), keywords...)
end

# A kernel field's source reads a cell state of the domain, so it reads the lift of the codomain's.
function _lift_field(f::CAC.KernelField, section)
    return CAC.KernelField(f.kernel, f.source ∘ section, f.include_centre, f.method,
                           f.precision)
end
_lift_field(f, section) = f

# The rule of a quotient: lift the cell and its neighbours, step, and map the result down.
struct _QuotientRule{R<:CAC.AbstractRule,H,S} <: CAC.AbstractRule
    rule::R
    h::H
    section::S
end
@inline function CAC.local_rule(r::_QuotientRule, cell, nbrs, ctx)
    return r.h(CAC.local_rule(r.rule, r.section(cell), map(r.section, nbrs), ctx))
end
CAC.neighbourhood(r::_QuotientRule) = CAC.neighbourhood(r.rule)
CAC.fields(r::_QuotientRule) = map(f -> _lift_field(f, r.section), CAC.fields(r.rule))
Base.show(io::IO, r::_QuotientRule) = print(io, "quotient of ", r.rule)

# The same for a block rule: lift the block, apply the rule, and map the new block down.
struct _QuotientBlock{F,H,S}
    f::F
    h::H
    section::S
end
(b::_QuotientBlock)(block, ctx) = map(b.h, b.f(map(b.section, block), ctx))
Base.nameof(::_QuotientBlock) = :quotient

function _quotient_rule(r::CAC.BlockRule, h, section)
    return CAC.BlockRule(_QuotientBlock(r.f, h, section))
end
_quotient_rule(r::CAC.AbstractRule, h, section) = _QuotientRule(r, h, section)

"""
    quotient(model, h, section; states, name, description="") -> ModelMap

The map from `model` to its quotient by the map of cell states `h`, a new model
that needs no rule of its own: `section` lifts a cell state of the quotient to
one of `model` (`h(section(b)) == b`), and the quotient's rule lifts a cell and
its neighbours, applies `model`'s rule and maps the result down with `h`. It
has `states` (as for `CAModel`) and `model`'s parameters, covariates and kernel
fields, whose sources read the lifted cell states.

The new model is defined for any `h`, but the result is a map of models only if
the dynamics do not depend on the lift: [`is_model_map`](@ref) is the real test
of that, and fails when what `h` forgets feeds back. When it is one, this is the
only rule that `h` commutes with, whichever section is used, and every map of
models that does not distinguish what `h` forgets factors through it. A problem
with a callback moves with `callback=:lift`, or `callback=:lift_step` to treat the
rule and the callback as one step
([`pushforward`](@ref pushforward(::ModelMap, ::Any))). A block rule's quotient is
a block rule, lifting the block and mapping the new block down. Event rules, whose
rule gives rates rather than a next state, raise `ArgumentError`.
"""
function quotient(model::CAC.CAModel, h, section; states,
                  name::Symbol=Symbol(model.name, :_quotient),
                  description::AbstractString="quotient of $(model.name)")
    model.rule isa CAC.EventRule &&
        throw(ArgumentError("cannot take a quotient of $(model.name): an event rule gives rates, not a next state"))
    rule = _quotient_rule(model.rule, h, section)
    fields = map(f -> _lift_field(f, section), model.fields)
    q = CAC.CAModel(rule; name, states, parameters=model.parameters, fields,
                    covariates=model.covariates, description)
    return ModelMap(model, q, h, identity, section)
end

"""
    forget_layers(model, layers...; name) -> ModelMap

The [`quotient`](@ref) of `model` that forgets some of its state layers: the
cell states keep the other layers, and a cell is lifted by giving the forgotten
layers their defaults. It is a map of models when the forgotten layers do not
feed back on the ones kept ([`is_model_map`](@ref)): layers that only record,
such as the time at which a cell was reached, or labels the rule never reads.
Naming a layer the model does not have, or every layer, raises `ArgumentError`.
"""
function forget_layers(model::CAC.CAModel, layers::Symbol...;
                       name::Symbol=Symbol(model.name, :_without_, join(layers, :_)))
    names = _names(model)
    for l in layers
        l in names ||
            throw(ArgumentError("model $(model.name) has no state $l; states are $names"))
    end
    kept = Tuple(n for n in names if n ∉ layers)
    isempty(kept) &&
        throw(ArgumentError("forgetting $layers would leave $(model.name) no layers"))
    full = NamedTuple{names}(Tuple(s.default for s in model.states))
    h = length(kept) == 1 ? (c -> getfield(c, only(kept))) : (c -> NamedTuple{kept}(c))
    section = length(kept) == 1 ? (b -> merge(full, NamedTuple{kept}((b,)))) :
              (b -> merge(full, b))
    states = [s for s in model.states if s.name in kept]
    return quotient(model, h, section; states, name)
end

const _Model = CAC.CAModel

function _model_id(m::CAC.CAModel)
    return ModelMap(m, m, identity, identity, identity)
end

# f then g: states and parameters go through both maps.
function _model_compose(f::ModelMap, g::ModelMap)
    f.codom === g.dom ||
        throw(DomainMismatchError("composing maps of models", f.codom.name, g.dom.name))
    parameters = f.parameters === identity ? g.parameters :
                 g.parameters === identity ? f.parameters : g.parameters ∘ f.parameters
    section = f.section === nothing || g.section === nothing ? nothing :
              f.section ∘ g.section
    return ModelMap(f.dom, g.codom, g.h ∘ f.h, parameters, section)
end

@instance ThCategory{_Model,ModelMap} begin
    dom(f::ModelMap) = f.dom
    codom(f::ModelMap) = f.codom
    id(m::CAC.CAModel) = _model_id(m)
    compose(f::ModelMap, g::ModelMap) = _model_compose(f, g)
end

"""
    compose(f::ModelMap, g::ModelMap) -> ModelMap
    id(m::CAModel) -> ModelMap

CellularAutomataCore models and the maps between them form a category, an
instance of Catlab's `ThCategory`: `compose(f, g)` is `f` followed by `g`
(cell states and parameters go through both maps, and sections in reverse), raising
[`DomainMismatchError`](@ref) unless the codomain of `f` is the domain of `g`
(the same model object); `id(m)` is the identity of `m`. Composites of maps of
models are maps of models, and pushing a problem forward along
`compose(f, g)` is pushing it along `f`, then `g`.

Pulling back along a map of spaces ([`pullback`](@ref
pullback(::SpaceMorphism, ::CellularAutomataCore.CAProblem))) is a functor on
this category: pushing a pulled-back problem forward along a map of models
gives the pullback of the pushed-forward problem, with the same solutions.
"""
compose(::ModelMap, ::ModelMap)
