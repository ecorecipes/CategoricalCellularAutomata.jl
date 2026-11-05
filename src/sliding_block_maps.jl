# Maps between models that read neighbours. A `ModelMap` sends a cell's state to a cell state; a
# sliding block map reads the cell and a window around it, as a rule reads its neighbourhood, so it
# can see what lies between cells (a boundary between two species). It is a map of models when one
# step of the domain followed by the map is the map followed by one step of the codomain. Runs then
# map to runs exactly. A stochastic domain's next state at a cell depends on the random numbers of
# every cell in the window, so a codomain rule has to read those cells' numbers too.

"""
    SlidingBlockMap(dom, codom, h, window; parameters=nothing)

A map from the CellularAutomataCore `CAModel` `dom` to the model `codom` that
reads neighbours: the cell of `codom` at a position is `h(cell, nbrs)`, where
`cell` and `nbrs` are the cell of `dom` at that position and the cells in the
neighbourhood `window`, in that neighbourhood's order, read as a rule reads them,
edges included. `parameters` sends the parameters of a problem of `dom` to those
of `codom` (by default, by name). A research extension, beyond the papers.

It is a map of models when it commutes with the rules: one step of `dom` followed
by the map is the map followed by one step of `codom`, with the mapped parameters
and the same cell ids, times and seed ([`is_model_map`](@ref is_model_map(::SlidingBlockMap))).
Then every run of `dom` mapped by `h` is the run of `codom` from the mapped initial state
([`pushforward`](@ref pushforward(::SlidingBlockMap, ::Any, ::CellularAutomataCore.AbstractSpace))). On a lattice these are the
sliding block codes of symbolic dynamics, and with a [`ModelMap`](@ref), which is the case of an
empty window, they form a category ([`compose`](@ref compose(::SlidingBlockMap, ::SlidingBlockMap))).

Unlike a `ModelMap` it can see what lies between cells, such as the boundaries
between regions, but it has no [`quotient`](@ref): `codom` is written by hand and
then checked. A stochastic `dom` makes the next state at a cell depend on the
random numbers of every cell in the window, so the rule of `codom` must draw those too:
a `CellularAutomataCore.CellContext` with another cell's id gives its numbers.
"""
struct SlidingBlockMap{H,W,P}
    dom::CAC.CAModel
    codom::CAC.CAModel
    h::H
    window::W
    parameters::P
end
function SlidingBlockMap(dom::CAC.CAModel, codom::CAC.CAModel, h,
                         window::CAC.AbstractNeighbourhood; parameters=nothing)
    π = parameters === nothing ? _shared_parameters(codom) : parameters
    return SlidingBlockMap(dom, codom, h, window, π)
end

function Base.show(io::IO, f::SlidingBlockMap)
    return print(io, "SlidingBlockMap(", f.dom.name, " → ", f.codom.name, ", window ",
                 f.window, ")")
end

_window_of(f::SlidingBlockMap, space) = CAC._offsets_of(CAC._resolve(f.window, space))

"""
    pushforward(f::SlidingBlockMap, u, space)
    pushforward(f::SlidingBlockMap, prob::CAProblem; callback) -> CAProblem

The state `u` of a problem of `f`'s domain on `space` mapped by `f`: every cell
reads its window, edges as a rule reads them. The second form maps a problem of the
domain to the problem of the codomain on the same space, from the mapped initial state,
with the mapped parameters and the same seed, time span, covariates, mask and solver
keywords. It also accepts a problem pulled back along a map of spaces: the window is read
on the new space, so a map that reverses slots needs a window to match, and
[`is_model_map`](@ref is_model_map(::SlidingBlockMap)) will tell.

A problem with a callback raises `ArgumentError` unless `callback` gives the new problem's
own, or `nothing` for none: a sliding block map has no section, so a callback cannot move
with it (`:lift` and `:lift_step` are refused). A problem whose rule is not the domain's raises
[`DomainMismatchError`](@ref), a mapped initial state outside a state variable's
domain raises `CellularAutomataCore.InvalidStateError`, and a missing covariate of the
codomain an `ArgumentError`.
"""
function pushforward(f::SlidingBlockMap, u, space::CAC.AbstractSpace)
    offs = _window_of(f, space)
    cells = map(I -> f.h(CAC._read(u, I), CAC._neighbour_states(space, u, I, offs)),
                collect(CAC.cells(space)))
    return _from_cell_values(f.codom, cells)
end

function pushforward(f::SlidingBlockMap, prob::CAC.CAProblem; callback=_UNSET)
    (callback === :lift || callback === :lift_step) &&
        throw(ArgumentError("a sliding block map has no section, so a callback cannot move with it; give the new problem's with `callback=` (`nothing` for none)"))
    keywords = _moved_keywords(prob, callback,
                               "pushing a problem forward along a sliding block map")
    u0 = pushforward(f, prob.u0, prob.space)
    _check_state_domains(f.codom, u0)
    return _pushed_problem(f, prob, _retarget(prob.rule, f), u0, keywords, nothing)
end

# Where a cell of `space` reads: itself and its neighbours, without those off the edge.
function _reads(space::CAC.Lattice, offs, I)
    around = [I]
    for o in offs
        J, out = CAC._boundary_lookup(space, I + o)
        out == 0 && push!(around, J)
    end
    return unique(around)
end
_reads(space::CAC.GraphSpace, offs, i) = unique([i; space.neighbours[i]])

_halo_of(offs) = isempty(offs) ? 0 : maximum(o -> maximum(abs, Tuple(o)), offs)

# A torus large enough that what the square reads does not wrap round on itself.
function _checking_space(f::SlidingBlockMap, dims)
    probe = CAC.Torus(ntuple(_ -> 201, dims)...)
    reach = _halo_of(_window_of(f, probe)) +
            maximum(m -> _halo_of(_rule_offsets(m, probe)), (f.dom, f.codom))
    side = 4 * reach + 3
    return CAC.Torus(ntuple(_ -> side, dims)...)
end

function _rule_offsets(m::CAC.CAModel, space)
    n = CAC.neighbourhood(m.rule)
    n === nothing &&
        throw(ArgumentError("the rule of $(m.name) must name its neighbourhood to be checked"))
    return CAC._offsets_of(CAC._resolve(n, space))
end

"""
    is_model_map(f::SlidingBlockMap; cells=nothing, p=nothing, contexts=8, samples=nothing,
                 space=nothing, dims=2) -> Bool
    is_model_map(f::SlidingBlockMap, prob::CAProblem; alg=Synchronous(), callback, kwargs...) -> Bool

Whether `f` commutes with the rules of its domain and codomain. The first form tries every
assignment of the values `cells` (by default those in the domains of `f.dom`'s state variables) to
the cells that one step followed by the map, or the map followed by one step, reads around a
position, and compares the two. It does so at `contexts` positions, times and seeds, with the
domain's parameters `p` (by default its defaults) and the codomain's `f.parameters(p)`. For
a deterministic rule that does not read the cell context a `true` proves the map on a torus; for a
stochastic rule it checks the random numbers on those contexts.

The check runs on `space`, by default a torus of `dims` dimensions large enough that nothing
wraps round. A rule that reads another cell's random numbers works out that cell's id from the
size of its space, so it needs its own `space` here. The number of assignments must stay below
`PATTERN_LIMIT`, or `ArgumentError` is raised; with `samples` set, that many are drawn at random
for each context instead, which can find a failure but proves nothing. Models that read covariates
or kernel fields, and block and event rules, raise `ArgumentError`: check them by running.

The second form solves `prob` and `pushforward(f, prob; callback)` with the scheme
`alg` (and `kwargs`, such as `saveat`) and compares every saved state, exactly. A `false` disproves
the map; a `true` holds for that problem and span only.
"""
function is_model_map(f::SlidingBlockMap; cells=nothing, p=nothing, contexts::Integer=8,
                      samples::Union{Nothing,Integer}=nothing, space=nothing,
                      dims::Integer=2)
    for m in (f.dom, f.codom)
        isempty(m.covariates) && isempty(m.fields) ||
            throw(ArgumentError("model $(m.name) reads covariates or kernel fields; check it by running a problem: is_model_map(f, prob)"))
        m.rule isa Union{CAC.EventRule,CAC.BlockRule} &&
            throw(ArgumentError("model $(m.name) has an event or block rule; check it by running a problem: is_model_map(f, prob)"))
    end
    vals = cells === nothing ? _domain_values(f.dom) : collect(cells)
    lattice = space === nothing ? _checking_space(f, dims) : space
    window = _window_of(f, lattice)
    nf, ng = _rule_offsets(f.dom, lattice), _rule_offsets(f.codom, lattice)
    positions = collect(CAC.cells(lattice))
    ids = Dict(I => id for (id, I) in enumerate(positions))
    centres = [positions[mod1(div(length(positions), 2) + i, length(positions))]
               for i in 1:contexts]
    regions = map(centres) do C
        return unique(vcat((_reads(lattice, nf, J) for J in _reads(lattice, window, C))...,
                           (_reads(lattice, window, K) for K in _reads(lattice, ng, C))...))
    end
    if samples === nothing
        total = sum(r -> big(length(vals))^length(r), regions)
        total <= PATTERN_LIMIT ||
            throw(ArgumentError("checking $f needs $total local configurations, more than PATTERN_LIMIT = $PATTERN_LIMIT; give `samples` to sample them"))
    end
    pdom = p === nothing ?
           (isempty(f.dom.parameters) ? CAC.NullParameters() : CAC.defaults(f.dom)) : p
    pcod = f.parameters(pdom)
    shape = size(positions)
    # filled, though only what each step writes is read: a graph's reads look at the first cell's type
    x = fill!(Array{Any}(undef, shape), first(vals))
    next = copy(x)
    y = fill!(Array{Any}(undef, shape),
              f.h(x[first(positions)],
                  CAC._neighbour_states(lattice, x, first(positions), window)))
    for (i, C) in enumerate(centres)
        region = regions[i]
        moved = _reads(lattice, window, C)
        read_by_rule = _reads(lattice, ng, C)
        patterns = samples === nothing ?
                   Iterators.product(ntuple(_ -> vals, length(region))...) :
                   (_sampled_pattern(vals, length(region) - 1, i, s) for s in 1:samples)
        for pattern in patterns
            foreach((K, v) -> x[K] = v, region, pattern)
            for J in moved
                ctx = CAC.CellContext(pdom, J, i, ids[J], UInt64(i))
                next[J] = CAC.local_rule(f.dom.rule, x[J],
                                         CAC._neighbour_states(lattice, x, J, nf), ctx)
            end
            for K in read_by_rule
                y[K] = f.h(x[K], CAC._neighbour_states(lattice, x, K, window))
            end
            one_way = f.h(next[C], CAC._neighbour_states(lattice, next, C, window))
            ctx = CAC.CellContext(pcod, C, i, ids[C], UInt64(i))
            other = CAC.local_rule(f.codom.rule, y[C],
                                   CAC._neighbour_states(lattice, y, C, ng), ctx)
            isequal(one_way, other) || return false
        end
    end
    return true
end

function is_model_map(f::SlidingBlockMap, prob::CAC.CAProblem; alg=CAC.Synchronous(),
                      callback=_UNSET, kwargs...)
    sol = CAC.solve(prob, alg; kwargs...)
    other = CAC.solve(pushforward(f, prob; callback), alg; kwargs...)
    return sol.t == other.t &&
           all(t -> isequal(pushforward(f, sol.u[t], prob.space), other.u[t]),
               eachindex(sol.u))
end

# Reading a composite's window: each code `g` reads is `f`'s, centred at one of `g`'s positions.
struct _ComposedCode{F,G,C,N}
    f::F
    g::G
    at_centre::C
    at_neighbours::N
end
@inline _slot(cell, nbrs, k) = k == 0 ? cell : nbrs[k]
function _apply_at(code, (centre, around), cell, nbrs)
    return code.f(_slot(cell, nbrs, centre), map(k -> _slot(cell, nbrs, k), around))
end
function (c::_ComposedCode)(cell, nbrs)
    return c.g(_apply_at(c, c.at_centre, cell, nbrs),
               map(a -> _apply_at(c, a, cell, nbrs), c.at_neighbours))
end

function _offsets_for_composite(f::SlidingBlockMap)
    f.window isa CAC.Offsets ||
        throw(ArgumentError("composing sliding block maps needs each window as `Offsets`; `neighbourhood_offsets(window, space)` gives them, and $f has $(f.window)"))
    return f.window.offsets
end

function _check_composable(f, g)
    f.codom === g.dom ||
        throw(DomainMismatchError("composing maps of models", f.codom.name, g.dom.name))
    return nothing
end

function _composed_parameters(f, g)
    f.parameters === identity && return g.parameters
    g.parameters === identity && return f.parameters
    return g.parameters ∘ f.parameters
end

"""
    compose(f::SlidingBlockMap, g::SlidingBlockMap) -> SlidingBlockMap
    compose(f::ModelMap, g::SlidingBlockMap) -> SlidingBlockMap
    compose(f::SlidingBlockMap, g::ModelMap) -> SlidingBlockMap

`f` followed by `g`, as for [`ModelMap`](@ref)s, raising [`DomainMismatchError`](@ref) unless the
codomain of `f` is the domain of `g` (the same model object). The window of a composite of two
sliding block maps holds the sums of the two windows' offsets, so both must be `Offsets` (`neighbourhood_offsets` gives
them), or `ArgumentError` is raised. A `ModelMap` reads no neighbours, so composing with one keeps
the other's window, on any space. Composites of maps of models are maps of models.
"""
function compose(f::SlidingBlockMap, g::SlidingBlockMap)
    _check_composable(f, g)
    wf, wg = _offsets_for_composite(f), _offsets_for_composite(g)
    origin = zero(first(wf))
    sums = unique([a + b for a in (origin, wg...) for b in (origin, wf...)])
    window = CAC.Offsets(Tuple(filter(!=(origin), sums)))
    slot(o) = o == origin ? 0 : findfirst(==(o), window.offsets)
    read_at(a) = (slot(a), map(b -> slot(a + b), wf))
    code = _ComposedCode(f.h, g.h, read_at(origin), map(read_at, wg))
    return SlidingBlockMap(f.dom, g.codom, code, window, _composed_parameters(f, g))
end
function compose(f::ModelMap, g::SlidingBlockMap)
    _check_composable(f, g)
    return SlidingBlockMap(f.dom, g.codom, (c, nbrs) -> g.h(f.h(c), map(f.h, nbrs)),
                           g.window, _composed_parameters(f, g))
end
function compose(f::SlidingBlockMap, g::ModelMap)
    _check_composable(f, g)
    return SlidingBlockMap(f.dom, g.codom, (c, nbrs) -> g.h(f.h(c, nbrs)), f.window,
                           _composed_parameters(f, g))
end
dom(f::SlidingBlockMap) = f.dom
codom(f::SlidingBlockMap) = f.codom

"""
    CellularAutomaton(f::SlidingBlockMap, space; alphabet, codom=alphabet)

The sliding block map `f` as a cellular automaton between the full shifts on `alphabet` and
`codom`, over the group of the periodic lattice `space`: its memory set is the identity followed by
`f`'s window. So a map of models between deterministic models with finite states is a
square of [`CellularAutomaton`](@ref)s: `compose(φ, G) == compose(F, φ)`.
"""
function CellularAutomaton(f::SlidingBlockMap, space::CAC.Lattice{N};
                           alphabet::FinAlphabet, codom::FinAlphabet=alphabet) where {N}
    G = torus_group(space)
    els = [_element(G, o) for o in _window_of(f, space)]
    memory = unique([identity_element(G); els])
    pos = _positions(els, memory)
    T = eltype(codom)
    μ = y -> convert(T, f.h(y[1], Tuple(y[i] for i in pos)))
    return CellularAutomaton(G, memory, μ; dom=alphabet, codom)
end
