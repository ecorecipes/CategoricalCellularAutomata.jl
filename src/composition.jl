# Composition of CellularAutomataCore models with undirected wiring diagrams. Each box is a CAModel
# exposing some of its state layers as ports; junctions identify layers across boxes. The composite is
# the pairing, in the product of all its layers, of each box's update restricted to the layers it owns,
# which is the product theorem of the categorical framework applied to whole models. Each layer has at
# most one owner; boxes read shared layers freely. Random numbers are drawn per box: each box's rule
# sees a seed derived from its name, unless `shared_randomness=true`.

"""
    OpenCAModel(model; ports=all states, reads=())

A CellularAutomataCore `CAModel` with some of its state layers exposed as
ports, in order, for composition with an undirected wiring diagram
([`oapply`](@ref)). Layers listed in `reads` are read but not updated by this
model: in a composite, its rule's result for them is ignored, and another box
may own them.
"""
struct OpenCAModel
    model::CAC.CAModel
    ports::Vector{Symbol}
    reads::Vector{Symbol}
    function OpenCAModel(model::CAC.CAModel; ports=[s.name for s in CAC.states(model)],
                         reads=Symbol[])
        names = [s.name for s in CAC.states(model)]
        for p in ports
            p in names ||
                throw(ArgumentError("model $(model.name) has no state $p; states are $names"))
        end
        allunique(ports) || throw(ArgumentError("ports must be distinct, got $ports"))
        for r in reads
            r in ports ||
                throw(ArgumentError("a read-only layer must be a port; $r is not one of $ports"))
        end
        return new(model, Symbol[ports...], Symbol[reads...])
    end
end

function Base.show(io::IO, m::OpenCAModel)
    print(io, "OpenCAModel ", m.model.name, " with ports (", join(m.ports, ", "), ")")
    isempty(m.reads) || print(io, ", reading (", join(m.reads, ", "), ")")
    return nothing
end

# One box of a composite, prepared for the composite rule.
struct _Box{R}
    name::Symbol
    rule::R
    layers::Vector{Symbol}        # the model's own state names
    targets::Vector{Symbol}       # the composite layer of each
    owned::Vector{Bool}           # whether the box updates that layer
    neighbours::Vector{Int}       # positions of the box's neighbours in the composite's
    single::Bool                  # a one-layer model has scalar cells
    seedmix::UInt64
end

# The composite local rule: each box sees its own view of the cell and its neighbours, its own
# parameters and its own random numbers, and writes the layers it owns.
struct _ComposedRule{B<:Tuple}
    boxes::B
end

# The core shows a rule by its function's name.
Base.nameof(r::_ComposedRule) = Symbol(join((b.name for b in r.boxes), " + "))

@inline function _view(box::_Box, cell::NamedTuple)
    box.single && return getfield(cell, only(box.targets))
    return NamedTuple{Tuple(box.layers)}(Tuple(getfield(cell, k) for k in box.targets))
end

function (r::_ComposedRule)(cell, nbrs, ctx)
    out = cell
    for box in r.boxes
        view = _view(box, cell)
        nb = Tuple(_view(box, nbrs[i]) for i in box.neighbours)
        p = ctx.p isa NamedTuple && haskey(ctx.p, box.name) ? getfield(ctx.p, box.name) :
            ctx.p
        bctx = CAC.CellContext(p, ctx.index, ctx.t, ctx.cellid, ctx.seed ⊻ box.seedmix,
                               ctx.covariates, ctx.fields)
        new = CAC.local_rule(box.rule, view, nb, bctx)
        for (k, layer) in enumerate(box.layers)
            box.owned[k] || continue
            v = box.single ? new : getfield(new, layer)
            out = merge(out, NamedTuple{(box.targets[k],)}((v,)))
        end
    end
    return out
end

"""
    oapply(diagram, boxes; dims=2, name=:composite, shared_randomness=false) -> CAModel

Compose CellularAutomataCore models along an undirected wiring diagram, such as
one written with Catlab's `@relation`. `boxes` gives an [`OpenCAModel`](@ref)
for each box of the diagram, as a vector in the diagram's order or a
`NamedTuple` by box name. A research extension, beyond the papers. (A method of
Catlab's `oapply`.)

The ports of each box are matched, in order, to the junctions its ports attach
to, and every junction becomes one state layer of the composite, named after
the junction's variable. Layers a box does not expose become layers of their
own, named `box_layer`. Each layer is updated by the one box that owns it:
the box that exposes it without listing it in `reads`. Two owners raise
[`LayerConflictError`](@ref); a layer without one keeps its state. All boxes
update synchronously from the same state, so the composite is the pairing of
the boxes' updates, and its neighbourhood is the union of theirs.

The composite's parameters are the boxes' default parameters, one
`NamedTuple` per box, named after the box. Its kernel fields and covariates
are the union of the boxes'. Each box draws its own random numbers, from a
seed derived from its name, unless `shared_randomness=true`, in which case
boxes that use the same draw numbers see the same uniforms. Every box's rule
must name its neighbourhood (`Moore`, `VonNeumann`, `Offsets`, ...), which is
resolved on a square lattice of `dims` dimensions. The composite must have at
least two layers.
"""
function oapply(d::AbstractUWD, boxes::AbstractVector{OpenCAModel}; dims::Integer=2,
                name::Symbol=:composite, shared_randomness::Bool=false)
    nb = nparts(d, :Box)
    length(boxes) == nb ||
        throw(ArgumentError("the diagram has $nb boxes, but $(length(boxes)) models were given"))
    boxnames = Symbol.(subpart(d, :name))
    allunique(boxnames) || throw(ArgumentError("box names must be distinct, got $boxnames"))
    variables = Symbol.(subpart(d, :variable))

    # the composite layer of each box layer, and who owns it
    target = Dict{Tuple{Int,Symbol},Symbol}()
    owners = Dict{Symbol,Vector{Symbol}}()
    declared = Dict{Symbol,CAC.StateVariable}()
    order = Symbol[]
    for (b, open) in enumerate(boxes)
        ps = ports(d, b)
        length(ps) == length(open.ports) ||
            throw(ArgumentError("box $(boxnames[b]) has $(length(ps)) ports, but its model exposes $(length(open.ports))"))
        for (port, layer) in zip(ps, open.ports)
            target[(b, layer)] = variables[subpart(d, port, :junction)]
        end
        for s in CAC.states(open.model)
            t = get!(target, (b, s.name), Symbol(boxnames[b], :_, s.name))
            if haskey(declared, t)
                typeof(declared[t].default) == typeof(s.default) ||
                    throw(ArgumentError("layer $t has type $(typeof(declared[t].default)) in one box and $(typeof(s.default)) in $(boxnames[b])"))
            else
                push!(order, t)
            end
            owns = !(s.name in open.reads)
            owns && push!(get!(owners, t, Symbol[]), boxnames[b])
            (owns || !haskey(declared, t)) && (declared[t] = s)
        end
    end
    for (t, os) in owners
        length(os) > 1 && throw(LayerConflictError(t, os))
    end
    length(order) >= 2 ||
        throw(ArgumentError("a composite needs at least two layers, got $(length(order))"))

    # the union neighbourhood, resolved on a lattice large enough for any radius in use
    lattice = CAC.Torus(ntuple(_ -> 201, dims)...)
    offsets_of = map(boxes) do open
        n = CAC.neighbourhood(open.model.rule)
        n === nothing &&
            throw(ArgumentError("the rule of $(open.model.name) must name its neighbourhood to be composed"))
        return collect(CAC.neighbourhood_offsets(n, lattice))
    end
    union_offsets = unique(reduce(vcat, offsets_of))

    prepared = map(enumerate(boxes)) do (b, open)
        layers = [s.name for s in CAC.states(open.model)]
        targets = [target[(b, l)] for l in layers]
        owned = [!(l in open.reads) for l in layers]
        nbrs = _positions(offsets_of[b], union_offsets)
        mix = shared_randomness ? UInt64(0) : hash(boxnames[b])
        return _Box(boxnames[b], open.model.rule, layers, targets, owned, nbrs,
                    length(layers) == 1, mix)
    end
    rule = CAC.LocalRule(_ComposedRule(Tuple(prepared)), CAC.Offsets(union_offsets))

    parameters = [CAC.Parameter(boxnames[b], CAC.defaults(open.model))
                  for (b, open) in enumerate(boxes)]
    fields = (;)
    for open in boxes
        clash = intersect(keys(fields), keys(open.model.fields))
        isempty(clash) ||
            throw(ArgumentError("kernel fields $(collect(clash)) are declared by more than one box"))
        fields = merge(fields, open.model.fields)
    end
    covariates = unique(reduce(vcat, [open.model.covariates for open in boxes]))
    statevars = [CAC.StateVariable(t, declared[t].default; domain=declared[t].domain,
                                   description=declared[t].description) for t in order]
    return CAC.CAModel(rule; name, states=statevars, parameters, fields, covariates,
                       description="composite of " * join(boxnames, ", "))
end

function oapply(d::AbstractUWD, boxes::NamedTuple; kwargs...)
    names = Symbol.(subpart(d, :name))
    for k in keys(boxes)
        k in names || throw(ArgumentError("the diagram has no box $k; boxes are $names"))
    end
    return oapply(d, OpenCAModel[getfield(boxes, n) for n in names]; kwargs...)
end
