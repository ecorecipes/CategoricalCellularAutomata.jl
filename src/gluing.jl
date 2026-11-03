# Gluing spaces. A space is drawn as a slot graph: a C-set with cells and slots, each slot going
# from the cell that reads to the cell it reads, labelled with its position in the reader's list.
# A closed space (every cell with its full list) is a NeighbourhoodSpace; an open one, a patch, also
# has halo cells that its cells read but that have no slots of their own. Patches are glued by
# pushouts of C-sets along shared cells (structured cospans with discrete feet, so composites are
# given by undirected wiring diagrams): each patch's halo is identified with cells of its
# neighbours, and the slots of the colimit are the disjoint union of the patches' slots. Pulling
# configurations back along the colimit's inclusions turns the colimit into a limit (a
# configuration on the landscape is one on each patch, agreeing where they meet), and a local
# rule on the landscape, restricted to a patch, is the rule on the patch reading its halo.

@present SchSlotGraph(FreeSchema) begin
    (Cell, Slot)::Ob
    reader::Hom(Slot, Cell)
    read::Hom(Slot, Cell)
    Index::AttrType
    index::Attr(Slot, Index)
end

"""
    SlotGraph{T}()

A space as a C-set (schema `SchSlotGraph`): parts `Cell` and `Slot`, maps
`reader, read: Slot → Cell` and an attribute `index: Slot → T` (an `Int`, the
slot's position in the reader's neighbour list). Slot `s` says that cell
`reader(s)` reads cell `read(s)` as its `index(s)`-th neighbour. Cells
without slots are halo cells: read, but not updated, by the space. Build one
with [`slot_graph`](@ref) or [`lattice_patch`](@ref), or by hand with
`add_parts!`; [`NeighbourhoodSpace`](@ref) turns a closed one back into a
space. Maps of slot graphs are Catlab `ACSetTransformation`s, and slot
graphs have all colimits (pushouts glue them).
"""
@acset_type SlotGraph(SchSlotGraph, index=[:reader, :read])

const OpenSlotGraphOb, OpenSlotGraph = OpenACSetTypes(SlotGraph, :Cell)

@doc """
    SchSlotGraph

The schema of [`SlotGraph`](@ref): objects `Cell` and `Slot`, morphisms
`reader, read: Slot → Cell`, and an attribute `index: Slot → Index`.
""" SchSlotGraph

@doc """
    OpenSlotGraph{T}(g::SlotGraph{T}, legs::FinFunction...)

An open slot graph: a [`SlotGraph`](@ref) with legs, functions from finite
sets of cells (the feet) into it; Catlab's structured (multi)cospans with
discrete feet [Baez2020](@cite). Composites are taken with
[`glue`](@ref) (or Catlab's `oapply`, `compose` and `otimes`); the legs are
Catlab's `legs`, the slot graph its `apex`.
""" OpenSlotGraph

@doc """
    OpenSlotGraphOb{T}

The objects that [`OpenSlotGraph`](@ref)s go between: finite sets of cells,
seen as slot graphs with no slots.
""" OpenSlotGraphOb

"""
    slot_graph(S::NeighbourhoodSpace) -> SlotGraph{Int}

The slot graph of `S`: one cell for each cell of `S`, one slot for each
neighbour of a free cell. Pinned cells become halo cells (cells without
slots), so their values are dropped.
"""
function slot_graph(S::NeighbourhoodSpace)
    g = SlotGraph{Int}()
    add_parts!(g, :Cell, length(S.neighbours))
    n = free_cells(S)
    reader = [i for i in 1:n for _ in S.neighbours[i]]
    read = reduce(vcat, S.neighbours[1:n]; init=Int[])
    index = [k for i in 1:n for k in eachindex(S.neighbours[i])]
    add_parts!(g, :Slot, length(reader); reader, read, index)
    return g
end

"""
    interior_cells(g::SlotGraph) -> Vector{Int}

The cells of `g` that have slots, in order: those a rule on `g` updates.
"""
function interior_cells(g::SlotGraph)
    return [c for c in parts(g, :Cell) if !isempty(incident(g, c, :reader))]
end

"""
    halo_cells(g::SlotGraph) -> Vector{Int}

The cells of `g` that have no slots, in order: read by other cells, never
updated.
"""
halo_cells(g::SlotGraph) = [c for c in parts(g, :Cell) if isempty(incident(g, c, :reader))]

# The neighbours of cell c in slot order; throws unless the slots are numbered 1:k once each.
function _slot_list(g::SlotGraph, c)
    slots = incident(g, c, :reader)
    idx = g[slots, :index]
    sort(idx) == 1:length(idx) ||
        throw(ArgumentError("cell $c has slots numbered $(sort(idx)), not 1:$(length(idx)) " *
                            "(do two glued patches both update it?)"))
    return g[slots[sortperm(idx)], :read]
end

"""
    NeighbourhoodSpace(g::SlotGraph; boundary=nothing)

The space of a slot graph: its interior cells (those with slots, in order) are
the free cells, each reading its neighbours in slot order. Every cell's slots
must be numbered `1:k` once each (two glued patches that both update a cell
give it its slots twice). Halo cells that are read become one cell pinned to
`boundary` (as beyond a `Constant` edge); with `boundary = nothing` there must
be none. Halo cells nobody reads are dropped.
"""
function NeighbourhoodSpace(g::SlotGraph; boundary=nothing)
    free = interior_cells(g)
    rank = Dict(c => k for (k, c) in enumerate(free))
    lists = [_slot_list(g, c) for c in free]
    open = any(ns -> any(j -> !haskey(rank, j), ns), lists)
    if open && boundary === nothing
        throw(ArgumentError("the space is open (cells read halo cells); close it with a boundary value"))
    end
    pin = length(free) + 1
    neighbours = [[get(rank, j, pin) for j in ns] for ns in lists]
    open || return NeighbourhoodSpace(neighbours)
    k = maximum(length, neighbours)
    push!(neighbours, fill(pin, k))
    return NeighbourhoodSpace(neighbours; pinned=Dict{Int,Any}(pin => boundary))
end

# A lattice patch: the cells of `dims` (first axis fastest) followed by the halo, the cells of the
# box padded by `r` on each side that are outside `dims`, in the padded box's order.
function _patch_layout(dims::NTuple{N,Int}, r::NTuple{N,Int}) where {N}
    inner = vec(collect(CartesianIndices(dims)))
    padded = CartesianIndices(ntuple(d -> (1 - r[d]):(dims[d] + r[d]), Val(N)))
    halo = [I for I in padded if !all(d -> 1 <= I[d] <= dims[d], 1:N)]
    return vcat(inner, halo)
end

function _patch_geometry(space::CAC.Lattice{N}, nbhd) where {N}
    nbhd = something(nbhd, CAC.default_neighbourhood(space))
    offs = collect(CAC.neighbourhood_offsets(nbhd, space))
    r = ntuple(d -> maximum(o -> abs(o[d]), offs; init=0), Val(N))
    return offs, size(space), r
end

"""
    patch_coordinates(space::Lattice, neighbourhood=nothing) -> Vector{CartesianIndex}

The position of each cell of [`lattice_patch`](@ref)`(space, neighbourhood)`:
the cells of the lattice in order (first axis fastest), then the halo, the
positions beyond the edges within the neighbourhood's reach on each axis (as
`0`, `-1`, … or `n + 1`, …).
"""
function patch_coordinates(space::CAC.Lattice, nbhd=nothing)
    _, dims, r = _patch_geometry(space, nbhd)
    return _patch_layout(dims, r)
end

"""
    lattice_patch(space::Lattice, neighbourhood=nothing) -> OpenSlotGraph{Int}

The cells of the lattice `space` (square or hexagonal; its edges are ignored)
as an open slot graph: each cell reads `neighbourhood` (the space's default
if `nothing`), and the cells beyond the edges that it reads are halo cells
(see [`patch_coordinates`](@ref)). The legs are the faces, two for each axis
`d`, in the order axis 1 low, axis 1 high, axis 2 low, …: the low face is the
strip of positions `1 - r:r` on axis `d` (the halo and the first `r` layers,
`r` the neighbourhood's reach along `d`) across the padded box, the high face
`n - r + 1:n + r`, both in the padded box's order. Gluing the high face of
one patch to the low face of another (with [`glue`](@ref)) sets them side by
side along axis `d`: each one's halo becomes the other's edge cells.
"""
function lattice_patch(space::CAC.Lattice{N}, nbhd=nothing) where {N}
    offs, dims, r = _patch_geometry(space, nbhd)
    coords = _patch_layout(dims, r)
    cell = Dict(I => k for (k, I) in enumerate(coords))
    g = SlotGraph{Int}()
    add_parts!(g, :Cell, length(coords))
    n, k = prod(dims), length(offs)
    add_parts!(g, :Slot, n * k; reader=repeat(1:n; inner=k),
               read=[cell[coords[i] + o] for i in 1:n for o in offs],
               index=repeat(1:k, n))
    padded = ntuple(d -> (1 - r[d]):(dims[d] + r[d]), Val(N))
    faces = FinFunction[]
    for d in 1:N, side in ((1 - r[d]):r[d], (dims[d] - r[d] + 1):(dims[d] + r[d]))
        box = CartesianIndices(ntuple(e -> e == d ? side : padded[e], Val(N)))
        push!(faces, FinFunction(Int[cell[I] for I in vec(box)], length(coords)))
    end
    return OpenSlotGraph{Int}(g, faces...)
end

"""
    glue(diagram, patches; algorithm=:union_find)
        -> (landscape::OpenSlotGraph, inclusions::Vector{Vector{Int}})

Glue open slot graphs ([`lattice_patch`](@ref)es, or any
[`OpenSlotGraph`](@ref)) along the undirected wiring diagram `diagram` (from
Catlab's `@relation`): each box is a patch, named in `patches` (a `Dict` or
`NamedTuple` from box names to patches; a patch may fill several boxes), its
ports its legs in order, and legs on the same junction are identified cell by
cell (their feet must have the same size). The landscape is the colimit (a
pushout for two patches, a coequaliser for a patch glued to itself), with
legs for the diagram's outer junctions so it can be glued again;
`inclusions[b]` sends each cell of box `b`'s patch to its cell in the
landscape. Close it with [`NeighbourhoodSpace`](@ref)`(apex(landscape);
boundary)`.

The feet are discrete (cells, no slots), so the colimit identifies cells only
and its slots are the disjoint union of the patches' slots: the default
`algorithm = :union_find` computes it so, in time linear in the size of the
patches. `algorithm = :catlab` takes it with Catlab's `oapply` for
structured cospans instead: the same landscape up to the order of its cells,
but slow beyond a few hundred cells.
"""
function glue(d::AbstractUWD, patches::Union{AbstractDict,NamedTuple};
              algorithm::Symbol=:union_find)
    names = Symbol.(subpart(d, :name))
    get_patch(b) = haskey(patches, b) ? patches[b] :
                   throw(ArgumentError("no patch for box $b; boxes are $(unique(names))"))
    cospans = [get_patch(b) for b in names]
    for (b, c) in enumerate(cospans)
        length(ports(d, b)) == length(legs(c)) ||
            throw(ArgumentError("box $b ($(names[b])) has $(length(ports(d, b))) ports but its patch $(length(legs(c))) legs"))
    end
    if algorithm === :catlab
        landscape, colim = oapply(d, cospans; return_colimit=true)
        inclusions = [_leg_cells(legs(colim)[b]) for b in eachindex(names)]
        return landscape, inclusions
    end
    algorithm === :union_find ||
        throw(ArgumentError("algorithm must be :union_find or :catlab, got :$algorithm"))
    return _glue_union_find(d, cospans)
end

_leg_cells(leg) = Vector{Int}(collect(leg[:Cell]))

function _glue_union_find(d::AbstractUWD, cospans)
    apexes = [apex(c) for c in cospans]
    offset = cumsum([0; [nparts(g, :Cell) for g in apexes]])
    parent = collect(1:offset[end])
    function root(i)
        while parent[i] != i
            parent[i] = parent[parent[i]]
            i = parent[i]
        end
        return i
    end
    # Identify the cells of every leg on a junction with those of the first leg on it.
    first_leg = Dict{Int,Vector{Int}}()
    for (b, cospan) in enumerate(cospans), (p, leg) in zip(ports(d, b), legs(cospan))
        j = subpart(d, p, :junction)
        cells = offset[b] .+ _leg_cells(leg)
        other = get!(first_leg, j, cells)
        other === cells && continue
        length(other) == length(cells) ||
            throw(ArgumentError("legs on junction $j have feet of $(length(other)) and $(length(cells)) cells"))
        for (u, v) in zip(other, cells)
            ru, rv = root(u), root(v)
            ru == rv || (parent[max(ru, rv)] = min(ru, rv))
        end
    end
    # Number the classes in order of their first cell.
    newid = zeros(Int, offset[end])
    count = 0
    for i in eachindex(parent)
        r = root(i)
        newid[r] == 0 && (newid[r] = (count += 1))
        newid[i] = newid[r]
    end
    g = SlotGraph{Int}()
    add_parts!(g, :Cell, count)
    for (b, h) in enumerate(apexes)
        nparts(h, :Slot) == 0 && continue
        add_parts!(g, :Slot, nparts(h, :Slot);
                   reader=newid[offset[b] .+ h[:reader]], read=newid[offset[b] .+ h[:read]],
                   index=h[:index])
    end
    outer = map(subpart(d, :outer_junction)) do j
        haskey(first_leg, j) ||
            throw(ArgumentError("outer junction $j is attached to no box"))
        return FinFunction(newid[first_leg[j]], count)
    end
    feet = FinSet[FinSet(length(collect(f))) for f in outer]
    landscape = OpenSlotGraph{Int}(g,
                                   Multicospan(FinSet(count), FinFunction[outer...], feet))
    inclusions = [newid[(offset[b] + 1):offset[b + 1]] for b in eachindex(cospans)]
    return landscape, inclusions
end

"""
    apply_local(f, g::SlotGraph, x) -> Vector

One synchronous step on the slot graph `g` of the local rule `f(cell,
neighbours)` from the configuration `x` over all cells of `g`: each interior
cell reads its neighbours in slot order, and halo cells keep their values.
On a patch of a glued landscape this is the landscape's step restricted to
the patch's interior, given the halo's values from the landscape.
"""
function apply_local(f, g::SlotGraph, x::AbstractVector)
    length(x) == nparts(g, :Cell) ||
        throw(ArgumentError("the configuration has $(length(x)) cells, the slot graph $(nparts(g, :Cell))"))
    out = Vector{Any}(x)
    for c in interior_cells(g)
        out[c] = f(x[c], Tuple(x[j] for j in _slot_list(g, c)))
    end
    return convert(Vector{eltype(x)}, out)
end
