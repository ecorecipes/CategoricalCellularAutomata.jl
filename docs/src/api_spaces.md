# Spaces and gluing

Research extension: geometries beyond groups, as neighbourhood spaces and the
maps between them, and landscapes glued from patches.

## Geometries

Spaces beyond groups: the cells of any CellularAutomataCore space with their
neighbour lists, and the maps between spaces that preserve neighbours, along
which configurations pull back.

```@docs
NeighbourhoodSpace
neighbourhood_space
free_cells
cayley_space
apply_local
SpaceMorphism
is_morphism
pullback(::SpaceMorphism, ::AbstractVector)
covering
reflection_fold
compose(::SpaceMorphism, ::SpaceMorphism)
```

## Gluing spaces

Spaces as C-sets of cells and neighbour slots, patches with halos, and
landscapes glued from patches as colimits along undirected wiring diagrams.

```@docs
SchSlotGraph
SlotGraph
OpenSlotGraph
OpenSlotGraphOb
slot_graph
interior_cells
halo_cells
NeighbourhoodSpace(::SlotGraph)
lattice_patch
patch_coordinates
glue
apply_local(::Any, ::SlotGraph, ::AbstractVector)
```
