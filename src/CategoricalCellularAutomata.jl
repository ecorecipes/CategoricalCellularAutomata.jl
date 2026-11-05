"""
    CategoricalCellularAutomata

Cellular automata over groups as a cartesian category, generalised cellular automata over group homomorphisms, and wiring-diagram composition: the applied-category-theory layer of the ecorecipes cellular-automata ecosystem.

Cellular automata over a group `G` form a category with finite products, and
cellular automata between different groups (generalised cellular automata over
group homomorphisms) form a category with weak products over the free product of
the groups [CastilloRamirez2025](@cite). The constructions extend from sets to
alphabets in any category with finite products, together with a categorical
Curtis–Hedlund–Lyndon theorem [CastilloRamirez2026](@cite). This package
implements those constructions on top of `CellularAutomataCore.jl`, binds them to
Catlab's cartesian-category generics, and produces rules that run on any
`CellularAutomataCore` backend.

Part of the ecorecipes cellular-automata ecosystem.
"""
module CategoricalCellularAutomata

using Catlab: Catlab, @instance, ThCategory, ThCartesianCategory, FreeCartesianCategory,
              functor,
              generator,
              to_hom_expr
import Catlab.Theories: dom, codom, id, compose, otimes, ⊗, munit, braid, mcopy, delete,
                        pair,
                        proj1, proj2
# Catlab exports these names too; extending its functions keeps `using Catlab` free of clashes
import Catlab: elements, restrict, shape, factorize, pullback, oapply
using Catlab: nparts, subpart, parts, incident, add_parts!, legs, apex, FinFunction,
              @present, FreeSchema, @acset_type, OpenACSetTypes, FinSet, Multicospan
using Catlab.WiringDiagrams.UndirectedWiringDiagrams: AbstractUWD, ports
using CellularAutomataCore: CellularAutomataCore
const CAC = CellularAutomataCore

# Groups and homomorphisms
export AbstractGroup, AbstractFiniteGroup, CyclicGroup, TorusGroup, FiniteGroup
export GroupHom, FreeProduct, ball, inclusion, induced_hom
export elements, mul, identity_element, inverse, shape, label
# Alphabets, configurations and full shifts
export FinAlphabet, Configuration, FullShift, group, alphabet, shift, restrict
# Cellular automata
export CellularAutomaton, memory_set, local_map
# The cartesian category (Catlab's generic operations) and wiring diagrams
export dom, codom, id, compose, otimes, ⊗, munit, braid, mcopy, delete, pair, proj1, proj2
export realize
# Curtis–Hedlund–Lyndon
export is_equivariant, cellular_automaton, minimal_neighbourhood
# Generalised cellular automata and weak products
export GeneralizedCA, factorize, pullback, pushforward, weak_product, weak_projections,
       weak_pair
# Linear and monotone cellular automata
export LinearCA, coefficients, isinvertible, is_monotone
# Research extensions: stochastic cellular automata, and composition of core models
export StochasticCA, distribution, marginal, stochastic_pair
export OpenCAModel, oapply
# Research extension: maps between models, a category
export ModelMap, is_model_map, quotient, forget_layers
# CellularAutomataCore
export torus_group, torus_space
# Geometries: neighbourhood spaces and the maps between them
export NeighbourhoodSpace, neighbourhood_space, free_cells, cayley_space, apply_local,
       SpaceMorphism, is_morphism, covering, reflection_fold
# Gluing spaces: slot graphs, patches and their colimits
export SchSlotGraph, SlotGraph, OpenSlotGraphOb, OpenSlotGraph, slot_graph, interior_cells,
       halo_cells, lattice_patch, patch_coordinates, glue
# Exceptions: the root and the concrete types under it
export CategoricalCellularAutomataError, GroupMismatchError, DomainMismatchError,
       LayerConflictError

include("errors.jl")
include("groups.jl")
include("configurations.jl")
include("ca.jl")
include("cartesian.jl")
include("chl.jl")
include("bridge.jl")
include("spaces.jl")
include("gluing.jl")
include("homomorphisms.jl")
include("generalized.jl")
include("linear.jl")
include("monotone.jl")
include("markov.jl")
include("composition.jl")
include("model_maps.jl")

end # module
