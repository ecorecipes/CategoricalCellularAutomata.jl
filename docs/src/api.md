# API Reference

```@docs
CategoricalCellularAutomata
```

## Groups

```@docs
AbstractGroup
AbstractFiniteGroup
CyclicGroup
TorusGroup
FiniteGroup
elements(::AbstractFiniteGroup)
mul
identity_element
inverse
shape(::AbstractFiniteGroup)
label
```

## Alphabets, configurations and full shifts

```@docs
FinAlphabet
Configuration
group
shift
restrict(::Configuration, ::Any)
FullShift
alphabet
```

## Cellular automata

```@docs
CellularAutomaton
memory_set
local_map
Base.:(==)(::CellularAutomaton, ::CellularAutomaton)
Base.:^(::CellularAutomaton, ::Integer)
```

## The cartesian category

Cellular automata over a group `G` form a cartesian category whose objects are
full shifts. The package implements Catlab's `ThCartesianCategory` for
[`FullShift`](@ref) and [`CellularAutomaton`](@ref) and re-exports its
operations:

| operation | cellular automaton | memory set |
|:--|:--|:--|
| `compose(τ, σ)`, `σ ∘ τ` | `x ↦ σ(τ(x))` | `{s t : s ∈ S, t ∈ T}` |
| `id(X)` | `x ↦ x` | `{e}` |
| `otimes(X, Y)`, `X ⊗ Y` | the product full shift (flat tuples) | |
| `pair(σ, τ)` | `x ↦ (σ(x), τ(x))` | `S ∪ T` |
| `proj1(X, Y)`, `proj2(X, Y)` | the projections of `X ⊗ Y` | `{e}` |
| `otimes(σ, τ)` | `(x, y) ↦ (σ(x), τ(y))` | `S ∪ T` |
| `braid(X, Y)` | `(x, y) ↦ (y, x)` | `{e}` |
| `mcopy(X)`, `delete(X)` | `x ↦ (x, x)`, `x ↦ ()` | `{e}` |
| `munit()` | the unit object | |
| `dom(τ)`, `codom(τ)` | the domain and codomain full shifts | |

```@docs
realize
```

## Group homomorphisms and free products

```@docs
GroupHom
FreeProduct
ball
inclusion
induced_hom
```

## Generalised cellular automata

Cellular automata between configurations over different groups, related by a
group homomorphism, and their weak products over free products.

```@docs
GeneralizedCA
factorize(::GeneralizedCA)
pullback(::GroupHom, ::Configuration)
pushforward
Base.:(==)(::GeneralizedCA, ::GeneralizedCA)
weak_product
weak_projections
weak_pair
```

## Linear and monotone cellular automata

Cellular automata whose alphabets are vector spaces over a prime field, and
partially ordered sets.

```@docs
LinearCA
coefficients
isinvertible
Base.inv(::LinearCA)
is_monotone
```

## Research extension: stochastic cellular automata

Beyond the papers, which treat deterministic automata: stochastic cellular
automata as morphisms of a Markov category, where copying is not natural and
pairs depend on a coupling.

```@docs
StochasticCA
distribution
marginal
stochastic_pair
CellularAutomataCore.LocalRule(::StochasticCA{<:Union{CyclicGroup, TorusGroup}})
```

## Research extension: composing models

CellularAutomataCore models composed along undirected wiring diagrams over
shared layers.

```@docs
OpenCAModel
oapply(::Catlab.WiringDiagrams.UndirectedWiringDiagrams.AbstractUWD, ::AbstractVector{OpenCAModel})
```

## The Curtis–Hedlund–Lyndon theorem

```@docs
is_equivariant
cellular_automaton
minimal_neighbourhood
```

## CellularAutomataCore

```@docs
torus_group
torus_space
CellularAutomaton(::CellularAutomataCore.AbstractRule, ::CellularAutomataCore.Lattice)
CellularAutomataCore.LocalRule(::CellularAutomaton{<:Union{CyclicGroup, TorusGroup}})
CellularAutomataCore.CAProblem(::CellularAutomaton{<:Union{CyclicGroup, TorusGroup}}, ::Any, ::Any, ::Vararg)
```

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

## Exceptions

Every exception the package defines subtypes the abstract root
[`CategoricalCellularAutomataError`](@ref). Invalid arguments and keywords raise
Base's `ArgumentError`, which is outside it.

```@docs
CategoricalCellularAutomataError
GroupMismatchError
DomainMismatchError
LayerConflictError
```
