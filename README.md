# CategoricalCellularAutomata.jl

[![Build Status](https://github.com/ecorecipes/CategoricalCellularAutomata.jl/actions/workflows/CI.yml/badge.svg)](https://github.com/ecorecipes/CategoricalCellularAutomata.jl/actions/workflows/CI.yml)
[![Docs](https://img.shields.io/badge/docs-dev-blue.svg)](https://ecorecipes.github.io/CategoricalCellularAutomata.jl/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

Cellular automata over groups as a cartesian category, generalised cellular automata over group homomorphisms, and wiring-diagram composition: the applied-category-theory layer of the ecorecipes cellular-automata ecosystem.

Part of the ecorecipes cellular-automata ecosystem: `CellularAutomataCore.jl` → `CategoricalCellularAutomata.jl` (applied category theory) and `CellularAutomataCore.jl` → `EcologicalCellularAutomata.jl` (model zoo).

## Features

- **Groups**: cyclic groups, tori (`Z_n1 × … × Z_nd`, matching CellularAutomataCore's `Torus`) and any finite
  group from a Cayley table or from elements and a multiplication (permutation groups, for example).
- **Configurations and cellular automata over groups**: shifts, memory sets and local rules;
  `τ(x)(g) = μ((x(s g))_{s ∈ S})`; equality decided at the identity cell.
- **The cartesian category CA(G)**: composition (memory set `{s t}`), identities, strictly associative
  products of full shifts, pairing (memory set `S ∪ T`), projections, braiding, copy and delete, as an
  instance of Catlab's `ThCartesianCategory`.
- **Wiring diagrams**: Catlab `@program` diagrams realised as single cellular automata (`realize`), so a
  multi-layer model can be drawn, rewired and run.
- **Curtis–Hedlund–Lyndon**: test whether a map of configurations commutes with the shifts, recover its local
  rule, and shrink a memory set to the cells a rule depends on.
- **CellularAutomataCore bridge**: core rules on periodic lattices become cellular automata over their torus
  group, and automata (composites and products included) run on every core backend via `CAProblem`.
- **Generalised cellular automata**: group homomorphisms, pullbacks and pushforwards, `φ`-cellular automata
  between configurations over different groups (factorisation, composition, equality), the periodic-tiling
  square, and weak products over free products of groups.
- **Linear and monotone automata**: linear cellular automata over `GF(p)` that compose and take powers through
  their coefficients and invert by linear algebra; a monotonicity test for automata over ordered alphabets.
- **Research extensions, beyond the papers**: stochastic cellular automata as Markov kernels (exact
  distributions on small groups, couplings of paired automata, sampling on the core), and composition of
  CellularAutomataCore `CAModel`s along Catlab undirected wiring diagrams over shared layers (`oapply`), with
  one owner per layer and per-model random numbers, on square or hexagonal lattices and on graphs; and
  geometries beyond groups: any core space as a set of cells with neighbour lists (a coalgebra), maps of
  spaces along which configurations pull back and local rules commute (coverings of tori, reflecting edges
  as a fold of a doubled torus), constant edges as pinned cells; and landscapes glued from patches:
  spaces as C-sets of cells and neighbour slots, lattice patches with halos, gluing as a colimit along
  undirected wiring diagrams (`glue`), on which a local rule restricts to each patch.

## Quick Start

```julia
using CategoricalCellularAutomata
using CellularAutomataCore: Life, Torus, CAProblem, solve

Z = CyclicGroup(16); B = FinAlphabet(0:1)
rule90 = CellularAutomaton(Z, [15, 1], p -> xor(p...); dom=B)   # memory set {-1, +1}
twice = compose(rule90, rule90)                                   # memory set {-2, 0, 2}
twice == CellularAutomaton(Z, [14, 2], p -> xor(p...); dom=B)     # true: rule 90 at distance 2

life = CellularAutomaton(Life(), Torus(64, 64); alphabet=FinAlphabet(Int8[0, 1]))
solve(CAProblem(life^2, rand(Int8[0, 1], 64, 64), 10))          # two Life steps per step
```

## Installation

The ecosystem packages are not registered, and this package finds its siblings through `[sources]` paths, so
clone them side by side:

```sh
mkdir -p ca && cd ca
git clone https://github.com/ecorecipes/CellularAutomataCore.jl
git clone https://github.com/ecorecipes/CategoricalCellularAutomata.jl
cd CategoricalCellularAutomata.jl
julia --project -e 'using Pkg; Pkg.instantiate()'
```

Requires Julia ≥ 1.12.

## Vignettes

| # | Vignette | Description |
|---|---|---|
| 1 | [Cellular automata over groups](https://github.com/ecorecipes/CategoricalCellularAutomata.jl/blob/main/vignettes/01_ca_over_groups/01_ca_over_groups.md) | Groups, configurations, shifts, equivariance; equality at the identity cell; the bridge to the core |
| 2 | [Composing cellular automata](https://github.com/ecorecipes/CategoricalCellularAutomata.jl/blob/main/vignettes/02_composition/02_composition.md) | Composites and their memory sets, the category laws, minimal neighbourhoods, alphabets, non-abelian groups |
| 3 | [Products and multi-layer models](https://github.com/ecorecipes/CategoricalCellularAutomata.jl/blob/main/vignettes/03_products/03_products.md) | A host and aphid model as the pair of its layer updates; the product laws; copying and deleting |
| 4 | [Models from wiring diagrams](https://github.com/ecorecipes/CategoricalCellularAutomata.jl/blob/main/vignettes/04_wiring_diagrams/04_wiring_diagrams.md) | Catlab `@program` diagrams realised as cellular automata; rewiring to add an intervention |
| 5 | [Recognising cellular automata](https://github.com/ecorecipes/CategoricalCellularAutomata.jl/blob/main/vignettes/05_curtis_hedlund_lyndon/05_curtis_hedlund_lyndon.md) | The Curtis–Hedlund–Lyndon test, recovered local rules, maps that fail |
| 6 | [Generalised cellular automata](https://github.com/ecorecipes/CategoricalCellularAutomata.jl/blob/main/vignettes/06_generalised_ca/06_generalised_ca.md) | Homomorphisms, pullbacks, `φ`-automata; lifting a transect rule to a field; periodic landscapes |
| 7 | [Linear and monotone cellular automata](https://github.com/ecorecipes/CategoricalCellularAutomata.jl/blob/main/vignettes/07_alphabet_categories/07_alphabet_categories.md) | Linear automata over GF(p): fast powers, inverses; monotone automata bounding an uncertain survey |
| 8 | [Free products and weak products](https://github.com/ecorecipes/CategoricalCellularAutomata.jl/blob/main/vignettes/08_free_products/08_free_products.md) | Free products of groups, the weak product of generalised automata, and why pairs are not unique |
| 9 | [Stochastic cellular automata in a Markov category](https://github.com/ecorecipes/CategoricalCellularAutomata.jl/blob/main/vignettes/09_stochastic_ca_markov/09_stochastic_ca_markov.md) | Research extension: exact distributions, copying, couplings and draw numbers, correlated composites |
| 10 | [Composing models over shared layers](https://github.com/ecorecipes/CategoricalCellularAutomata.jl/blob/main/vignettes/10_composing_models/10_composing_models.md) | Research extension: crop, aphid and spraying models composed with `@relation` and `oapply` |
| 11 | [Geometries](https://github.com/ecorecipes/CategoricalCellularAutomata.jl/blob/main/vignettes/11_geometries/11_geometries.md) | Research extension: square and hexagonal tori as Cayley spaces, periodic and reflecting edges as quotients, constant edges as pinned cells, graphs, and composites on any geometry |
| 12 | [Gluing spaces](https://github.com/ecorecipes/CategoricalCellularAutomata.jl/blob/main/vignettes/12_gluing_spaces/12_gluing_spaces.md) | Research extension: landscapes as colimits of patches (strips, cylinders, tori, blocks), gluing in stages, dynamics restricted to patches, and fields joined by a road |

Each vignette is also published as a tutorial in the
[documentation](https://ecorecipes.github.io/CategoricalCellularAutomata.jl/); the sources are the `.qmd` files in
[`vignettes/`](vignettes/).

## References

The full bibliography for the ecosystem is `docs/src/references.bib` (also in
`vignettes/references.bib`); the rendered list is the References page of the
[documentation](https://ecorecipes.github.io/CategoricalCellularAutomata.jl/).
