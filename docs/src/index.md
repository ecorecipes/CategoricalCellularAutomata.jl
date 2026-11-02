# CategoricalCellularAutomata.jl

Cellular automata over groups as a cartesian category, generalised cellular automata over group homomorphisms, and wiring-diagram composition: the applied-category-theory layer of the ecorecipes cellular-automata ecosystem.

Part of the ecorecipes cellular-automata ecosystem: `CellularAutomataCore.jl` → `CategoricalCellularAutomata.jl` (applied category theory) and `CellularAutomataCore.jl` → `EcologicalCellularAutomata.jl` (model zoo).

Cellular automata over a group `G` form a category with finite products, and
cellular automata between different groups (generalised cellular automata over
group homomorphisms) form a category with weak products over the free product of
the groups [CastilloRamirez2025](@cite). The constructions extend from sets to
alphabets in any category with finite products, together with a categorical
Curtis–Hedlund–Lyndon theorem [CastilloRamirez2026](@cite). This package
implements those constructions on top of `CellularAutomataCore.jl`, binds them to
Catlab's cartesian-category generics, and produces rules that run on any
`CellularAutomataCore` backend.

## Status

Implemented: finite groups (cyclic, tori, Cayley tables), configurations, the
category of cellular automata over a group with its cartesian structure and
Catlab's `ThCartesianCategory` instance, wiring diagrams evaluated as cellular
automata, the Curtis–Hedlund–Lyndon checks, the bridge to and from
`CellularAutomataCore` rules and problems, generalised cellular automata over
group homomorphisms with weak products over free products, and linear and
monotone automata. Two research extensions go beyond the papers: stochastic
automata in a Markov category, and composition of CellularAutomataCore models
along undirected wiring diagrams.

## Errors

Every exception the package defines subtypes the abstract root
[`CategoricalCellularAutomataError`](@ref).

See the API Reference for docstrings and the [References](references.md) page
for full bibliographic entries.
