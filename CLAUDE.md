# CategoricalCellularAutomata.jl

Cellular automata over groups as a cartesian category, generalised cellular automata over group homomorphisms, and wiring-diagram composition: the applied-category-theory layer of the ecorecipes cellular-automata ecosystem.

## Place in the ecosystem

Dependency order (arrows = depends on): CategoricalCellularAutomata → CellularAutomataCore and
EcologicalCellularAutomata → CellularAutomataCore. The zoo does not depend on the categorical package.
This package depends on: `CellularAutomataCore.jl`, through `[sources]` paths to sibling directories.

The shared bibliography lives in the development workspace that holds the three packages side by side;
the `references.bib` files here are synced copies.

## Invariants that must not be broken

- This is the only package of the cellular-automata family that may depend on Catlab, GATlab or ACSets.
  The category of cellular automata over a group is a model-free Catlab `@instance` of
  `ThCartesianCategory{FullShift, CellularAutomaton}`; its operations (`compose`, `otimes`, `id`, `pair`,
  `proj1`, `proj2`, `mcopy`, `delete`, `braid`, `munit`) are Catlab's generic functions, re-exported, and are
  implemented by `_`-prefixed functions in `src/cartesian.jl`. n-ary `compose`/`otimes` methods are needed
  by GATlab's `functor`, which `realize` uses.
- Products are strict, as Catlab's free cartesian category assumes: a `FullShift` is a flat list of factor
  alphabets with flat tuple values, so `(X ⊗ Y) ⊗ Z == X ⊗ (Y ⊗ Z)`, and `munit()` (no factors, group
  `nothing`) is a strict unit.
- Catlab also exports `elements`, `restrict`, `shape`, `factorize` and `pullback`: this package adds methods to Catlab's functions
  rather than defining its own, so that `using Catlab` alongside it causes no ambiguity. Check new exports
  against Catlab's and CellularAutomataCore's.
- Equality of cellular automata enumerates patterns over the union of memory sets (Cor 3.8 of the framework
  paper); enumerations stop with `ArgumentError` beyond `PATTERN_LIMIT` patterns or `CONFIGURATION_LIMIT`
  configurations instead of hanging.
- Generalised automata whose codomain group is infinite (a free product) are evaluated one element at a
  time (`T(x, h)`); `==` needs a finite codomain group. Weak products use their own names (`weak_pair`,
  `weak_projections`), not Catlab's `pair` and projections, because they are not categorical products.
- `LinearCA`'s fast composition and powers are checked against the generic composition of local rules.
- `oapply` composites: each layer has at most one owner (`LayerConflictError`), all boxes update
  synchronously from the same state, parameters are namespaced by box, and each box's random numbers come
  from `seed ⊻ hash(box name)` unless `shared_randomness=true`; tests compare composites with hand-written
  layered rules exactly. Catlab's `oapply` is extended, not shadowed.
- A configuration over a torus group is exactly a CellularAutomataCore state (first axis fastest, element
  `g` at `CartesianIndex(g .+ 1)`); the bridge maps elements to centred offsets.
- A `NeighbourhoodSpace` built from a core space steps exactly as the core does (neighbours in the core's
  order; `Constant` edges as pinned cells); maps of spaces are tested by commuting with local rules (every
  rule for coverings, reflection-symmetric rules for `reflection_fold`, and an anisotropic rule must fail).
  `pullback(f, prob; space)` moves a whole problem: each cell runs its image's rule with its image's slot
  order and cell id (so its random numbers), and tests check every saved state equals the pulled-back
  original run, for stochastic and anisotropic rules, layered states, covariates, masks and graphs.
- Maps between models (`src/model_maps.jl`): a `ModelMap` is a map of cell states (and of parameters) between
  two `CAModel`s; it is a map of models when it commutes with the rules at the same cell id, time and seed, so
  runs map to runs exactly, stochastic ones included. `is_model_map` checks every local configuration (finite
  domains, or `cells`) at several contexts; `pushforward(f, prob)` keeps seed, space, covariates and mask and
  passes through `pullback`s along maps of spaces. Models and maps are an `@instance ThCategory{CAModel,
  ModelMap}` (objects compared with `===`). Tests compare mapped runs with the codomain's runs exactly, and
  include maps that must fail (a label that feeds back, a composite without shared random numbers). A
  callback acts on the whole state and is not moved by a map: `pushforward` and `pullback` of a problem with a
  callback raise `ArgumentError` unless `callback=` names the new problem's, and `is_model_map(f, prob)` is the
  check that includes it. The local check sees only rules. `quotient` and `forget_layers` build a codomain from
  the domain's own rule, so nothing is written twice, and never assume the result is a map: check it.
- This package does not depend on EcologicalCellularAutomata. Only the vignette environment does (vignette
  14 uses published models); the test suite does not, and `vignettes.yml` checks the zoo out.
- Gluing (`src/gluing.jl`): spaces as `SlotGraph` C-sets, patches as `OpenSlotGraph` structured cospans with
  discrete feet. `glue` computes colimits by union-find (feet are cells, so slots are never identified);
  `algorithm=:catlab` uses Catlab's `oapply` and the tests check the two agree. Glued landscapes are tested
  as bijective maps of spaces onto the core's lattices, and the landscape's step restricted to a patch must
  equal the patch's step.
- `proofs/` (Lean 4 / Mathlib, toolchain and Mathlib v4.30.0) proves the laws the tests check: the
  default target builds with `--wfail` (no `sorry`), `Audit.lean` lists every main theorem's axioms (only
  `propext`, `Classical.choice`, `Quot.sound`), and `Basic.lean` maps each Lean name to its Julia function.
  A change to a definition the proofs mirror (configurations, shifts, `CellularAutomaton`, `GeneralizedCA`,
  `glue`) updates the Lean statement too. Its dependencies live in `../../.lake-packages`, shared with
  sibling `proofs/` projects; CI uses a local checkout.
- Constructions faithful to the papers and the research extensions beyond them (stochastic cellular automata
  in a Markov category) are documented separately, and the extensions are labelled as such.

## Layout

- `src/CategoricalCellularAutomata.jl`: module docstring, exports, includes.
- `proofs/`: the Lean library (`CategoricalCellularAutomataProofs/{Basic,Configurations,CellularAutomata,
  Category,CurtisHedlundLyndon,Linear,Generalized,Gluing,Spaces,Models}.lean`), `Audit.lean`, `Makefile`, `lakefile.toml`, `lean-toolchain`, and the
  generated document; `.github/workflows/lean.yml` builds and audits it.
- `src/errors.jl`: the root `CategoricalCellularAutomataError` and every exception under it.
- `src/groups.jl`: `CyclicGroup`, `TorusGroup`, `FiniteGroup`. `src/configurations.jl`: `FinAlphabet`,
  `Configuration`, `shift`, `restrict`, `FullShift`. `src/ca.jl`: `CellularAutomaton`, evaluation, powers,
  equality. `src/cartesian.jl`: composition, products, the Catlab instance, `realize`. `src/chl.jl`:
  `is_equivariant`, `cellular_automaton`, `minimal_neighbourhood`. `src/bridge.jl`: `torus_group`,
  `torus_space`, core rules to automata and back (`LocalRule`, `CAProblem` methods). `src/homomorphisms.jl`:
  `GroupHom`, `FreeProduct` (reduced words), `ball`, `inclusion`, `induced_hom`. `src/generalized.jl`:
  `GeneralizedCA` stored as its factorisation (homomorphism, ordinary CA), `pullback`, `pushforward`, weak
  products. `src/linear.jl`: `LinearCA` (group-algebra coefficients, Gauss–Jordan inverse mod p).
  `src/monotone.jl`: `is_monotone`. Research extensions: `src/markov.jl` (`StochasticCA`, exact
  `distribution`, `marginal`, `stochastic_pair`, core sampling) and `src/composition.jl` (`OpenCAModel`,
  `oapply` for core `CAModel`s over undirected wiring diagrams, on square or hexagonal lattices and graphs)
  and `src/spaces.jl` (`NeighbourhoodSpace` from any core space, `SpaceMorphism`, `pullback`, `covering`,
  `reflection_fold`, `cayley_space`) and `src/gluing.jl` (`SlotGraph`, `lattice_patch`, `glue`) and `src/model_maps.jl` (`ModelMap`,
  `is_model_map`, `pushforward` of states and problems, `quotient`, `forget_layers`, the category of models).
- `test/runtests.jl`, `test/test_groups.jl`, `test/test_cartesian.jl` (category and product laws with random
  lookup-table rules), `test/test_chl_bridge.jl`, `test/test_generalized.jl` (homomorphisms, free
  products, generalised, linear and monotone automata), `test/test_markov.jl` (the research
  extensions), `test/test_spaces.jl` (geometries and composites on them), `test/test_gluing.jl` (landscapes glued
  from patches), `test/test_model_maps.jl` (maps between models), `test/test_errors.jl`,
  `test/test_docstrings.jl`: the suite,
  seeded RNGs only.

## Commands

```sh
julia --project -e 'using Pkg; Pkg.instantiate(); Pkg.test()'   # the test suite
julia --project=docs docs/make.jl --no-deploy                     # build docs locally
cd vignettes && quarto render && quarto render --to gfm         # render vignettes to html/gfm/pdf (julia engine; PDF needs lualatex + ../fonts/JuliaMono)
julia scripts/sync_vignettes.jl [--check]                         # copy vignettes into docs/src/tutorials
cd proofs && make build && make audit                           # Lean proofs: sorry-free build, axiom audit
cd proofs && make docs                                          # proofs document (.md/.html/.pdf; pandoc, lualatex)
```

## Files not to edit by hand

- `docs/src/tutorials/` is generated by `scripts/sync_vignettes.jl`.
- `proofs/CategoricalCellularAutomataProofs.{md,html,pdf}` are generated by `make docs` from the Lean
  sources; edit the `.lean` files.
- `vignettes/*/*.md`, `*.html`, `*.pdf` and `*_files/` are quarto output; edit the `.qmd`.
- `docs/src/references.bib` and `vignettes/references.bib` are copied from the workspace
  `docs/references.bib` by `scripts/sync_references.jl`; edit the workspace copy.

## Style

JuliaFormatter `yas`; docstrings on every exported name, which `test/test_docstrings.jl` enforces; the docs
build is strict (no `warnonly`), so a docstring left out of the manual or a broken `@ref` fails it; typed
exceptions with the offending names in the message: they live in `src/errors.jl` and
subtype `CategoricalCellularAutomataError`, invalid arguments and keywords raise `ArgumentError`, typed errors from a lower package pass
through unchanged and documented, and another package's type is named as a code span, never with `@ref`;
seeded RNGs only in tests; every optimised code path is tested against a slower reference; no emojis in code
or docs.
