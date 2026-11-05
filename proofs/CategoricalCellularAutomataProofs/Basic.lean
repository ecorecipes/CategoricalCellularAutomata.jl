/-!
# Formal verification of CategoricalCellularAutomata.jl

This library proves, in Lean 4 with Mathlib, the laws that `CategoricalCellularAutomata.jl`
relies on and that its test suite checks numerically. The definitions are the mathematical
objects the Julia types implement, over any group (finite or not), with any alphabet; the
Julia package works with finite groups and alphabets, so its computations are instances.

| Lean | Julia | statement |
|---|---|---|
| `Config G A` | `Configuration` | a configuration `G → A` |
| `shift g x` | `shift(x, g)` | `(g · x)(h) = x(h g)`, a left action (`shift_one`, `shift_shift`) |
| `pullback φ x` | `pullback(φ, X)` | `x ∘ φ`, contravariantly functorial (`pullback_id`, `pullback_comp`) |
| `ca S μ` | `CellularAutomaton(G, S, μ)` | `τ(x)(g) = μ((x(s g))_{s ∈ S})` |
| `ca_shift` | `is_equivariant` | every cellular automaton commutes with the shifts |
| `ca_eq_iff` | `σ == τ` | two automata are equal when they agree at the identity |
| `ca_id`, `ca_comp` | `id`, `compose` | the identity, and composites with memory set `T S` |
| `ca_pair` | `pair` | pairing over the disjoint union of memory sets |
| `CAObj G`, `IsCA` | `FullShift`, `CellularAutomaton` | alphabets, and the maps of configurations that are cellular automata |
| `CartesianMonoidalCategory (CAObj G)` | the Catlab `@instance` of `ThCartesianCategory` | CA(G) is a cartesian monoidal category: `compose`, `id`, `otimes`, `munit`, `proj1`, `proj2`, `pair` |
| `isCA_iff_shift_comm_and_local` | `is_equivariant`, `cellular_automaton` | Curtis–Hedlund–Lyndon: a cellular automaton is an equivariant map that is local at the identity |
| `isCA_iff_shift_comm` | `cellular_automaton`, `minimal_neighbourhood` | over a finite group, every equivariant map is a cellular automaton |
| `linCA a` | `LinearCA(G, coefficients; p)` | `τ(x)(g) = Σ_s a_s x(s g)` |
| `linCA_mul`, `linCA_pow` | `compose`, `^` for `LinearCA` | composition and powers are products in the group algebra |
| `gca φ S μ` | `GeneralizedCA(φ, S, μ)` | `T(x)(h) = μ((x(s φ(h)))_{s ∈ S})` |
| `gca_eq_pullback_ca` | `factorize` | `T = φ* ∘ τ` |
| `pullback_ca` | `pullback`, `SpaceMorphism` | pullback commutes with local rules: `φ* ∘ τ_{φ(S)} = τ_S ∘ φ*` |
| `gca_comp` | `compose` | generalised automata compose along `φ ∘ ψ` |
| `gluedConfigEquiv`, `exists_unique_glued_config` | `glue` | configurations of a glued space are the compatible families on its patches (a limit) |
| `step_restrict`, `step_eq_of_cover` | `glue`, `apply_local` | the landscape's step on a patch's interior is the patch's step |
| `SpaceMap`, `SpaceMap.run_pullback` | `SpaceMorphism`, `pullback(f, prob; space)` | a problem moved along a map of spaces (slots reordered, the image's rule and random numbers) runs the pullback of the original run |
| `CAModel`, `ModelMap`, `instCategoryCAModel` | `CAModel`, `ModelMap`, `compose`, `id`, `is_model_map` | models and the maps of cell states commuting with their rules form a category |
| `ModelMap.run_map` | `pushforward(f, prob)` | a map of models sends every run to the run from the mapped initial state |
| `SpaceMap.pullFunctor` | `pullback(f, prob; space)`, `pushforward` | moving models along a map of spaces is a functor: maps of models and of spaces commute |
| `Lumping`, `Lumping.model` | `quotient(model, h, section)`, `forget_layers` | the quotient's rule: lift the neighbours, apply the rule, map the result down |
| `Lumping.descends_iff_exists_rule`, `Lumping.rule_unique` | `is_model_map` on a quotient | `h` commutes with some rule exactly when the dynamics do not depend on what it forgets; that rule is the quotient's, whichever section is used |
| `Lumping.lift_comp`, `Lumping.lift_unique` | `quotient` | the universal property: maps of models that do not distinguish what `h` forgets factor through the quotient, uniquely |
| `Lumping.liftCallback`, `Lumping.runWith_quotient` | `pushforward(f, prob; callback=:lift)` | a callback lifts when it does not depend on what is forgotten, and the quotient with it runs every run of the original, mapped down |
| `wholeStep`, `Lumping.runWith_wholeStep_quotient`, `Lumping.wholeStep_unique` | `pushforward(f, prob; callback=:lift_step)` | the rule and the callback as one step: when a whole step does not depend on what is forgotten, the quotient of it runs every run of the original, mapped by `h`, and is the only such step |
| `Lumping.wholeStep_descends`, `Lumping.liftCallback_wholeStep`, `wholeStep_strictly_more` | `callback=:lift_step` and `callback=:lift` | what descends separately descends together, with the same result, and the converse fails: a rule can write a layer that its callback reads |
| `BlockLumping`, `BlockLumping.blockRun_quotient` | `quotient` of a model with a `BlockRule` | block rules: the same construction on blocks of states, and the quotient runs every run of the original, mapped down |
| `Lumping.erased_run` | `is_model_map(f, prob)` | what a run can show: without feedback, erasing what is forgotten changes nothing kept, so a difference disproves the map |
| `SlidingMap`, `SlidingMap.run_map` | `SlidingBlockMap`, `pushforward`, `is_model_map` | maps that read a window around each cell send runs to runs |
| `instCategorySlidingModels`, `ModelMap.slidingFunctor`, `kinkMap126_not_cellwise` | `compose` of `SlidingBlockMap`s and `ModelMap`s | they form a category holding the cell-by-cell maps as a subcategory, and it is larger |
| `kinkMap126`, `wallsMap`, `walls_need_other_coins` | vignette 15, `Maps that read neighbours` | the boundaries of rule 126 are rule 18; the boundaries of a voter model move on the coins of two cells, whichever coins are drawn, and cannot on one |
| `factor_exists_iff`, `factor_unique`, `factor_isCA` | the search over elementary rules in the tests | through a surjective cellular automaton, a factor exists exactly when the rule respects the fibres, and is a unique cellular automaton |

Every theorem in the default target is free of `sorry`; `Audit.lean` prints the axioms each
main theorem uses (only `propext`, `Classical.choice` and `Quot.sound` are expected).
-/
