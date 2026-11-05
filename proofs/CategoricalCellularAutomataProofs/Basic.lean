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

Every theorem in the default target is free of `sorry`; `Audit.lean` prints the axioms each
main theorem uses (only `propext`, `Classical.choice` and `Quot.sound` are expected).
-/
