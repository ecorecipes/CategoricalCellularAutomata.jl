# CategoricalCellularAutomataProofs

Lean 4 / Mathlib proofs of the laws `CategoricalCellularAutomata.jl` relies on (toolchain
v4.30.0, Mathlib v4.30.0). The test suite checks these laws numerically on finite groups and
alphabets; here they are proved for any group and alphabet.

```sh
cd proofs
lake exe cache get   # prebuilt Mathlib oleans (once per Mathlib revision)
make build           # lake build --wfail: the default target, sorry-free
make audit           # #print axioms for every main theorem (Audit.lean)
make docs            # the readable document: .md (mdgen), .html and .pdf (pandoc)
```

The dependency checkout lives in `../../.lake-packages` (`packagesDir`), one directory shared by
the `proofs/` projects of sibling packages. CI (`.github/workflows/lean.yml`) uses a local
checkout instead, runs `lake build --wfail` and the audit.

## Documents

`CategoricalCellularAutomataProofs.md`, `.html` and `.pdf` are generated from the Lean sources by
[mdgen](https://github.com/Seasawher/mdgen) (the `/-! ... -/` module docstrings become prose,
everything else a `lean` code block) and pandoc, and committed. They need pandoc (3.8 or later;
`lean.xml` is a minimal Lean syntax definition) and `lualatex`, with STIX Two Text and Math and
JuliaMono read from `../../fonts/JuliaMono/`.

## What is proved

1. `Basic.lean`: introduction and the table of Lean and Julia names.
2. `Configurations.lean`: configurations `G → A`; the shift `(g · x)(h) = x(h g)` is a left
   action; pullback along a homomorphism is contravariantly functorial and intertwines shifts.
3. `CellularAutomata.lean`: `τ(x)(g) = μ((x(s g))_{s ∈ S})` commutes with the shifts; two
   automata are equal when they agree at the identity (`σ == τ`); identity, composition over
   the products `T S` (`compose`), and pairing over a disjoint union of memory sets (`pair`).
4. `Category.lean`: the maps of configurations that are cellular automata form a category whose
   objects are alphabets, with the product of alphabets as a categorical product and the
   one-letter alphabet as terminal object, hence a Mathlib `CartesianMonoidalCategory`: the
   structure of the package's Catlab instance of `ThCartesianCategory`.
5. `CurtisHedlundLyndon.lean`: over any group, a map into a nonempty alphabet is a cellular
   automaton exactly when it commutes with the shifts and its value at the identity depends on
   finitely many cells; over a finite group, exactly when it commutes with the shifts.
6. `Linear.lean`: linear automata `τ(x)(g) = Σ_s a_s x(s g)` over a commutative semiring compose
   and take powers as products in the group algebra (`compose(L, M)` has coefficients `L * M`),
   and are cellular automata.
7. `Generalized.lean`: generalised automata along `φ : H →* G` factor as `φ* ∘ τ`
   (`factorize`); pullback commutes with local rules, `φ* ∘ τ_{φ(S)} = τ_S ∘ φ*`; they
   intertwine shifts along `φ` and compose along `φ ∘ ψ`.
8. `Gluing.lean`: configurations of a space glued as a colimit of patches are exactly the
   compatible families of configurations of the patches (a limit; unique gluing); one step of
   the landscape on a patch's interior is the patch's own step (halo exchange), and patches
   whose interiors cover the landscape determine its step.
9. `Spaces.lean`: a problem moved along a map of spaces (each cell reading its neighbours in
   its image's slot order and running its image's time-dependent rule) runs, step by step, the
   pullback of the original run, for every rule; coverings and reversing folds are instances.
