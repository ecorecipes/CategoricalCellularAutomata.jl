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
4. `Generalized.lean`: generalised automata along `φ : H →* G` factor as `φ* ∘ τ`
   (`factorize`); pullback commutes with local rules, `φ* ∘ τ_{φ(S)} = τ_S ∘ φ*`; they
   intertwine shifts along `φ` and compose along `φ ∘ ψ`.
5. `Gluing.lean`: configurations of a space glued as a colimit of patches are exactly the
   compatible families of configurations of the patches (a limit; unique gluing); one step of
   the landscape on a patch's interior is the patch's own step (halo exchange), and patches
   whose interiors cover the landscape determine its step.
