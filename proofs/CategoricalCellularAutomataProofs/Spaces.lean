import CategoricalCellularAutomataProofs.Gluing

/-!
# Moving models between spaces

A space is a set of cells `X`, each reading its neighbours `nbrs c` in slot order (a list, so
graphs, whose cells have different numbers of neighbours, are included). A map of spaces
`φ : Y → X` preserves neighbours up to a reordering of each cell's slots: `ρ y` puts the
images of `y`'s neighbours in the slot order of `φ y`. A reordering moves list entries by
position, so it commutes with relabelling them (`ρ_natural`): a natural transformation of the
list functor, such as the identity (a covering) or reversal (a one-dimensional fold).

The package's `pullback(f, prob; space)` moves a problem along such a map: each cell `y` of
the new space runs the rule of its image `φ y`, reading its neighbours reordered by `ρ y`, and
draws the random numbers of `φ y`. A rule that depends on the cell and the time (as a rule
drawing counter-based random numbers keyed by cell and step does) is a family
`μ t c : List A → A`. The pulled-back run is the pullback of the run, step by step, for every
such rule: no symmetry of the rule is needed.
-/

namespace CategoricalCellularAutomataProofs

universe u

variable {X Y A : Type u}

/-- The run of a time-dependent rule: `run nbrs μ x n` is the configuration after `n`
synchronous steps from `x`, step `t` applying the rule `μ t`. -/
def run (nbrs : X → List X) (μ : ℕ → X → List A → A) (x : X → A) : ℕ → X → A
  | 0 => x
  | n + 1 => step nbrs (μ n) (run nbrs μ x n)

/-- A map of spaces `φ : Y → X` with slot reorderings `ρ`. -/
structure SpaceMap (Y X : Type u) (nbrsY : Y → List Y) (nbrsX : X → List X) where
  /-- where each cell goes -/
  φ : Y → X
  /-- the reordering of each cell's slots, at every type of values -/
  ρ : Y → ∀ {B : Type u}, List B → List B
  /-- a reordering moves entries by position, so it commutes with relabelling them -/
  ρ_natural : ∀ (y : Y) {B C : Type u} (g : B → C) (l : List B), ρ y (l.map g) = (ρ y l).map g
  /-- neighbours are preserved: the images of `y`'s neighbours, reordered, are `φ y`'s -/
  map_nbrs : ∀ y, ρ y ((nbrsY y).map φ) = nbrsX (φ y)

variable {nbrsY : Y → List Y} {nbrsX : X → List X}

/-- The rule pulled back along a map of spaces: the cell `y` runs the rule of `φ y` on its
neighbours' values in `φ y`'s slot order. -/
def SpaceMap.pullRule (f : SpaceMap Y X nbrsY nbrsX) (μ : X → List A → A) : Y → List A → A :=
  fun y l => μ (f.φ y) (f.ρ y l)

/-- One step of the pulled-back rule from a pulled-back configuration is the pullback of one
step. -/
theorem SpaceMap.step_pullback (f : SpaceMap Y X nbrsY nbrsX) (μ : X → List A → A)
    (x : X → A) : step nbrsY (f.pullRule μ) (x ∘ f.φ) = step nbrsX μ x ∘ f.φ := by
  funext y
  simp only [step, SpaceMap.pullRule, Function.comp_apply]
  rw [← List.map_map, f.ρ_natural, f.map_nbrs]

/-- **Moving a model along a map of spaces.** The run of the pulled-back time-dependent rule
from the pulled-back initial state is, at every step, the pullback of the run. -/
theorem SpaceMap.run_pullback (f : SpaceMap Y X nbrsY nbrsX) (μ : ℕ → X → List A → A)
    (x : X → A) (n : ℕ) :
    run nbrsY (fun t => f.pullRule (μ t)) (x ∘ f.φ) n = run nbrsX μ x n ∘ f.φ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, ih, SpaceMap.step_pullback]

/-- A covering: a map that preserves neighbours slot by slot (no reordering). -/
def SpaceMap.ofSlotwise (φ : Y → X) (h : ∀ y, (nbrsY y).map φ = nbrsX (φ y)) :
    SpaceMap Y X nbrsY nbrsX where
  φ := φ
  ρ _ _ l := l
  ρ_natural _ _ _ _ _ := rfl
  map_nbrs := h

/-- A fold that reverses the slots of some cells (on a line with neighbours `[left, right]`,
the mirrored half reads them the other way round), as `reflection_fold` builds. -/
def SpaceMap.ofReversing (φ : Y → X) (flip : Y → Bool)
    (h : ∀ y, (if flip y then List.reverse else id) ((nbrsY y).map φ) = nbrsX (φ y)) :
    SpaceMap Y X nbrsY nbrsX where
  φ := φ
  ρ y _ l := if flip y then l.reverse else l
  ρ_natural y _ _ g l := by cases flip y <;> simp [List.map_reverse]
  map_nbrs y := by simpa [apply_ite (fun F : List X → List X => F ((nbrsY y).map φ))] using h y

end CategoricalCellularAutomataProofs
