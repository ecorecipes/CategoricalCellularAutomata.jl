import CategoricalCellularAutomataProofs.Category
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Curtis–Hedlund–Lyndon

The package decides whether a map of configurations is a cellular automaton
(`is_equivariant`, `cellular_automaton`, `minimal_neighbourhood`) by checking that it commutes
with the shifts and that its value at the identity depends on finitely many cells. This file
proves that test correct, in the uniform form that needs no topology: over any group, a map of
configurations (into a nonempty alphabet) is a cellular automaton exactly when it commutes
with the shifts and its value at the identity depends only on the cells of some finite set.
Over a finite group the second condition always holds, so a map is a cellular automaton
exactly when it commutes with the shifts, with the whole group as a memory set.
-/

namespace CategoricalCellularAutomataProofs

universe u

variable {G : Type u} [Monoid G] {A B : Type u}

/-- A map whose value at the identity depends only on the cells of `S`. -/
def LocalAt (S : Finset G) (f : Config G A → Config G B) : Prop :=
  ∀ x y : Config G A, (∀ s ∈ S, x s = y s) → f x 1 = f y 1

/-- A cellular automaton's value at the identity depends only on its memory set. -/
theorem IsCA.exists_localAt [DecidableEq G] {f : Config G A → Config G B} (hf : IsCA G f) :
    ∃ S : Finset G, LocalAt S f := by
  obtain ⟨I, _, S, μ, rfl⟩ := hf
  have := Fintype.ofFinite I
  refine ⟨Finset.univ.image S, fun x y h => ?_⟩
  simp only [ca_apply, mul_one]
  congr 1
  funext i
  exact h (S i) (Finset.mem_image_of_mem S (Finset.mem_univ i))

/-- **Curtis–Hedlund–Lyndon (uniform form).** Over any group, a map of configurations into
a nonempty alphabet is a cellular automaton exactly when it commutes with the shifts and its
value at the identity depends only on a finite set of cells; that set is then a memory set. -/
theorem isCA_iff_shift_comm_and_local [DecidableEq G] [Nonempty A]
    (f : Config G A → Config G B) :
    IsCA G f ↔ (∀ g x, f (shift g x) = shift g (f x)) ∧ ∃ S : Finset G, LocalAt S f := by
  constructor
  · intro hf
    exact ⟨hf.shift_comm, hf.exists_localAt⟩
  · rintro ⟨hshift, S, hS⟩
    classical
    let ext : (S → A) → Config G A := fun p g =>
      if h : g ∈ S then p ⟨g, h⟩ else Classical.arbitrary A
    refine ⟨S, inferInstance, fun s => s.1, fun p => f (ext p) 1, ?_⟩
    funext x g
    rw [apply_eq_apply_one_shift f hshift x g, ca_apply]
    refine hS _ _ (fun s hs => ?_)
    simp [ext, hs, shift]

/-- **Curtis–Hedlund–Lyndon on a finite group.** A map of configurations over a finite group
is a cellular automaton exactly when it commutes with the shifts; the whole group serves as
its memory set (`cellular_automaton` recovers the rule, `minimal_neighbourhood` shrinks the
set). -/
theorem isCA_iff_shift_comm [Finite G] (f : Config G A → Config G B) :
    IsCA G f ↔ ∀ g x, f (shift g x) = shift g (f x) := by
  constructor
  · exact fun hf => hf.shift_comm
  · intro hshift
    refine ⟨G, inferInstance, id, fun p => f p 1, ?_⟩
    funext x g
    rw [apply_eq_apply_one_shift f hshift x g]
    rfl

end CategoricalCellularAutomataProofs
