import CategoricalCellularAutomataProofs.Models

/-!
# Quotients of models, with and without callbacks

A lumping of a model `M` is a map of cell states `h : M.A → B` with a section `s`
(`h (s b) = b`): a way to forget something, and a way to fill it back in. The package's
`quotient(model, h, section)` builds the quotient model from `M`'s own rule: lift the
neighbours with `s`, apply the rule, and map the result down with `h`.

That rule exists for every lumping. It makes `h` a map of models exactly when the next state,
mapped by `h`, does not depend on what `h` forgets (`Lumping.Descends`), and then it is the only
rule that does, whichever section was used (`Lumping.rule_unique`), and the quotient has the
universal property of a quotient: every map of models that does not distinguish what `h` forgets
factors through it, uniquely (`Lumping.lift_comp`, `Lumping.lift_unique`).

A callback acts on the whole configuration, not cell by cell, and runs after each step. It
lifts in the same way, `y ↦ h ∘ κ (s ∘ y)`, under the same kind of condition
(`Lumping.CallbackDescends`). With both conditions the quotient, with its lifted callback, runs
every run of the original mapped by `h` (`Lumping.runWith_quotient`). The package's
`pushforward(f, prob; callback=:lift)` is this construction.

The last theorem says what erasing a layer after every step can show. If `h` forgets without
feedback, the erased run agrees with the original on everything kept (`Lumping.erased_run`). So a
difference between the two disproves the map; agreement on one problem does not prove it.
-/

namespace CategoricalCellularAutomataProofs

open CategoryTheory

universe u

variable {X : Type u} {nbrs : X → List X}

/-- The run of a time-dependent rule with a callback: each step applies the rule, then the
callback `κ n` to the whole configuration. -/
def runWith {A : Type u} (nbrs : X → List X) (μ : ℕ → X → List A → A)
    (κ : ℕ → (X → A) → X → A) (x : X → A) : ℕ → X → A
  | 0 => x
  | n + 1 => κ n (step nbrs (μ n) (runWith nbrs μ κ x n))

/-- A map of models that commutes with two callbacks sends runs with the first to runs with the
second. -/
theorem ModelMap.runWith_map {M N : CAModel X} (F : ModelMap M N)
    (κM : ℕ → (X → M.A) → X → M.A) (κN : ℕ → (X → N.A) → X → N.A)
    (hκ : ∀ n x, F.h ∘ κM n x = κN n (F.h ∘ x)) (x : X → M.A) (n : ℕ) :
    runWith nbrs N.μ κN (F.h ∘ x) n = F.h ∘ runWith nbrs M.μ κM x n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [runWith, ih, ModelMap.step_map, hκ]

/-- A way to forget something about cell states of `M`, and to fill it back in. -/
structure Lumping (M : CAModel X) (B : Type u) where
  /-- the map of cell states -/
  h : M.A → B
  /-- the lift of a cell state -/
  s : B → M.A
  /-- lifting and mapping down changes nothing -/
  h_s : ∀ b, h (s b) = b

namespace Lumping

variable {M N : CAModel X} {B : Type u} (q : Lumping M B)

theorem h_comp_s : q.h ∘ q.s = _root_.id := funext q.h_s

theorem map_h_map_s (l : List B) : (l.map q.s).map q.h = l := by
  rw [List.map_map, q.h_comp_s, List.map_id]

/-- The quotient model: lift the neighbours, apply `M`'s rule, map the result down. -/
def model : CAModel X where
  A := B
  μ t c l := q.h (M.μ t c (l.map q.s))

/-- The next state, mapped by `h`, does not depend on what `h` forgets. -/
def Descends : Prop :=
  ∀ t c (l l' : List M.A), l.map q.h = l'.map q.h → q.h (M.μ t c l) = q.h (M.μ t c l')

/-- When the dynamics do not depend on what is forgotten, `h` is a map onto the quotient. -/
def map (hd : q.Descends) : ModelMap M q.model where
  h := q.h
  comm t c l := hd t c l ((l.map q.h).map q.s) (q.map_h_map_s _).symm

/-- **Any rule that `h` commutes with is the quotient's**, whichever section was used. -/
theorem rule_unique {μ' : ℕ → X → List B → B}
    (comm : ∀ t c l, q.h (M.μ t c l) = μ' t c (l.map q.h)) : μ' = q.model.μ := by
  funext t c l
  show μ' t c l = q.h (M.μ t c (l.map q.s))
  rw [comm, q.map_h_map_s]

/-- **`h` commutes with some rule exactly when the dynamics do not depend on what it forgets.**
This is what `is_model_map` tests for a quotient. -/
theorem descends_iff_exists_rule :
    q.Descends ↔ ∃ μ' : ℕ → X → List B → B, ∀ t c l, q.h (M.μ t c l) = μ' t c (l.map q.h) := by
  constructor
  · intro hd
    exact ⟨q.model.μ, (q.map hd).comm⟩
  · rintro ⟨μ', comm⟩ t c l l' e
    rw [comm, comm, e]

/-- Two sections of the same map give the same quotient rule. -/
theorem rule_eq_of_section (q' : Lumping M B) (hh : q'.h = q.h) (hd : q.Descends) :
    q'.model.μ = q.model.μ := by
  apply q.rule_unique
  intro t c l
  have e : l.map q.h = ((l.map q.h).map q'.s).map q.h := by
    have := q'.map_h_map_s (l.map q.h)
    rw [hh] at this
    exact this.symm
  show q.h (M.μ t c l) = q'.h (M.μ t c ((l.map q.h).map q'.s))
  rw [hh]
  exact hd t c _ _ e

/-- The map out of the quotient induced by a map of models that does not distinguish what `h`
forgets. -/
def lift (F : ModelMap M N) (hF : ∀ a a', q.h a = q.h a' → F.h a = F.h a') :
    ModelMap q.model N where
  h b := F.h (q.s b)
  comm t c l := by
    show F.h (q.s (q.h (M.μ t c (l.map q.s)))) = N.μ t c (l.map fun b => F.h (q.s b))
    rw [hF _ _ (q.h_s _), F.comm, List.map_map]
    rfl

/-- **Universal property, existence.** The map factors through the quotient. -/
theorem lift_comp (hd : q.Descends) (F : ModelMap M N)
    (hF : ∀ a a', q.h a = q.h a' → F.h a = F.h a') :
    (q.map hd).comp (q.lift F hF) = F := by
  apply ModelMap.ext
  funext a
  exact hF _ _ (q.h_s _)

/-- **Universal property, uniqueness.** The factorisation is the only one. -/
theorem lift_unique (hd : q.Descends) (F : ModelMap M N)
    (hF : ∀ a a', q.h a = q.h a' → F.h a = F.h a') (G : ModelMap q.model N)
    (hG : (q.map hd).comp G = F) : G = q.lift F hF := by
  apply ModelMap.ext
  funext b
  have e : F.h (q.s b) = G.h (q.h (q.s b)) := by rw [← hG]; rfl
  show G.h b = F.h (q.s b)
  rw [e, q.h_s]

/-- The callback of the quotient: lift the configuration, apply the callback, map down. -/
def liftCallback (κ : ℕ → (X → M.A) → X → M.A) : ℕ → (X → B) → X → B :=
  fun n y => q.h ∘ κ n (q.s ∘ y)

/-- What a callback leaves, mapped by `h`, does not depend on what `h` forgets. -/
def CallbackDescends (κ : ℕ → (X → M.A) → X → M.A) : Prop :=
  ∀ n (x x' : X → M.A), q.h ∘ x = q.h ∘ x' → q.h ∘ κ n x = q.h ∘ κ n x'

theorem h_comp_s_comp (y : X → B) : q.h ∘ (q.s ∘ y) = y := by
  funext c
  exact q.h_s (y c)

/-- When the callback does not depend on what is forgotten, `h` commutes with the lifted
callback. -/
theorem liftCallback_comm {κ : ℕ → (X → M.A) → X → M.A} (hκ : q.CallbackDescends κ) (n : ℕ)
    (x : X → M.A) : q.h ∘ κ n x = q.liftCallback κ n (q.h ∘ x) :=
  hκ n x (q.s ∘ (q.h ∘ x)) (q.h_comp_s_comp (q.h ∘ x)).symm

/-- **`h` commutes with some callback exactly when the callback does not depend on what it
forgets.** -/
theorem callbackDescends_iff_exists {κ : ℕ → (X → M.A) → X → M.A} :
    q.CallbackDescends κ ↔
      ∃ κ' : ℕ → (X → B) → X → B, ∀ n x, q.h ∘ κ n x = κ' n (q.h ∘ x) := by
  constructor
  · intro hκ
    exact ⟨q.liftCallback κ, q.liftCallback_comm hκ⟩
  · rintro ⟨κ', comm⟩ n x x' e
    rw [comm, comm, e]

/-- **Any callback that `h` commutes with is the lifted one.** -/
theorem callback_unique {κ : ℕ → (X → M.A) → X → M.A} {κ' : ℕ → (X → B) → X → B}
    (comm : ∀ n x, q.h ∘ κ n x = κ' n (q.h ∘ x)) : κ' = q.liftCallback κ := by
  funext n y
  show κ' n y = q.h ∘ κ n (q.s ∘ y)
  rw [comm, q.h_comp_s_comp]

/-- **The quotient with its lifted callback runs every run of the original, mapped by `h`.** -/
theorem runWith_quotient (hd : q.Descends) {κ : ℕ → (X → M.A) → X → M.A}
    (hκ : q.CallbackDescends κ) (x : X → M.A) (n : ℕ) :
    runWith nbrs q.model.μ (q.liftCallback κ) (q.h ∘ x) n = q.h ∘ runWith nbrs M.μ κ x n :=
  (q.map hd).runWith_map κ (q.liftCallback κ) (q.liftCallback_comm hκ) x n

/-- One step from configurations that `h` does not distinguish gives results it does not
distinguish, when the rule does not depend on what it forgets. -/
theorem step_congr (hd : q.Descends) (t : ℕ) {x y : X → M.A} (e : q.h ∘ x = q.h ∘ y) :
    q.h ∘ step nbrs (M.μ t) x = q.h ∘ step nbrs (M.μ t) y := by
  funext c
  refine hd t c _ _ ?_
  simp only [List.map_map, e]

/-- **What erasing shows.** Run with what `h` forgets filled back in by the section after every
step: if neither the rule nor the callback depends on it, everything `h` keeps agrees with the
original run. So a difference disproves the map; agreement on one problem does not prove it. -/
theorem erased_run (hd : q.Descends) {κ : ℕ → (X → M.A) → X → M.A}
    (hκ : q.CallbackDescends κ) (x : X → M.A) (n : ℕ) :
    q.h ∘ runWith nbrs M.μ (fun n y => q.s ∘ (q.h ∘ κ n y)) (q.s ∘ (q.h ∘ x)) n =
      q.h ∘ runWith nbrs M.μ κ x n := by
  induction n with
  | zero => exact q.h_comp_s_comp (q.h ∘ x)
  | succ n ih =>
    simp only [runWith]
    rw [q.h_comp_s_comp]
    exact hκ n _ _ (q.step_congr hd n ih)

end Lumping

end CategoricalCellularAutomataProofs
