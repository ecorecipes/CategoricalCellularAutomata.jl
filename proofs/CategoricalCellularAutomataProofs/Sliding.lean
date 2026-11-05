import CategoricalCellularAutomataProofs.Models
import CategoricalCellularAutomataProofs.CurtisHedlundLyndon
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Maps between models that read neighbours

A `ModelMap` sends the state of a cell to a state. A sliding map reads a finite window around
the cell, so it can see what lies between cells, such as a boundary between two regions. Here it is
a map of configurations `Φ` whose value at a cell depends only on the configuration on a finite
window of that cell, and it is a map of models when it commutes with the steps of the two models.
On a lattice these are the sliding block codes of symbolic dynamics, the package's
`SlidingBlockMap`.

A sliding map sends every run to a run (`SlidingMap.run_map`). The windows of a composite are
found by reading each window through the other, so sliding maps form a category
(`SlidingModels`), and cell-by-cell maps are a subcategory (`ModelMap.slidingFunctor`) that misses
some of them (`kinkMap126_not_cellwise`).

A rule is a family `μ t c` in the time and the cell, so counter-based random numbers are covered.
A rule of the codomain may depend on the numbers of cells other than its own, as it must when the
window holds several cells: in `wallsMap`, the boundaries of a voter model move on the coins of the
two cells beside them, whichever coins are drawn.

Over a group, a surjective cellular automaton `Φ` has a cellular automaton `F'` with
`F' ∘ Φ = Φ ∘ F` exactly when `F` respects the fibres of `Φ`, and then `F'` is unique
(`factor_exists_iff`, `factor_unique`, `factor_isCA`); over a finite group that follows from the
Curtis–Hedlund–Lyndon theorem.
-/

namespace CategoricalCellularAutomataProofs

open CategoryTheory

universe u

variable {X : Type u}

/-- A map of models that reads a window: a map of configurations, each of whose values depends only
on the configuration on a finite window of the cell, commuting with the steps of the two models. -/
@[ext]
structure SlidingMap (nbrs : X → List X) (M N : CAModel X) where
  /-- the map of configurations -/
  Φ : (X → M.A) → X → N.A
  /-- each value reads a finite window -/
  reads : ∃ w : X → List X, ∀ c x y, (∀ d ∈ w c, x d = y d) → Φ x c = Φ y c
  /-- one step followed by the map is the map followed by one step -/
  comm : ∀ t x, Φ (step nbrs (M.μ t) x) = step nbrs (N.μ t) (Φ x)

variable {nbrs : X → List X}

/-- **Sliding maps send runs to runs.** The run of the codomain from the mapped initial state is,
at every step, the run of the domain mapped. -/
theorem SlidingMap.run_map {M N : CAModel X} (f : SlidingMap nbrs M N) (x : X → M.A) (n : ℕ) :
    run nbrs N.μ (f.Φ x) n = f.Φ (run nbrs M.μ x n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, ih, f.comm]

/-- The identity reads the cell alone. -/
def SlidingMap.id (M : CAModel X) : SlidingMap nbrs M M where
  Φ x := x
  reads := ⟨fun c => [c], fun c x y e => e c (by simp)⟩
  comm _ _ := rfl

/-- A sliding map followed by another reads each window of the second through the first. -/
def SlidingMap.comp {M N P : CAModel X} (f : SlidingMap nbrs M N) (g : SlidingMap nbrs N P) :
    SlidingMap nbrs M P where
  Φ x := g.Φ (f.Φ x)
  reads := by
    obtain ⟨wf, hf⟩ := f.reads
    obtain ⟨wg, hg⟩ := g.reads
    refine ⟨fun c => (wg c).flatMap wf, fun c x y e => hg c _ _ fun d hd => hf d x y fun b hb => ?_⟩
    exact e b (List.mem_flatMap.mpr ⟨d, hd, hb⟩)
  comm t x := by rw [f.comm, g.comm]

/-- The models on a space with its neighbours, for the category of sliding maps. -/
structure SlidingModels (nbrs : X → List X) where
  /-- the model -/
  model : CAModel X

/-- **Models and the sliding maps between them form a category.** -/
instance instCategorySlidingModels : Category.{u} (SlidingModels nbrs) where
  Hom M N := SlidingMap nbrs M.model N.model
  id M := SlidingMap.id M.model
  comp f g := SlidingMap.comp f g
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- A map of cell states is a sliding map, with a window of the cell alone. -/
def ModelMap.toSliding {M N : CAModel X} (f : ModelMap M N) : SlidingMap nbrs M N where
  Φ x := f.h ∘ x
  reads := ⟨fun c => [c], fun c x y e => by simp [e c (by simp)]⟩
  comm t x := (f.step_map t x).symm

/-- **Cell-by-cell maps are a subcategory of sliding maps.** -/
def ModelMap.slidingFunctor : CAModel X ⥤ SlidingModels nbrs where
  obj M := ⟨M⟩
  map f := ModelMap.toSliding f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Over a nonempty space, different maps of cell states are different sliding maps. -/
theorem ModelMap.toSliding_injective [Nonempty X] {M N : CAModel X} {f g : ModelMap M N}
    (e : (ModelMap.toSliding f : SlidingMap nbrs M N) = ModelMap.toSliding g) : f = g := by
  obtain ⟨c⟩ := ‹Nonempty X›
  ext a
  have := congrArg (fun F : SlidingMap nbrs M N => F.Φ (fun _ => a) c) e
  exact this

/-! ## Examples on a ring -/

section Ring

variable (n : ℕ)

/-- A ring of cells, each reading the cell before it, itself and the cell after it. -/
def ringNbrs : ZMod n → List (ZMod n) := fun c => [c - 1, c, c + 1]

/-- An elementary cellular automaton on the ring, whose rule may depend on the time and cell. -/
def ringModel (r : ℕ → ZMod n → Bool → Bool → Bool → Bool) : CAModel (ZMod n) where
  A := Bool
  μ t c l := match l with
    | [a, b, d] => r t c a b d
    | _ => false

variable {n}

/-- Whether a boundary lies between a cell and the next. -/
def kink (x : ZMod n → Bool) (c : ZMod n) : Bool := xor (x c) (x (c + 1))

theorem kink_reads : ∃ w : ZMod n → List (ZMod n), ∀ c x y, (∀ d ∈ w c, x d = y d) →
    kink x c = kink y c :=
  ⟨fun c => [c, c + 1], fun c x y e => by simp [kink, e c (by simp), e (c + 1) (by simp)]⟩

/-- Elementary rule 126: a cell is on unless it and its neighbours agree. -/
def rule126 (_ : ℕ) (_ : ZMod n) (a b d : Bool) : Bool := !(a == b && b == d)

/-- Elementary rule 18: a cell that is off turns on when exactly one neighbour is on. -/
def rule18 (_ : ℕ) (_ : ZMod n) (a b d : Bool) : Bool := !b && xor a d

/-- **The boundaries of rule 126 are rule 18.** -/
def kinkMap126 : SlidingMap (ringNbrs n) (ringModel n rule126) (ringModel n rule18) where
  Φ := kink
  reads := kink_reads
  comm t x := by
    funext c
    simp only [step, ringNbrs, ringModel, List.map, kink, rule126, rule18, sub_add_cancel,
      add_sub_cancel_right]
    cases x (c - 1) <;> cases x c <;> cases x (c + 1) <;> cases x (c + 1 + 1) <;> rfl

/-- **A sliding map need not be cell by cell.** Two cells in the same state can have different
boundaries beside them. -/
theorem kinkMap126_not_cellwise [Fact (1 < n)] :
    ¬ ∃ h : Bool → Bool, ∀ (x : ZMod n → Bool) c, (kinkMap126 (n := n)).Φ x c = h (x c) := by
  rintro ⟨h, hh⟩
  have zero := hh (fun _ => false) 0
  have one := hh (fun c => decide (c = 1)) 0
  have ne : (0 : ZMod n) ≠ 1 := zero_ne_one
  simp [kinkMap126, kink, ne] at zero one
  rw [← zero] at one
  exact Bool.noConfusion one

/-- A voter model with any field of coins: a cell copies the cell before it on `true` and the cell
after it on `false`. A random draw at each cell and step is such a field. -/
def voterRule (coin : ℕ → ZMod n → Bool) (t : ℕ) (c : ZMod n) (a _ d : Bool) : Bool :=
  if coin t c then a else d

/-- The boundaries of the voter model, moved by the coins of the cells on either side. -/
def wallRule (coin : ℕ → ZMod n → Bool) (t : ℕ) (c : ZMod n) (a b d : Bool) : Bool :=
  match coin t c, coin t (c + 1) with
  | true, true => a
  | false, false => d
  | true, false => xor (xor a b) d
  | false, true => b

/-- **The boundaries between two species that compete by copying move on the coins of the two cells
beside them**, on every path, whichever coins are drawn. By `walls_need_other_coins`, no rule that
reads only its own cell's coin could do this. -/
def wallsMap (coin : ℕ → ZMod n → Bool) :
    SlidingMap (ringNbrs n) (ringModel n (voterRule coin)) (ringModel n (wallRule coin)) where
  Φ := kink
  reads := kink_reads
  comm t x := by
    funext c
    simp only [step, ringNbrs, ringModel, List.map, kink, voterRule, wallRule, sub_add_cancel,
      add_sub_cancel_right]
    cases coin t c <;> cases coin t (c + 1) <;> cases x (c - 1) <;> cases x c <;>
      cases x (c + 1) <;> cases x (c + 1 + 1) <;> rfl

/-- **A map that reads a window needs the random numbers of the window.** No rule of the boundaries
that reads the three boundaries around a cell and only that cell's coin gives their next state: on
a ring of at least four cells, the next boundary also depends on the coin of the next cell. -/
theorem walls_need_other_coins [hn : Fact (3 < n)] :
    ¬ ∃ r : ZMod n → Bool → Bool → Bool → Bool → Bool,
      ∀ (coin : ℕ → ZMod n → Bool) (x : ZMod n → Bool) (c : ZMod n),
        kink (step (ringNbrs n) ((ringModel n (voterRule coin)).μ 0) x) c =
          r c (coin 0 c) (kink x (c - 1)) (kink x c) (kink x (c + 1)) := by
  rintro ⟨r, hr⟩
  have nonzero : ∀ k : ℕ, 0 < k → k ≤ 3 → (k : ZMod n) ≠ 0 := fun k k0 k3 e => by
    have := (ZMod.natCast_eq_zero_iff k n).mp e
    have := Nat.le_of_dvd k0 this
    have := hn.out
    omega
  have one : (1 : ZMod n) ≠ 0 := by simpa using nonzero 1 (by omega) (by omega)
  have two : (2 : ZMod n) ≠ 0 := by simpa using nonzero 2 (by omega) (by omega)
  have three : (3 : ZMod n) ≠ 0 := by simpa using nonzero 3 (by omega) (by omega)
  have m1 : (-1 : ZMod n) ≠ 1 := fun e => two (by linear_combination -e)
  have m2 : (-1 : ZMod n) ≠ 2 := fun e => three (by linear_combination -e)
  have n12 : (1 : ZMod n) ≠ 2 := fun e => one (by linear_combination -e)
  let x : ZMod n → Bool := fun c => decide (c = 1) || decide (c = 2)
  have both := hr (fun _ d => decide (d = 0) || decide (d = 1)) x 0
  have only := hr (fun _ d => decide (d = 0)) x 0
  have hx : ∀ c, x c = (decide (c = 1) || decide (c = 2)) := fun _ => rfl
  simp [step, ringNbrs, ringModel, voterRule, kink, hx, one, one.symm, two.symm, m1, m2, n12,
    n12.symm, one_add_one_eq_two, zero_sub] at both only
  rw [both] at only
  simp at only

end Ring

/-! ## Factors -/

section Factor

variable {S T : Type*}

/-- A map through a surjection exists exactly when the map respects its fibres. -/
theorem factor_exists_iff {Φ : S → T} (hs : Function.Surjective Φ) (F : S → S) :
    (∃ F' : T → T, ∀ x, F' (Φ x) = Φ (F x)) ↔ ∀ x y, Φ x = Φ y → Φ (F x) = Φ (F y) := by
  constructor
  · rintro ⟨F', h⟩ x y e
    rw [← h, ← h, e]
  · intro h
    choose s hs using hs
    refine ⟨fun y => Φ (F (s y)), fun x => h _ _ (hs _)⟩

/-- A map through a surjection is unique. -/
theorem factor_unique {Φ : S → T} (hs : Function.Surjective Φ) {F : S → S} {F₁ F₂ : T → T}
    (h₁ : ∀ x, F₁ (Φ x) = Φ (F x)) (h₂ : ∀ x, F₂ (Φ x) = Φ (F x)) : F₁ = F₂ := by
  funext y
  obtain ⟨x, rfl⟩ := hs y
  rw [h₁, h₂]

variable {G : Type u} [Group G] {A B : Type u}

/-- **The factor of a cellular automaton by a surjective one is a cellular automaton**, over a finite
group: a map on the codomain that commutes with both commutes with the shifts. -/
theorem factor_isCA [Finite G] {Φ : Config G A → Config G B} (hΦ : IsCA G Φ)
    (hs : Function.Surjective Φ) {F : Config G A → Config G A} (hF : IsCA G F)
    {F' : Config G B → Config G B} (h : ∀ x, F' (Φ x) = Φ (F x)) : IsCA G F' := by
  rw [isCA_iff_shift_comm]
  intro g y
  obtain ⟨x, rfl⟩ := hs y
  rw [← hΦ.shift_comm, h, hF.shift_comm, hΦ.shift_comm, h]

end Factor

end CategoricalCellularAutomataProofs
