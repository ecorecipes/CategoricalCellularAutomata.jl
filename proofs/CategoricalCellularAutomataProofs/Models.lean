import CategoricalCellularAutomataProofs.Spaces
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Maps between models

A model on a space (cells `X`, each reading its neighbours in slot order) is a set of cell
states `A` with a rule `μ t c : List A → A` for each time `t` and cell `c` (a rule drawing
counter-based random numbers keyed by cell and step is such a family). A map of models
`M → N` is a map of cell states `h : M.A → N.A` that commutes with the rules: the next state
of `M`, mapped by `h`, is the next state of `N` from the mapped neighbours, at every time and
cell. It forgets what does not feed back (a lineage label carried along, the colours of the
immigration game), and it sends every run of `M` to the run of `N` from the mapped initial
state (`ModelMap.run_map`).

The package's `ModelMap(dom, codom, h)` is such a map (its parameter map is absorbed here into
the rules, which are the models' rules at given parameters), `is_model_map` checks the
commuting condition on every local configuration, and `pushforward(f, prob)` maps a problem.
Models and their maps form a category, and pulling back along a map of spaces is a functor
between the categories of models on the two spaces (`SpaceMap.pullFunctor`): maps of models
and maps of spaces commute.
-/

namespace CategoricalCellularAutomataProofs

open CategoryTheory

universe u

variable {X Y : Type u}

/-- A model on the cells `X`: cell states and a time- and cell-dependent rule. -/
structure CAModel (X : Type u) where
  /-- the cell states -/
  A : Type u
  /-- the rule at time `t` and cell `c`, reading the neighbours' states in slot order -/
  μ : ℕ → X → List A → A

/-- A map of models: a map of cell states commuting with the rules. -/
@[ext]
structure ModelMap (M N : CAModel X) where
  /-- the map of cell states, applied cell by cell -/
  h : M.A → N.A
  /-- the next state, mapped, is the next state from the mapped neighbours -/
  comm : ∀ t c l, h (M.μ t c l) = N.μ t c (l.map h)

variable {nbrs : X → List X}

/-- One step of the codomain from a mapped configuration is the mapped step. -/
theorem ModelMap.step_map {M N : CAModel X} (f : ModelMap M N) (t : ℕ) (x : X → M.A) :
    step nbrs (N.μ t) (f.h ∘ x) = f.h ∘ step nbrs (M.μ t) x := by
  funext c
  simp only [step, Function.comp_apply, f.comm, List.map_map]

/-- **Maps of models send runs to runs.** The run of the codomain from the mapped initial
state is, at every step, the run of the domain mapped cell by cell. -/
theorem ModelMap.run_map {M N : CAModel X} (f : ModelMap M N) (x : X → M.A) (n : ℕ) :
    run nbrs N.μ (f.h ∘ x) n = f.h ∘ run nbrs M.μ x n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, ih, ModelMap.step_map]

/-- The identity map of a model. -/
def ModelMap.id (M : CAModel X) : ModelMap M M where
  h a := a
  comm t c l := by simp

/-- A map of models followed by another. -/
def ModelMap.comp {M N P : CAModel X} (f : ModelMap M N) (g : ModelMap N P) :
    ModelMap M P where
  h := g.h ∘ f.h
  comm t c l := by simp only [Function.comp_apply, f.comm, g.comm, List.map_map]

/-- Models on `X` and the maps between them form a category. -/
instance instCategoryCAModel : Category.{u} (CAModel X) where
  Hom M N := ModelMap M N
  id M := ModelMap.id M
  comp f g := ModelMap.comp f g
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable {nbrsY : Y → List Y} {nbrsX : X → List X}

/-- A model moved along a map of spaces: each cell runs its image's rule on its neighbours in
the image's slot order (`pullback(f, prob; space)`). -/
def SpaceMap.pullModel (f : SpaceMap Y X nbrsY nbrsX) (M : CAModel X) : CAModel Y where
  A := M.A
  μ t := f.pullRule (M.μ t)

/-- A map of models is a map of the models moved along a map of spaces: the slot reordering
moves entries by position, so it commutes with mapping them. -/
def SpaceMap.pullMap (f : SpaceMap Y X nbrsY nbrsX) {M N : CAModel X} (F : ModelMap M N) :
    ModelMap (f.pullModel M) (f.pullModel N) where
  h := F.h
  comm t y l := by
    simp only [SpaceMap.pullModel, SpaceMap.pullRule, F.comm, f.ρ_natural]

/-- **Moving models along a map of spaces is a functor** from the models on `X` to the models
on `Y`: maps of models and maps of spaces commute. -/
def SpaceMap.pullFunctor (f : SpaceMap Y X nbrsY nbrsX) : CAModel X ⥤ CAModel Y where
  obj := f.pullModel
  map F := f.pullMap F
  map_id _ := rfl
  map_comp _ _ := rfl

end CategoricalCellularAutomataProofs
