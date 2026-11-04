import CategoricalCellularAutomataProofs.CellularAutomata
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sum

/-!
# The cartesian category of cellular automata over a group

The package makes the cellular automata over a group `G` a Catlab instance of
`ThCartesianCategory`: the objects are full shifts `A^G` (one for each alphabet `A`), the
morphisms are cellular automata, composition is `compose`, the product of `A^G` and `B^G` is
`(A × B)^G` (`otimes`), with `proj1`, `proj2` and `pair`, and the unit `munit()` is the
one-letter alphabet.

Here the category is built in Mathlib: an object is an alphabet, a morphism is a map of
configurations that *is* a cellular automaton (has a finite memory set and a local rule), and
Mathlib's `CartesianMonoidalCategory.ofChosenFiniteProducts` turns the terminal object and the
binary products into the cartesian monoidal structure, with all its coherence laws (the
associator, unitors and braiding are then the ones the package's strict products realise).
-/

namespace CategoricalCellularAutomataProofs

open CategoryTheory Limits

universe u

variable (G : Type u) [Monoid G]

/-- A map of configurations is a cellular automaton when it has a finite memory set `S` and
a local rule `μ`. -/
def IsCA {A B : Type u} (f : Config G A → Config G B) : Prop :=
  ∃ (I : Type u) (_ : Finite I) (S : I → G) (μ : (I → A) → B), f = ca S μ

variable {G}

theorem isCA_ca {A B : Type u} {I : Type u} [Finite I] (S : I → G) (μ : (I → A) → B) :
    IsCA G (ca S μ) :=
  ⟨I, inferInstance, S, μ, rfl⟩

theorem isCA_id (A : Type u) : IsCA G (id : Config G A → Config G A) :=
  ⟨PUnit, inferInstance, fun _ => 1, fun p => p PUnit.unit, by funext x g; simp [ca]⟩

theorem isCA_comp {A B C : Type u} {f : Config G A → Config G B} {g : Config G B → Config G C}
    (hf : IsCA G f) (hg : IsCA G g) : IsCA G (g ∘ f) := by
  obtain ⟨J, _, T, ν, rfl⟩ := hf
  obtain ⟨I, _, S, μ, rfl⟩ := hg
  refine ⟨I × J, inferInstance, fun p => T p.2 * S p.1,
    fun q => μ (fun i => ν (fun j => q (i, j))), ?_⟩
  funext x
  exact ca_comp S μ T ν x

/-- A cellular automaton is equivariant: it commutes with every shift. -/
theorem IsCA.shift_comm {A B : Type u} {f : Config G A → Config G B} (hf : IsCA G f) (g : G)
    (x : Config G A) : f (shift g x) = shift g (f x) := by
  obtain ⟨I, _, S, μ, rfl⟩ := hf
  exact ca_shift S μ g x

/-- An alphabet, as an object of the category of cellular automata over `G` (the full shift
`A^G`). The group is a parameter of the type, so each group has its own category. -/
@[nolint unusedArguments]
structure CAObj (G : Type u) [Monoid G] where
  /-- the alphabet -/
  α : Type u

/-- The category of cellular automata over `G`: morphisms are the maps of configurations that
are cellular automata, composed as maps. -/
instance : Category (CAObj G) where
  Hom X Y := { f : Config G X.α → Config G Y.α // IsCA G f }
  id X := ⟨id, isCA_id X.α⟩
  comp f g := ⟨g.1 ∘ f.1, isCA_comp f.2 g.2⟩

@[ext] theorem CAObj.hom_ext {X Y : CAObj G} {f g : X ⟶ Y} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

@[simp] theorem CAObj.id_val (X : CAObj G) : (𝟙 X : X ⟶ X).1 = id := rfl

@[simp] theorem CAObj.comp_val {X Y Z : CAObj G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = g.1 ∘ f.1 := rfl

/-- The one-letter alphabet, the unit `munit()`. -/
def unitObj : CAObj G := ⟨PUnit⟩

/-- The product alphabet `A × B` (`otimes`). -/
def prodObj (X Y : CAObj G) : CAObj G := ⟨X.α × Y.α⟩

/-- The first projection `proj1`: memory set `{1}`, rule `fst`. -/
def fstHom (X Y : CAObj G) : prodObj X Y ⟶ X :=
  ⟨ca (fun _ : PUnit => 1) (fun p => (p PUnit.unit).1), isCA_ca _ _⟩

/-- The second projection `proj2`: memory set `{1}`, rule `snd`. -/
def sndHom (X Y : CAObj G) : prodObj X Y ⟶ Y :=
  ⟨ca (fun _ : PUnit => 1) (fun p => (p PUnit.unit).2), isCA_ca _ _⟩

@[simp] theorem fstHom_apply (X Y : CAObj G) (x : Config G (X.α × Y.α)) (g : G) :
    (fstHom X Y).1 x g = (x g).1 := by
  simp [fstHom, ca]

@[simp] theorem sndHom_apply (X Y : CAObj G) (x : Config G (X.α × Y.α)) (g : G) :
    (sndHom X Y).1 x g = (x g).2 := by
  simp [sndHom, ca]

/-- The pairing `pair(f, g)` of two cellular automata is a cellular automaton (over the
disjoint union of their memory sets). -/
def pairHom {W X Y : CAObj G} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ prodObj X Y :=
  ⟨fun x h => (f.1 x h, g.1 x h), by
    obtain ⟨I, _, S, μ, hS⟩ := f.2
    obtain ⟨J, _, T, ν, hT⟩ := g.2
    refine ⟨I ⊕ J, inferInstance, Sum.elim S T,
      fun p => (μ (fun i => p (Sum.inl i)), ν (fun j => p (Sum.inr j))), ?_⟩
    funext x h
    rw [hS, hT]
    exact (ca_pair S μ T ν x h).symm⟩

/-- The product cone: `(A × B)^G` with its projections is a product of `A^G` and `B^G`. -/
def prodIsLimit (X Y : CAObj G) : IsLimit (BinaryFan.mk (fstHom X Y) (sndHom X Y)) :=
  BinaryFan.IsLimit.mk _ (fun f g => pairHom f g)
    (fun f g => by ext x h; simp [pairHom])
    (fun f g => by ext x h; simp [pairHom])
    (fun f g m h₁ h₂ => by
      ext x h
      have e₁ := congrFun (congrFun (congrArg Subtype.val h₁) x) h
      have e₂ := congrFun (congrFun (congrArg Subtype.val h₂) x) h
      simp only [CAObj.comp_val, Function.comp_apply, BinaryFan.mk_fst, BinaryFan.mk_snd,
        fstHom_apply, sndHom_apply] at e₁ e₂
      show m.1 x h = (f.1 x h, g.1 x h)
      exact Prod.ext e₁ e₂)

/-- The one-letter alphabet is terminal: the only map into it is a cellular automaton with an
empty memory set. -/
def unitIsTerminal : IsTerminal (unitObj : CAObj G) :=
  IsTerminal.ofUniqueHom
    (fun X => ⟨fun _ _ => PUnit.unit, ⟨PEmpty, inferInstance, PEmpty.elim,
      fun _ => PUnit.unit, rfl⟩⟩)
    (fun X m => by ext x h; rfl)

/-- **The cartesian category CA(G).** The cellular automata over `G` form a cartesian monoidal
category, with the product of alphabets as the monoidal product and the one-letter alphabet as
its unit: the structure the package's Catlab instance of `ThCartesianCategory` asserts. -/
instance : CartesianMonoidalCategory (CAObj G) :=
  .ofChosenFiniteProducts ⟨_, unitIsTerminal⟩ (fun X Y => ⟨_, prodIsLimit X Y⟩)

end CategoricalCellularAutomataProofs
