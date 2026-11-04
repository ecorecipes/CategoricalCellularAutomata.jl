import CategoricalCellularAutomataProofs.Category
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Tactic.Ring

/-!
# Linear cellular automata and the group algebra

A linear cellular automaton with coefficients `a_s` maps `x` to
`τ(x)(g) = Σ_s a_s x(s g)` (`LinearCA(G, coefficients; p)`, over `GF(p)`). The package composes
linear automata and takes their powers through their coefficients, as elements of the group
algebra, instead of composing local rules: `compose(L, M)` (first `L`, then `M`) has the
coefficients of the product `L * M`. This file proves that this is right, over any commutative
semiring and any group: running `a` and then `b` is the linear automaton of `a * b`, the unit
of the algebra is the identity, and a linear automaton is a cellular automaton whose memory
set is the support of its coefficients.
-/

namespace CategoricalCellularAutomataProofs

universe u

variable {G : Type u} [Monoid G] {R : Type u} [CommSemiring R]

/-- The linear cellular automaton with coefficients `a`: `τ(x)(g) = Σ_s a_s x(s g)`. -/
noncomputable def linCA (a : G →₀ R) (x : Config G R) : Config G R :=
  fun g => a.sum fun s r => r * x (s * g)

theorem linCA_apply (a : G →₀ R) (x : Config G R) (g : G) :
    linCA a x g = a.sum fun s r => r * x (s * g) := rfl

/-- The convolution of coefficients, `(a ⋆ b)_u = Σ_{s t = u} a_s b_t`: the product of the
group algebra (`MonoidAlgebra.mul_def`). -/
noncomputable def conv (a b : G →₀ R) : G →₀ R :=
  a.sum fun s r => b.sum fun t r' => Finsupp.single (s * t) (r * r')

/-- Running `a` and then `b` is the linear automaton of their convolution. -/
theorem linCA_conv (a b : G →₀ R) (x : Config G R) :
    linCA b (linCA a x) = linCA (conv a b) x := by
  funext g
  simp only [linCA_apply, conv]
  rw [Finsupp.sum_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  have h1 : ∀ s r, ((b.sum fun t r' => Finsupp.single (s * t) (r * r')).sum
      fun u r => r * x (u * g)) = b.sum fun t r' => r * r' * x (s * t * g) := by
    intro s r
    rw [Finsupp.sum_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    exact Finsupp.sum_congr fun t _ => Finsupp.sum_single_index (zero_mul _)
  simp only [h1, Finsupp.mul_sum]
  rw [Finsupp.sum_comm]
  refine Finsupp.sum_congr fun s _ => Finsupp.sum_congr fun t _ => ?_
  rw [mul_assoc s t g]; ring

/-- The product of the group algebra is the convolution of coefficients. -/
theorem monoidAlgebra_mul_eq_conv (a b : MonoidAlgebra R G) :
    (a * b : MonoidAlgebra R G) = (conv a b : G →₀ R) := by
  rw [MonoidAlgebra.mul_def]; rfl

/-- **Composition through the coefficients.** Running `a` and then `b` is the linear automaton
of the product `a * b` in the group algebra (`compose(L, M)`). -/
theorem linCA_mul (a b : MonoidAlgebra R G) (x : Config G R) :
    linCA b (linCA a x) = linCA (a * b : MonoidAlgebra R G) x := by
  rw [linCA_conv, monoidAlgebra_mul_eq_conv]

/-- The unit of the group algebra is the identity automaton. -/
theorem linCA_one (x : Config G R) : linCA (1 : MonoidAlgebra R G) x = x := by
  funext g
  rw [MonoidAlgebra.one_def, linCA_apply, MonoidAlgebra.single, Finsupp.sum_single_index] <;>
    simp

/-- Powers through the coefficients: running `a` `n` times is the linear automaton of `a ^ n`
(`L^n`, computed by repeated squaring of the coefficients). -/
theorem linCA_pow (a : MonoidAlgebra R G) (n : ℕ) (x : Config G R) :
    (linCA a)^[n] x = linCA (a ^ n : MonoidAlgebra R G) x := by
  induction n generalizing x with
  | zero => simp [linCA_one]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, linCA_mul, ← pow_succ]

/-- A linear automaton is a cellular automaton (`CellularAutomaton(L)`): its memory set is the
support of its coefficients and its local rule the weighted sum. -/
theorem isCA_linCA (a : G →₀ R) : IsCA G (linCA a) := by
  classical
  refine ⟨a.support, inferInstance, fun s => s.1,
    fun p => ∑ s : a.support, a s.1 * p s, ?_⟩
  funext x g
  simp only [linCA_apply, ca_apply, Finsupp.sum]
  exact (Finset.sum_coe_sort a.support (fun s => a s * x (s * g))).symm

end CategoricalCellularAutomataProofs
