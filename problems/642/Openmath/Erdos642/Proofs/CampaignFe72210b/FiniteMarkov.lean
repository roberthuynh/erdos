import Mathlib

/-! Explicit finite real Markov path weights. -/
namespace Erdos642.FiniteMarkov

universe u
variable {V : Type u} [Fintype V]

/-- The future states of a path, in chronological order. -/
def Path (V : Type u) : ℕ → Type u
  | 0 => PUnit.{u + 1}
  | n + 1 => V × Path V n

instance pathFintype (n : ℕ) : Fintype (Path V n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact @instFintypeProd V (Path V n) _ ih

instance pathZeroUnique : Unique (Path V 0) := inferInstanceAs (Unique PUnit)

structure Chain (V : Type*) [Fintype V] where
  transition : Matrix V V ℝ
  nonneg : ∀ x y, 0 ≤ transition x y
  row_sum : ∀ x, ∑ y, transition x y = 1

namespace Chain
variable (C : Chain V)

def weight (C : Chain V) : {n : ℕ} → V → Path V n → ℝ
  | 0, _, _ => 1
  | _ + 1, x, (y, p) => C.transition x y * C.weight y p

def endpoint (C : Chain V) : {n : ℕ} → V → Path V n → V
  | 0, x, _ => x
  | _ + 1, _, (y, p) => C.endpoint y p

 theorem weight_nonneg {n : ℕ} (x : V) (p : Path V n) : 0 ≤ C.weight x p := by
  induction n generalizing x with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (C.nonneg x p.1) (ih p.1 p.2)

 theorem total_weight (n : ℕ) (x : V) : ∑ p : Path V n, C.weight x p = 1 := by
  induction n generalizing x with
  | zero => rw [Fintype.sum_unique]; rfl
  | succ n ih =>
    change ∑ p : V × Path V n, C.transition x p.1 * C.weight p.1 p.2 = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact C.row_sum x

/-- The endpoint marginal of the actual path law is the transition matrix power. -/
theorem endpoint_marginal [DecidableEq V] (n : ℕ) (x y : V) :
    (∑ p : Path V n, if C.endpoint x p = y then C.weight x p else 0) =
      (C.transition ^ n) x y := by
  classical
  induction n generalizing x with
  | zero =>
    rw [Fintype.sum_unique]
    simp only [endpoint, weight, pow_zero, Matrix.one_apply]
    split_ifs <;> simp_all
  | succ n ih =>
    change (∑ p : V × Path V n,
      if C.endpoint p.1 p.2 = y then C.transition x p.1 * C.weight p.1 p.2 else 0) = _
    rw [Fintype.sum_prod_type, pow_succ', Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro z _
    rw [← ih z, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp_all

/-- Concatenation retains chronological order. -/
def append (C : Chain V) : {m n : ℕ} → Path V m → Path V n → Path V (n + m)
  | 0, _, _, q => q
  | _ + 1, _, (y, p), q => (y, C.append p q)

 theorem weight_append {m n : ℕ} (x : V) (p : Path V m) (q : Path V n) :
    C.weight x (C.append p q) = C.weight x p * C.weight (C.endpoint x p) q := by
  induction m generalizing x with
  | zero => simp [append, weight, endpoint]
  | succ m ih =>
    change C.transition x p.1 * C.weight p.1 (C.append p.2 q) =
      (C.transition x p.1 * C.weight p.1 p.2) * C.weight (C.endpoint p.1 p.2) q
    rw [ih, mul_assoc]

 theorem extension_weight_sum {m : ℕ} (n : ℕ) (x : V) (p : Path V m) :
    (∑ q : Path V n, C.weight x (C.append p q)) = C.weight x p := by
  simp_rw [C.weight_append]
  rw [← Finset.mul_sum, C.total_weight, mul_one]

 theorem endpoint_append {m n : ℕ} (x : V) (p : Path V m) (q : Path V n) :
    C.endpoint x (C.append p q) = C.endpoint (C.endpoint x p) q := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => exact ih p.1 p.2

/-- A path event may also depend on its initial state. -/
noncomputable def eventMass (n : ℕ) (E : V → Path V n → Prop) (x : V) : ℝ :=
  by classical exact ∑ p, if E x p then C.weight x p else 0

 theorem eventMass_nonneg (n : ℕ) (E : V → Path V n → Prop) (x : V) :
    0 ≤ C.eventMass n E x := by
  classical
  unfold eventMass
  exact Finset.sum_nonneg fun p _ => by
    split_ifs
    · exact C.weight_nonneg x p
    · exact le_refl 0

 theorem eventMass_le_one (n : ℕ) (E : V → Path V n → Prop) (x : V) :
    C.eventMass n E x ≤ 1 := by
  classical
  rw [← C.total_weight n x]
  unfold eventMass
  apply Finset.sum_le_sum
  intro p _
  split_ifs
  · exact le_refl _
  · exact C.weight_nonneg x p

 theorem start_domination (n : ℕ) (E : V → Path V n → Prop)
    (pi : V → ℝ) (hpi : ∀ y, 0 ≤ pi y) (x : V) :
    pi x * C.eventMass n E x ≤ ∑ y, pi y * C.eventMass n E y := by
  classical
  exact Finset.single_le_sum
    (fun y _ => mul_nonneg (hpi y) (C.eventMass_nonneg n E y)) (Finset.mem_univ x)

 theorem start_domination_div (n : ℕ) (E : V → Path V n → Prop)
    (pi : V → ℝ) (hpi : ∀ y, 0 ≤ pi y) (x : V) (hx : 0 < pi x) :
    C.eventMass n E x ≤ (∑ y, pi y * C.eventMass n E y) / pi x := by
  apply (le_div_iff₀ hx).2
  simpa [mul_comm] using C.start_domination n E pi hpi x

/-- Domination of any initial law by another, for the same state-dependent event. -/
theorem mixture_domination (n : ℕ) (E : V → Path V n → Prop)
    (mu pi : V → ℝ) (K : ℝ) (hbound : ∀ x, mu x ≤ K * pi x) :
    (∑ x, mu x * C.eventMass n E x) ≤ K * ∑ x, pi x * C.eventMass n E x := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right (hbound x) (C.eventMass_nonneg n E x)

end Chain
end Erdos642.FiniteMarkov
