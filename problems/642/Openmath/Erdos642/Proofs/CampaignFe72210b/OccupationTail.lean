import Openmath.Erdos642.Proofs.CampaignFe72210b.PathMoment

/-! Finite exponential Markov inequalities and the exact scalar occupation-tail step.
    The final path theorem has an explicit intermediate moment premise. -/
namespace Erdos642.OccupationTail

/-- Exponential Markov inequality for genuine nonnegative finite weights. -/
theorem finite_exponential_markov {I : Type*} [Fintype I]
    (w φ : I → ℝ) (hw : ∀ i, 0 ≤ w i) (θ a : ℝ) (hθ : 0 ≤ θ) :
    (∑ i, if φ i ≤ a then w i else 0) ≤
      Real.exp (θ * a) * ∑ i, w i * Real.exp (-θ * φ i) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : φ i ≤ a
  · simp only [hi, if_true]
    have he : 1 ≤ Real.exp (θ * a) * Real.exp (-θ * φ i) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hm := mul_le_mul_of_nonneg_left he (hw i)
    nlinarith
  · simp only [hi, if_false]
    exact mul_nonneg (le_of_lt (Real.exp_pos _))
      (mul_nonneg (hw i) (le_of_lt (Real.exp_pos _)))

/-- The scalar conversion used after bounding the finite moment by a matrix power. -/
theorem scalar_tail_bound (γ μ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (γ * μ * (n : ℝ) / 32) * (1 - 3 * γ * μ / 64) ^ (n - 1) ≤
      2 * Real.exp (-γ * μ * (n : ℝ) / 64) := by
  have hp0 : 0 ≤ γ * μ := mul_nonneg (le_of_lt hγ) hμ
  have hp1 : γ * μ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hμ1 (le_of_lt hγ)
    nlinarith
  have hq0 : 0 ≤ 1 - 3 * γ * μ / 64 := by nlinarith
  have hq : 1 - 3 * γ * μ / 64 ≤ Real.exp (-3 * γ * μ / 64) := by
    have h := Real.add_one_le_exp (-3 * γ * μ / 64)
    linarith
  have hpow := pow_le_pow_left₀ hq0 hq (n - 1)
  have hpref : Real.exp (3 * γ * μ / 64) ≤ 2 := by
    have hs : Real.exp (3 * γ * μ / 64) ^ 2 ≤ Real.exp 1 := by
      rw [pow_two, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    nlinarith [Real.exp_one_lt_three, Real.exp_pos (3 * γ * μ / 64)]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  calc
    Real.exp (γ * μ * (n : ℝ) / 32) * (1 - 3 * γ * μ / 64) ^ (n - 1) ≤
      Real.exp (γ * μ * (n : ℝ) / 32) * Real.exp (-3 * γ * μ / 64) ^ (n - 1) :=
        mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos _))
    _ = Real.exp (3 * γ * μ / 64) * Real.exp (-γ * μ * (n : ℝ) / 64) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, hcast]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpref (le_of_lt (Real.exp_pos _))

open Erdos642.FiniteMarkov

variable {V : Type*} [Fintype V]

/-- A fixed-start exponential Markov inequality for the actual finite path law. -/
theorem path_exponential_markov (C : Chain V) (f : V → ℝ) (m : ℕ)
    (x : V) (θ a : ℝ) (hθ : 0 ≤ θ) :
    C.eventMass m (fun x p => Chain.vertexSum f x p ≤ a) x ≤
      Real.exp (θ * a) *
        ∑ p : Path V m, C.weight x p * Real.exp (-θ * Chain.vertexSum f x p) := by
  classical
  exact finite_exponential_markov (C.weight x) (Chain.vertexSum f x)
    (C.weight_nonneg x) θ a hθ

/-- The same finite inequality for arbitrary nonnegative initial coefficients. -/
theorem mixture_exponential_markov (C : Chain V) (f pi : V → ℝ)
    (hpi : ∀ x, 0 ≤ pi x) (m : ℕ) (θ a : ℝ) (hθ : 0 ≤ θ) :
    (∑ x, pi x * C.eventMass m (fun x p => Chain.vertexSum f x p ≤ a) x) ≤
      Real.exp (θ * a) *
        ∑ x, pi x * ∑ p : Path V m,
          C.weight x p * Real.exp (-θ * Chain.vertexSum f x p) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have h := mul_le_mul_of_nonneg_left (path_exponential_markov C f m x θ a hθ) (hpi x)
  simpa only [mul_assoc, mul_left_comm] using h

variable [DecidableEq V]

/-- The actual vertex occupation count, including the initial path vertex. -/
noncomputable def occupation (S : Finset V) {m : ℕ}
    (x : V) (p : Path V m) : ℝ := Chain.vertexSum (fun y => if y ∈ S then 1 else 0) x p

/-- An explicit intermediate consequence of the actual finite path-moment bound.
    This does not assert that the moment premise has already been discharged. -/
theorem occupation_tail_from_moment (C : Chain V) (S : Finset V)
    (γ μ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (x : V)
    (hmoment : (∑ p : Path V (n - 1),
      C.weight x p * Real.exp (-(γ / 16) * occupation S x p)) ≤
      (1 - 3 * γ * μ / 64) ^ (n - 1)) :
    C.eventMass (n - 1) (fun x p => occupation S x p ≤ (n : ℝ) * μ / 2) x ≤
      2 * Real.exp (-γ * μ * (n : ℝ) / 64) := by
  have hmarkov := path_exponential_markov C (fun y => if y ∈ S then 1 else 0)
    (n - 1) x (γ / 16) ((n : ℝ) * μ / 2) (by positivity)
  change C.eventMass (n - 1) (fun x p => occupation S x p ≤ (n : ℝ) * μ / 2) x ≤
    Real.exp ((γ / 16) * ((n : ℝ) * μ / 2)) * _ at hmarkov
  have hmoment' := mul_le_mul_of_nonneg_left hmoment
    (le_of_lt (Real.exp_pos ((γ / 16) * ((n : ℝ) * μ / 2))))
  have heq : (γ / 16) * ((n : ℝ) * μ / 2) = γ * μ * (n : ℝ) / 32 := by ring
  rw [heq] at hmarkov hmoment'
  exact hmarkov.trans (hmoment'.trans (scalar_tail_bound γ μ hγ hγ1 hμ hμ1 n hn))

/-- A mixture version suitable for a stationary path-moment bound. -/
theorem mixture_occupation_tail_from_moment (C : Chain V) (S : Finset V)
    (pi : V → ℝ) (hpi : ∀ x, 0 ≤ pi x)
    (γ μ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (n : ℕ) (hn : 1 ≤ n)
    (hmoment : (∑ x, pi x * ∑ p : Path V (n - 1),
      C.weight x p * Real.exp (-(γ / 16) * occupation S x p)) ≤
      (1 - 3 * γ * μ / 64) ^ (n - 1)) :
    (∑ x, pi x * C.eventMass (n - 1)
      (fun x p => occupation S x p ≤ (n : ℝ) * μ / 2) x) ≤
      2 * Real.exp (-γ * μ * (n : ℝ) / 64) := by
  have hmarkov := mixture_exponential_markov C (fun y => if y ∈ S then 1 else 0)
    pi hpi (n - 1) (γ / 16) ((n : ℝ) * μ / 2) (by positivity)
  change (∑ x, pi x * C.eventMass (n - 1)
    (fun x p => occupation S x p ≤ (n : ℝ) * μ / 2) x) ≤
    Real.exp ((γ / 16) * ((n : ℝ) * μ / 2)) * _ at hmarkov
  have hmoment' := mul_le_mul_of_nonneg_left hmoment
    (le_of_lt (Real.exp_pos ((γ / 16) * ((n : ℝ) * μ / 2))))
  have heq : (γ / 16) * ((n : ℝ) * μ / 2) = γ * μ * (n : ℝ) / 32 := by ring
  rw [heq] at hmarkov hmoment'
  exact hmarkov.trans (hmoment'.trans (scalar_tail_bound γ μ hγ hγ1 hμ hμ1 n hn))

end Erdos642.OccupationTail
