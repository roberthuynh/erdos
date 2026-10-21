import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Erdos1017
open scoped BigOperators

/-- A finite prefix and a geometric majorant bound the entire convergent series. -/
theorem series_geometric_tail_upper (a : ℕ → ℝ) (A r : ℝ) (hA : HasSum a A)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ)
    (hstep : ∀ k, a (k+N+1) ≤ r*a (k+N)) :
    A ≤ (∑ k ∈ Finset.range N, a k) + a N/(1-r) := by
  have hdom : ∀ k, a (k+N) ≤ a N*r^k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        a (k+1+N) = a (k+N+1) := by congr 1; omega
        _ ≤ r*a (k+N) := hstep k
        _ ≤ r*(a N*r^k) := mul_le_mul_of_nonneg_left ih hr0
        _ = a N*r^(k+1) := by ring
  have hshift : Summable (fun k => a (k+N)) := (summable_nat_add_iff N).mpr hA.summable
  have hgeom := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (a N)
  have ht := hshift.tsum_le_tsum hdom hgeom.summable
  rw [hgeom.tsum_eq] at ht
  have hsplit := hA.summable.sum_add_tsum_nat_add N
  rw [hA.tsum_eq] at hsplit
  calc
    A = (∑ k ∈ Finset.range N, a k) + ∑' k, a (k+N) := hsplit.symm
    _ ≤ (∑ k ∈ Finset.range N, a k) + a N/(1-r) := by
      simpa only [div_eq_mul_inv] using add_le_add_right ht (∑ k ∈ Finset.range N, a k)

theorem exp_geometric_tail_upper (x : ℝ) (hx : 0 ≤ x) (N : ℕ) (hN : x < N+1) :
    Real.exp x ≤ (∑ k ∈ Finset.range N, x^k/k.factorial) +
      (x^N/N.factorial)/(1-x/(N+1)) := by
  have ha : HasSum (fun k : ℕ => x^k/k.factorial) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  apply series_geometric_tail_upper _ _ (x/(N+1)) ha (by positivity)
    ((div_lt_one (by positivity : (0 : ℝ) < N+1)).mpr hN) N
  intro k
  calc
    x^(k+N+1)/((k+N+1).factorial : ℝ) =
        (x^(k+N)/(k+N).factorial)*x/(k+N+1) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      simp only [div_eq_mul_inv, mul_inv_rev, Nat.cast_add]
      ring
    _ ≤ (x^(k+N)/(k+N).factorial)*x/(N+1) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact_mod_cast (show N+1 ≤ k+N+1 by omega)
    _ = x/(N+1)*(x^(k+N)/(k+N).factorial) := by ring

theorem neg_log_geometric_tail_upper (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    -Real.log (1-x) ≤ (∑ k ∈ Finset.range N, x^(k+1)/(k+1)) +
      (x^(N+1)/(N+1))/(1-x) := by
  have ha := Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by simpa [abs_of_nonneg hx] using hx1)
  apply series_geometric_tail_upper _ _ x ha hx hx1 N
  intro k
  simp only [Nat.cast_add, Nat.cast_one]
  calc
    x^(k+N+1+1)/(k+N+1+1) = x^(k+N+1)*x/(k+N+1+1) := by rw [pow_succ]
    _ ≤ x^(k+N+1)*x/(k+N+1) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      push_cast
      linarith
    _ = x*(x^(k+N+1)/(k+N+1)) := by ring

end Erdos1017
