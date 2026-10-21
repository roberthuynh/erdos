import Erdos1017.GeometricTail

namespace Erdos1017
open scoped BigOperators

noncomputable def logCoefficientUpper (N : ℕ) (m : ℝ) : ℝ :=
  (∑ j ∈ Finset.range N, m^j/(j+2)) + m^N/((N+2)*(1-m))

theorem logCoefficientUpper_nonneg (N : ℕ) (m : ℝ) (hm : 0 ≤ m) (hm1 : m < 1) :
    0 ≤ logCoefficientUpper N m := by
  unfold logCoefficientUpper
  apply add_nonneg
  · exact Finset.sum_nonneg (fun j _ => div_nonneg (pow_nonneg hm _) (by positivity))
  · exact div_nonneg (pow_nonneg hm _) (mul_nonneg (by positivity) (sub_pos.mpr hm1).le)

theorem log_prefix_quadratic (x : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (N+1), x^(j+1)/(j+1)) =
      x+x^2*(∑ j ∈ Finset.range N, x^j/(j+2)) := by
  rw [Finset.sum_range_succ']
  simp only [pow_one, Nat.cast_zero, zero_add, div_one]
  rw [Finset.mul_sum]
  rw [add_comm x]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

/-- A finite positive-series enclosure, with the same geometric remainder as the
rational certificate. `N=13` is its actual truncation. -/
theorem neg_log_quadratic_upper (x m : ℝ) (hx : 0 ≤ x) (hxm : x ≤ m) (hm1 : m < 1)
    (N : ℕ) : -Real.log (1-x) ≤ x+logCoefficientUpper N m*x^2 := by
  have hm : 0 ≤ m := hx.trans hxm
  have hx1 : x < 1 := hxm.trans_lt hm1
  have hprefix : (∑ j ∈ Finset.range N, x^j/(j+2)) ≤
      ∑ j ∈ Finset.range N, m^j/(j+2) := by
    apply Finset.sum_le_sum
    intro j _
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxm j) (by positivity)
  have htail : x^N/((N+2)*(1-x)) ≤ m^N/((N+2)*(1-m)) := by
    rw [div_mul_eq_div_div, div_mul_eq_div_div]
    calc
      _ ≤ (m^N/(N+2))/(1-x) := div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxm N) (by positivity)) (sub_pos.mpr hx1).le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hm1) (sub_le_sub_left hxm 1)
  have h := neg_log_geometric_tail_upper x hx hx1 (N+1)
  rw [log_prefix_quadratic] at h
  have he : (x^(N+1+1)/(N+1+1))/(1-x) = x^2 * (x^N/((N+2)*(1-x))) := by
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  push_cast at h
  rw [he] at h
  have hb := mul_le_mul_of_nonneg_left (add_le_add hprefix htail) (sq_nonneg x)
  unfold logCoefficientUpper
  nlinarith

theorem independent_product_exp_lower {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (m : ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) (hm : ∀ i ∈ s, p i ≤ m) (hm1 : m < 1) (N : ℕ) :
    Real.exp (-(∑ i ∈ s, p i)-logCoefficientUpper N m*(∑ i ∈ s, (p i)^2)) ≤
      ∏ i ∈ s, (1-p i) := by
  have hsum : -(∑ i ∈ s, Real.log (1-p i)) ≤
      (∑ i ∈ s, p i)+logCoefficientUpper N m*(∑ i ∈ s, (p i)^2) := by
    rw [← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i hi => neg_log_quadratic_upper (p i) m (hp i hi) (hm i hi) hm1 N)
  have he := Real.exp_le_exp.mpr (show -(∑ i ∈ s, p i)-logCoefficientUpper N m*(∑ i ∈ s, (p i)^2) ≤
      ∑ i ∈ s, Real.log (1-p i) by linarith)
  rw [Real.exp_sum] at he
  have hp' : (∏ i ∈ s, Real.exp (Real.log (1-p i))) = ∏ i ∈ s, (1-p i) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact Real.exp_log (sub_pos.mpr ((hm i hi).trans_lt hm1))
  rwa [hp'] at he

end Erdos1017
