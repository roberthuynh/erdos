import Erdos1017.LogEnclosure

namespace Erdos1017
open scoped BigOperators

/-- The exact degree-16 exponential polynomial with a geometric tail at term 17. -/
noncomputable def expUpper (x : ℝ) : ℝ :=
  (∑ j ∈ Finset.range 17, x^j/j.factorial) + (x^17/(17).factorial)/(1-x/18)

theorem expUpper_bound (x : ℝ) (hx : 0 ≤ x) (hx18 : x < 18) : Real.exp x ≤ expUpper x := by
  simpa only [expUpper, Nat.cast_ofNat, show (17 : ℝ)+1=18 by norm_num] using
    exp_geometric_tail_upper x hx 17 (by norm_num; exact hx18)

theorem expUpper_pos (x : ℝ) (hx : 0 ≤ x) (hx18 : x < 18) : 0 < expUpper x :=
  (Real.exp_pos x).trans_le (expUpper_bound x hx hx18)

/-- The rational product enclosure used on each closed certificate rectangle. -/
theorem independent_product_rational_lower {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (m Sh qh : ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) (hm : ∀ i ∈ s, p i ≤ m)
    (hm0 : 0 ≤ m) (hm1 : m < 1) (hSh : 0 ≤ Sh) (hqh : 0 ≤ qh)
    (hS : (∑ i ∈ s, p i) ≤ Sh) (hq : (∑ i ∈ s, (p i)^2) ≤ qh)
    (hX : Sh+logCoefficientUpper 13 m*qh < 18) :
    1/expUpper (Sh+logCoefficientUpper 13 m*qh) ≤ ∏ i ∈ s, (1-p i) := by
  have hc : 0 ≤ logCoefficientUpper 13 m := logCoefficientUpper_nonneg 13 m hm0 hm1
  have hx0 : 0 ≤ Sh+logCoefficientUpper 13 m*qh := add_nonneg hSh (mul_nonneg hc hqh)
  have hexp := expUpper_bound (Sh+logCoefficientUpper 13 m*qh) hx0 hX
  calc
    _ ≤ 1/Real.exp (Sh+logCoefficientUpper 13 m*qh) :=
      one_div_le_one_div_of_le (Real.exp_pos _) hexp
    _ = Real.exp (-(Sh+logCoefficientUpper 13 m*qh)) := by rw [Real.exp_neg, one_div]
    _ ≤ Real.exp (-(∑ i ∈ s, p i)-logCoefficientUpper 13 m*(∑ i ∈ s, (p i)^2)) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left hq hc
      linarith
    _ ≤ _ := independent_product_exp_lower s p m hp hm hm1 13

end Erdos1017
