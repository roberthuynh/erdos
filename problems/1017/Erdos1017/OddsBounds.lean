import Erdos1017.ElementaryBounds
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

theorem odds_decomposition (x : ℝ) (hx : x < 1) :
    x/(1-x) = x + x^2/(1-x) := by
  have h : 1-x ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  field_simp
  ring

/-- The upper odds budget and the weighted Cauchy lower correction used in the
continuous sharp-line certificate. Zero coordinates are allowed. -/
theorem odds_sum_certificate (s : Finset ι) (p : ι → ℝ) (m : ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ p i) (hm : ∀ i ∈ s, p i ≤ m) (hm1 : m < 1)
    (hgap : 0 < (∑ i ∈ s, p i) - ∑ i ∈ s, (p i)^2) :
    (∑ i ∈ s, p i/(1-p i)) ≤ (∑ i ∈ s, p i) + (∑ i ∈ s, (p i)^2)/(1-m) ∧
    ((∑ i ∈ s, p i)*(∑ i ∈ s, (p i)^2))/
        ((∑ i ∈ s, p i)-(∑ i ∈ s, (p i)^2)) ≤ ∑ i ∈ s, (p i)^2/(1-p i) := by
  have hlt : ∀ i ∈ s, p i < 1 := fun i hi => (hm i hi).trans_lt hm1
  have hdecomp : (∑ i ∈ s, p i/(1-p i)) =
      (∑ i ∈ s, p i) + ∑ i ∈ s, (p i)^2/(1-p i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i hi => odds_decomposition (p i) (hlt i hi))
  constructor
  · rw [hdecomp]
    apply add_le_add_right
    have hsum : (∑ i ∈ s, (p i)^2)/(1-m) = ∑ i ∈ s, (p i)^2/(1-m) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    rw [hsum]
    apply Finset.sum_le_sum
    intro i hi
    exact div_le_div_of_nonneg_left (sq_nonneg _) (sub_pos.mpr hm1) (sub_le_sub_left (hm i hi) 1)
  · have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (r := p) (f := fun i => p i/(1-p i)) (g := fun i => p i*(1-p i))
      (fun i hi => div_nonneg (h0 i hi) (sub_pos.mpr (hlt i hi)).le)
      (fun i hi => mul_nonneg (h0 i hi) (sub_pos.mpr (hlt i hi)).le)
      (fun i hi => by
        have hn : 1-p i ≠ 0 := ne_of_gt (sub_pos.mpr (hlt i hi))
        have he : p i/(1-p i)*(p i*(1-p i)) = (p i)^2 := by field_simp
        rw [he])
    have hg : (∑ i ∈ s, p i*(1-p i)) = (∑ i ∈ s, p i) - ∑ i ∈ s, (p i)^2 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hg, hdecomp] at hc
    apply (div_le_iff₀ hgap).mpr
    nlinarith

end Erdos1017
