import Openmath.Erdos643R3.PsiLoss

set_option autoImplicit false
namespace Erdos643R3.GeneralizedPsi
open G3hpArith

theorem lossJ_formula (k m : ℕ) :
    lossJ k m = (m : ℚ) / ((2 + (k : ℚ)) * (2 + (k : ℚ) + m)) := by
  unfold lossJ
  field_simp; ring

theorem lossE_formula (k m : ℕ) :
    lossE k m = (m : ℚ) / (2 * (1 + (k : ℚ)) * (1 + (k : ℚ) + m)) := by
  unfold lossE
  field_simp; ring

/-- The two exceptional loss forms are bounded by U(c)'s loss budget for `k ≥ 1`. -/
theorem loss_budget {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (inJ : Bool) :
    exceptionalLoss inJ k m ≤ (m : ℚ) / (3 * ((m : ℚ) + 3)) := by
  have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
  cases inJ
  · change lossE k m ≤ _
    rw [lossE_formula]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [mul_nonneg (show (0 : ℚ) ≤ k - 1 by linarith) (show (0 : ℚ) ≤ 2 * k + 2 * m + 6 by positivity)]
  · change lossJ k m ≤ _
    rw [lossJ_formula]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith

theorem zero_k_large {j d e r : ℕ} (hj : 2 ≤ j) (hlarge : j ≤ r → 5 ≤ j)
    (hr : 2 ≤ r) {L : ℚ} (hL : L < 1 / 2) : 2 < PsiR j d e r 0 - L := by
  rcases le_or_gt j r with hjr | hrj
  · have h := case_ii_zero (d := d) (e := e) (hlarge hjr) hjr
    linarith
  · have h := case_iii (d := d) (e := e) (by omega : r + 1 ≤ j) (show 0 ≤ r by omega)
    have hz := correction_zero (by omega : r + 1 ≤ j)
    have hm := chi_mono (show r + 2 ≤ j + 1 by omega)
    have hb := chi_base r
    have hr' : (2 : ℚ) ≤ r := by exact_mod_cast hr
    have b : (1 : ℚ) / 2 ≤ (r : ℚ)^2 / (2 * ((r : ℚ) + 2)) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    linarith

/-- Lemma U(c)'s exact arithmetic bound for unrestricted `m ≥ 2`, retaining `m ≤ r - k`. -/
theorem lemmaUc_arith {j d e r k m : ℕ} (inJ : Bool)
    (hj : 2 ≤ j) (hlarge : j ≤ r → 5 ≤ j) (hm : 2 ≤ m) (hkm : k + m ≤ r) :
    -(m : ℚ) / (3 * ((m : ℚ) + 3)) < PsiR j d e r k - exceptionalLoss inJ k m - 2 := by
  rw [neg_div]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst k
    have hl : exceptionalLoss inJ 0 m < 1 / 2 := by
      cases inJ
      · simpa [exceptionalLoss] using lossE_lt 0 m
      · simpa [exceptionalLoss] using lossJ_lt 0 m
    have h := zero_k_large (d := d) (e := e) hj hlarge (by omega : 2 ≤ r) hl
    have hbudget : (0 : ℚ) ≤ (m : ℚ) / (3 * ((m : ℚ) + 3)) := by positivity
    linarith
  · have h := psiR_gt_two (d := d) (e := e) hj hlarge (by omega : k ≤ r)
    have hl := loss_budget hk (show 1 ≤ m by omega) inJ
    linarith

end Erdos643R3.GeneralizedPsi
