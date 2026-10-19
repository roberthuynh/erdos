import Openmath.Erdos643R3.G3hpArith

set_option autoImplicit false

namespace Erdos643R3.GeneralizedPsi
open G3hpArith

/-- Generalized Ψ with the total `r` and type-one count `k` explicit. -/
def PsiR (j d e r k : ℕ) : ℚ :=
  2 / (2 + (r : ℚ)) + 1 / (2 + (j : ℚ) + d) + 1 / (2 + (j : ℚ)) +
  (j : ℚ) / (2 + (k : ℚ)) + (d : ℚ) / (2 * (1 + (r : ℚ))) +
  (r : ℚ) / (2 * (1 + (j : ℚ) + d)) + (e : ℚ) / (2 * (1 + (k : ℚ))) +
  (k : ℚ) / (2 * (1 + (j : ℚ) + e))

/-- Exact notation of consolidated proof §7.7, with `r = k + q`. -/
def PsiN (j d e k q : ℕ) : ℚ := PsiR j d e (k + q) k

def delta (j d : ℕ) : ℚ :=
  ((1 + (j : ℚ) + d) - 1) / (2 * (1 + (j : ℚ) + d) * (2 + (j : ℚ) + d))

def correction (j r k : ℕ) : ℚ :=
  ((r : ℚ) - k) * ((j : ℚ) / ((2 + (k : ℚ)) * (2 + (r : ℚ))) - 1 / (2 * (1 + (j : ℚ))))

theorem delta_pos {j d : ℕ} (hj : 1 ≤ j) : 0 < delta j d := by
  have : (1 : ℚ) ≤ j := by exact_mod_cast hj
  unfold delta
  exact div_pos (by have hd : (0 : ℚ) ≤ d := Nat.cast_nonneg d; linarith) (by positivity)

theorem pair_bound (j d r : ℕ) :
    1 - (1 + (j : ℚ)) / (2 * (1 + (r : ℚ))) + delta j d ≤
      1 / (2 + (j : ℚ) + d) + (d : ℚ) / (2 * (1 + (r : ℚ))) +
      (r : ℚ) / (2 * (1 + (j : ℚ) + d)) := by
  have h := amgm_pair (x := 1 + (j : ℚ) + d) (y := 1 + (r : ℚ)) (by positivity) (by positivity)
  have eq : 1 / (2 + (j : ℚ) + d) + (d : ℚ) / (2 * (1 + (r : ℚ))) +
      (r : ℚ) / (2 * (1 + (j : ℚ) + d)) =
      ((1 + (j : ℚ) + d) / (2 * (1 + (r : ℚ))) +
      (1 + (r : ℚ)) / (2 * (1 + (j : ℚ) + d))) -
      (1 + (j : ℚ)) / (2 * (1 + (r : ℚ))) + delta j d := by
    unfold delta
    field_simp
    ring
  rw [eq]
  linarith

/-- Case (i) of S10.1, with all five explicit nonnegative terms. -/
theorem case_i {j d e r k : ℕ} (hj : 2 ≤ j) (hjk : j ≤ k) (hkr : k ≤ r) :
    ((r : ℚ) - j) / (2 * (1 + (r : ℚ)) * (2 + (r : ℚ))) +
    ((k : ℚ) - j) / (2 * (1 + (k : ℚ)) * (2 + (k : ℚ))) +
    ((j : ℚ) - 2) * ((r : ℚ) - k) / (2 * (2 + (r : ℚ)) * (2 + (k : ℚ))) +
    delta j d + (j : ℚ) / (2 * (1 + (j : ℚ)) * (2 + (j : ℚ))) ≤ PsiR j d e r k - 2 := by
  have pd := pair_bound j d r
  have pe := amgm_pair (x := 1 + (j : ℚ) + e) (y := 1 + (k : ℚ)) (by positivity) (by positivity)
  have ee : (e : ℚ) / (2 * (1 + (k : ℚ))) + (k : ℚ) / (2 * (1 + (j : ℚ) + e)) =
      ((1 + (j : ℚ) + e) / (2 * (1 + (k : ℚ))) + (1 + (k : ℚ)) / (2 * (1 + (j : ℚ) + e))) -
      (1 + (j : ℚ)) / (2 * (1 + (k : ℚ))) - 1 / (2 * (1 + (j : ℚ) + e)) := by
    field_simp; ring
  have inv : 1 / (2 * (1 + (j : ℚ) + e)) ≤ 1 / (2 * (1 + (j : ℚ))) :=
    one_div_le_one_div_of_le (by positivity) (by have he : (0 : ℚ) ≤ e := Nat.cast_nonneg e; linarith)
  have id : 2 / (2 + (r : ℚ)) + (j : ℚ) / (2 + (k : ℚ)) -
      (1 + (j : ℚ)) / (2 * (1 + (r : ℚ))) - (1 + (j : ℚ)) / (2 * (1 + (k : ℚ))) =
      ((r : ℚ) - j) / (2 * (1 + (r : ℚ)) * (2 + (r : ℚ))) +
      ((k : ℚ) - j) / (2 * (1 + (k : ℚ)) * (2 + (k : ℚ))) +
      ((j : ℚ) - 2) * ((r : ℚ) - k) / (2 * (2 + (r : ℚ)) * (2 + (k : ℚ))) := by
    field_simp; ring
  have id2 : 1 / (2 + (j : ℚ)) - 1 / (2 * (1 + (j : ℚ))) =
      (j : ℚ) / (2 * (1 + (j : ℚ)) * (2 + (j : ℚ))) := by field_simp; ring
  unfold PsiR
  linarith

/-- Case (iii) of S10.1. -/
theorem case_iii {j d e r k : ℕ} (hjr : r + 1 ≤ j) (hkr : k ≤ r) :
    chi r (j + 1) + correction j r k ≤ PsiR j d e r k := by
  have he := e_part (e := e) (show k + 1 ≤ j by omega)
  have hd := psi_mono (d := d) hjr
  have id : chi r (j + 1) + correction j r k =
      2 / (2 + (r : ℚ)) + 1 / (2 + (j : ℚ)) + 1 / (2 + (j : ℚ)) +
      (j : ℚ) / (2 + (k : ℚ)) + (r : ℚ) / (2 * (1 + (j : ℚ))) + (k : ℚ) / (2 * (1 + (j : ℚ))) := by
    unfold chi correction
    push_cast
    field_simp; ring
  rw [id]
  unfold PsiR
  linarith

/-- The bracket estimate in case (iii). -/
theorem bracket_bound {j r k : ℕ} (hjr : r + 1 ≤ j) :
    ((r : ℚ) + 1) / ((2 + (k : ℚ)) * (2 + (r : ℚ))) - 1 / (2 * ((r : ℚ) + 2)) ≤
      (j : ℚ) / ((2 + (k : ℚ)) * (2 + (r : ℚ))) - 1 / (2 * (1 + (j : ℚ))) := by
  have h : (r : ℚ) + 1 ≤ j := by exact_mod_cast hjr
  have a := div_le_div_of_nonneg_right h (show (0 : ℚ) ≤ (2 + (k : ℚ)) * (2 + (r : ℚ)) by positivity)
  have b : 1 / (2 * (1 + (j : ℚ))) ≤ 1 / (2 * ((r : ℚ) + 2)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

theorem correction_nonneg {j r k : ℕ} (hjr : r + 1 ≤ j) (hkr : k ≤ r) : 0 ≤ correction j r k := by
  have hk : (k : ℚ) ≤ r := by exact_mod_cast hkr
  have hr : (0 : ℚ) ≤ r := Nat.cast_nonneg r
  have b := bracket_bound (k := k) hjr
  have base : 1 / (2 * ((r : ℚ) + 2)) ≤ ((r : ℚ) + 1) / ((2 + (k : ℚ)) * (2 + (r : ℚ))) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  unfold correction
  exact mul_nonneg (by linarith) (by linarith)

def fR (j r : ℕ) : ℚ := 2 / (2 + (r : ℚ)) - (1 + (j : ℚ)) / (2 * (1 + (r : ℚ)))

theorem fR_step {j r : ℕ} (hj : 3 ≤ j) : fR j r ≤ fR j (r + 1) := by
  have hj' : (3 : ℚ) ≤ j := by exact_mod_cast hj
  have hr : (0 : ℚ) ≤ r := Nat.cast_nonneg r
  have diff : fR j (r + 1) - fR j r =
      (1 + (j : ℚ)) / (2 * (1 + (r : ℚ)) * (2 + (r : ℚ))) -
      2 / ((2 + (r : ℚ)) * (3 + (r : ℚ))) := by
    unfold fR
    push_cast
    field_simp; ring
  have le : 2 / ((2 + (r : ℚ)) * (3 + (r : ℚ))) ≤
      (1 + (j : ℚ)) / (2 * (1 + (r : ℚ)) * (2 + (r : ℚ))) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (show (0 : ℚ) ≤ j - 3 by linarith) (show (0 : ℚ) ≤ (r + 2) * (r + 3) by positivity)]
  linarith

theorem fR_mono {j r : ℕ} (hj : 3 ≤ j) (hjr : j ≤ r) : fR j j ≤ fR j r := by
  induction r, hjr using Nat.le_induction with
  | base => exact le_rfl
  | succ r h ih => exact ih.trans (fR_step hj)

def g10 (k j : ℕ) : ℚ := (j : ℚ) / (2 + (k : ℚ)) + (k : ℚ) / (2 * (1 + (j : ℚ))) + 3 / (2 + (j : ℚ))

theorem g10_step {k j : ℕ} (hkj : k + 1 ≤ j) : g10 k j ≤ g10 k (j + 1) := by
  have hkj' : (k : ℚ) + 1 ≤ j := by exact_mod_cast hkj
  have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have diff : g10 k (j + 1) - g10 k j = 1 / (2 + (k : ℚ)) -
      (k : ℚ) / (2 * (1 + (j : ℚ)) * (2 + (j : ℚ))) - 3 / ((2 + (j : ℚ)) * (3 + (j : ℚ))) := by
    unfold g10
    push_cast
    field_simp; ring
  have b1 : (k : ℚ) / (2 * (1 + (j : ℚ)) * (2 + (j : ℚ))) ≤
      (k : ℚ) / (2 * (2 + (k : ℚ)) * (3 + (k : ℚ))) :=
    div_le_div_of_nonneg_left hk (by positivity) (by nlinarith)
  have b2 : (3 : ℚ) / ((2 + (j : ℚ)) * (3 + (j : ℚ))) ≤
      3 / ((3 + (k : ℚ)) * (4 + (k : ℚ))) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have b3 : (k : ℚ) / (2 * (2 + (k : ℚ)) * (3 + (k : ℚ))) +
      3 / ((3 + (k : ℚ)) * (4 + (k : ℚ))) ≤ 1 / (2 + (k : ℚ)) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (k : ℚ), mul_nonneg hk (sq_nonneg (k : ℚ)), mul_nonneg (sq_nonneg (k : ℚ)) (sq_nonneg (k : ℚ))]
  linarith

theorem g10_mono {k a b : ℕ} (hka : k + 1 ≤ a) (hab : a ≤ b) : g10 k a ≤ g10 k b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b h ih => exact ih.trans (g10_step (by omega))

theorem case_ii_aux {j d e r k : ℕ} (hj : 3 ≤ j) (hkj : k < j) (hjr : j ≤ r) :
    g10 k j - 3 / 2 + delta j d ≤ PsiR j d e r k - 2 := by
  have pd := pair_bound j d r
  have pe := e_part (e := e) (show k + 1 ≤ j by omega)
  have hm := fR_mono hj hjr
  have id : fR j j = 2 / (2 + (j : ℚ)) - 1 / 2 := by unfold fR; field_simp
  rw [id] at hm
  unfold fR at hm
  unfold PsiR g10
  rw [show (3 : ℚ) / (2 + (j : ℚ)) = 2 / (2 + (j : ℚ)) + 1 / (2 + (j : ℚ)) by ring]
  linarith

/-- Case (ii) of S10.1. -/
theorem case_ii {j d e r k : ℕ} (hj : 5 ≤ j) (hkj : k < j) (hjr : j ≤ r) :
    (k : ℚ) / (((k : ℚ) + 2) * ((k : ℚ) + 3)) + delta j d ≤ PsiR j d e r k - 2 := by
  have b := case_ii_aux (d := d) (e := e) (by omega : 3 ≤ j) hkj hjr
  have h := g10_mono (show k + 1 ≤ k + 1 by omega) (show k + 1 ≤ j by omega)
  have id : g10 k (k + 1) - 3 / 2 = (k : ℚ) / (((k : ℚ) + 2) * ((k : ℚ) + 3)) := by
    unfold g10
    push_cast
    field_simp; ring
  linarith

/-- The stronger zero-`k` bound in case (ii). -/
theorem case_ii_zero {j d e r : ℕ} (hj : 5 ≤ j) (hjr : j ≤ r) :
    10 / 7 ≤ PsiR j d e r 0 - 2 := by
  have b := case_ii_aux (d := d) (e := e) (by omega : 3 ≤ j) (by omega : 0 < j) hjr
  have h := g10_mono (show 0 + 1 ≤ 5 by omega) hj
  have hd := delta_pos (d := d) (show 1 ≤ j by omega)
  norm_num [g10] at h
  norm_num [g10] at b
  linarith

/-- All unrestricted natural-number cases of S10.1. The size assumptions are exactly the conclusions of S9. -/
theorem psiR_gt_two {j d e r k : ℕ} (hj : 2 ≤ j) (hlarge : j ≤ r → 5 ≤ j) (hkr : k ≤ r) :
    2 < PsiR j d e r k := by
  rcases le_or_gt j k with hjk | hkj
  · have h := case_i (d := d) (e := e) hj hjk hkr
    have hj' : (2 : ℚ) ≤ j := by exact_mod_cast hj
    have hk' : (j : ℚ) ≤ k := by exact_mod_cast hjk
    have hr' : (k : ℚ) ≤ r := by exact_mod_cast hkr
    have a : 0 ≤ ((r : ℚ) - j) / (2 * (1 + (r : ℚ)) * (2 + (r : ℚ))) := div_nonneg (by linarith) (by positivity)
    have b : 0 ≤ ((k : ℚ) - j) / (2 * (1 + (k : ℚ)) * (2 + (k : ℚ))) := div_nonneg (by linarith) (by positivity)
    have c : 0 ≤ ((j : ℚ) - 2) * ((r : ℚ) - k) / (2 * (2 + (r : ℚ)) * (2 + (k : ℚ))) :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
    have dd := delta_pos (d := d) (show 1 ≤ j by omega)
    have ee : 0 ≤ (j : ℚ) / (2 * (1 + (j : ℚ)) * (2 + (j : ℚ))) := by positivity
    linarith
  · rcases le_or_gt j r with hjr | hrj
    · have h := case_ii (d := d) (e := e) (hlarge hjr) hkj hjr
      have dd := delta_pos (d := d) (show 1 ≤ j by omega)
      have a : 0 ≤ (k : ℚ) / (((k : ℚ) + 2) * ((k : ℚ) + 3)) := by positivity
      linarith
    · have h := case_iii (d := d) (e := e) (by omega : r + 1 ≤ j) hkr
      have hc := correction_nonneg (by omega : r + 1 ≤ j) hkr
      have hm := chi_mono (show r + 2 ≤ j + 1 by omega)
      have hb := chi_base r
      linarith

theorem psiN_gt_two {j d e k q : ℕ} (hj : 2 ≤ j) (hlarge : j ≤ k + q → 5 ≤ j) :
    2 < PsiN j d e k q := psiR_gt_two hj hlarge (by omega)

end Erdos643R3.GeneralizedPsi
