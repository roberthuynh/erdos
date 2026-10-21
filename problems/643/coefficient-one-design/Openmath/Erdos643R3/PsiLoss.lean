import Openmath.Erdos643R3.GeneralizedPsi

set_option autoImplicit false
namespace Erdos643R3.GeneralizedPsi
open G3hpArith

def lossJ (k m : ℕ) : ℚ := 1 / (2 + (k : ℚ)) - 1 / (2 + (k : ℚ) + m)
def lossE (k m : ℕ) : ℚ := 1 / (2 * (1 + (k : ℚ))) - 1 / (2 * (1 + (k : ℚ) + m))

theorem lossJ_lt (k m : ℕ) : lossJ k m < 1 / (2 + (k : ℚ)) := by
  unfold lossJ
  have : (0 : ℚ) < 1 / (2 + (k : ℚ) + m) := by positivity
  linarith

theorem lossE_lt (k m : ℕ) : lossE k m < 1 / (2 + (k : ℚ)) := by
  have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have h : 1 / (2 * (1 + (k : ℚ))) ≤ 1 / (2 + (k : ℚ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have : (0 : ℚ) < 1 / (2 * (1 + (k : ℚ) + m)) := by positivity
  unfold lossE
  linarith

theorem lossJ_one (k : ℕ) : lossJ k 1 = 1 / ((2 + (k : ℚ)) * (3 + (k : ℚ))) := by
  unfold lossJ
  push_cast
  field_simp; ring

theorem lossE_one (k : ℕ) : lossE k 1 = 1 / (2 * (1 + (k : ℚ)) * (2 + (k : ℚ))) := by
  unfold lossE
  push_cast
  field_simp; ring

theorem chi_margin {j r : ℕ} (hjr : r + 1 ≤ j) :
    2 + ((r : ℚ) + 1) / (((r : ℚ) + 2) * ((r : ℚ) + 3)) ≤ chi r (j + 1) := by
  have h := chi_mono (show r + 2 ≤ j + 1 by omega)
  have id : chi r (r + 2) = 2 + ((r : ℚ) + 1) / (((r : ℚ) + 2) * ((r : ℚ) + 3)) := by
    unfold chi
    push_cast
    field_simp; ring
  rwa [id] at h

theorem correction_zero {j r : ℕ} (hjr : r + 1 ≤ j) :
    (r : ℚ)^2 / (2 * ((r : ℚ) + 2)) ≤ correction j r 0 := by
  have b := bracket_bound (k := 0) hjr
  have hr : (0 : ℚ) ≤ r := Nat.cast_nonneg r
  have h := mul_le_mul_of_nonneg_left b hr
  simp only [Nat.cast_zero, add_zero] at h
  unfold correction
  simp only [Nat.cast_zero, add_zero, sub_zero]
  have id : (r : ℚ) * (((r : ℚ) + 1) / (2 * (2 + (r : ℚ))) - 1 / (2 * ((r : ℚ) + 2))) =
      (r : ℚ)^2 / (2 * ((r : ℚ) + 2)) := by field_simp; ring
  linarith

/-- S10 compensation for at least two exceptional slots. Both loss forms satisfy its bound. -/
theorem many_loss {j d e r k : ℕ} (hj : 2 ≤ j) (hlarge : j ≤ r → 5 ≤ j)
    (hkr : k ≤ r) (hr : 1 ≤ r) {L : ℚ} (hL : L < 1 / (2 + (k : ℚ))) :
    2 < PsiR j d e r k - L + 1 / 3 := by
  have hp := psiR_gt_two (d := d) (e := e) hj hlarge hkr
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst k
    rcases le_or_gt j r with hjr | hrj
    · have hz := case_ii_zero (d := d) (e := e) (hlarge hjr) hjr
      norm_num at hL
      linarith
    · have hc := case_iii (d := d) (e := e) (by omega : r + 1 ≤ j) (show 0 ≤ r by omega)
      have hchi := chi_margin (by omega : r + 1 ≤ j)
      have hz := correction_zero (by omega : r + 1 ≤ j)
      have hr' : (1 : ℚ) ≤ r := by exact_mod_cast hr
      have hm : (1 : ℚ) / 6 ≤ (r : ℚ)^2 / (2 * ((r : ℚ) + 2)) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith
      have hmpos : (0 : ℚ) < ((r : ℚ) + 1) / (((r : ℚ) + 2) * ((r : ℚ) + 3)) := by positivity
      norm_num at hL
      linarith
  · have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have : 1 / (2 + (k : ℚ)) ≤ (1 : ℚ) / 3 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith

/-- A stronger case-(iii) correction pays the single `J₁` loss. -/
theorem correction_pays_J {j r k : ℕ} (hjr : r + 1 ≤ j) (hkr : k < r) :
    lossJ k 1 ≤ correction j r k := by
  have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have hr : (k : ℚ) + 1 ≤ r := by exact_mod_cast hkr
  have b := bracket_bound (k := k) hjr
  have hb := mul_le_mul_of_nonneg_left b (show (0 : ℚ) ≤ r - k by linarith)
  rw [lossJ_one]
  unfold correction
  have id : ((r : ℚ) - k) * (((r : ℚ) + 1) / ((2 + (k : ℚ)) * (2 + (r : ℚ))) - 1 / (2 * ((r : ℚ) + 2))) =
      ((r : ℚ) - k) * (2 * r - k) / (2 * (2 + (k : ℚ)) * (2 + (r : ℚ))) := by
    field_simp; ring
  rw [id] at hb
  refine le_trans ?_ hb
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (0 : ℚ) ≤ r - k - 1 := by linarith
  have h2 : (0 : ℚ) ≤ (r - k - 1) * (2 * k + 4) := mul_nonneg h1 (by positivity)
  have h3 : (0 : ℚ) ≤ (r - k - 1)^2 := sq_nonneg _
  have key : (2 : ℚ) * (r + 2) ≤ (r - k) * (2 * r - k) * (k + 3) := by
    nlinarith [mul_nonneg hk (sq_nonneg ((r : ℚ) - k - 1)), mul_nonneg hk h1,
      mul_nonneg (sq_nonneg (k : ℚ)) h1, sq_nonneg (k : ℚ)]
  nlinarith [mul_le_mul_of_nonneg_left key (show (0 : ℚ) ≤ k + 2 by positivity)]

theorem loss_one_case_i {j k : ℕ} (hjk : j ≤ k) :
    lossJ k 1 ≤ 1 / (2 * (2 + (j : ℚ))) ∧ lossE k 1 ≤ 1 / (2 * (2 + (j : ℚ))) := by
  have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
  have hk : (j : ℚ) ≤ k := by exact_mod_cast hjk
  rw [lossJ_one, lossE_one]
  constructor <;> apply one_div_le_one_div_of_le (by positivity) <;> nlinarith

theorem loss_one_case_ii {k : ℕ} (hk : 1 ≤ k) :
    lossJ k 1 ≤ (k : ℚ) / (((k : ℚ) + 2) * ((k : ℚ) + 3)) ∧
    lossE k 1 ≤ (k : ℚ) / (((k : ℚ) + 2) * ((k : ℚ) + 3)) := by
  have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
  rw [lossJ_one, lossE_one]
  constructor
  · rw [show ((k : ℚ) + 2) * ((k : ℚ) + 3) = (2 + (k : ℚ)) * (3 + (k : ℚ)) by ring]
    exact div_le_div_of_nonneg_right hk' (by positivity)
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (show (0 : ℚ) ≤ k - 1 by linarith) (show (0 : ℚ) ≤ k * k + 4 * k + 6 by positivity)]

/-- In the `Eᵤ` single-loss case, retain `e ≥ 1` and pay the loss directly from the e-terms. -/
theorem e_part_loss {j e k : ℕ} (he : 1 ≤ e) (hkj : k + 1 ≤ j) :
    (k : ℚ) / (2 * (1 + (j : ℚ))) ≤
      (e : ℚ) / (2 * (1 + (k : ℚ))) + (k : ℚ) / (2 * (1 + (j : ℚ) + e)) - lossE k 1 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le he
  have h := e_part (e := a) (show k + 1 ≤ j + 1 by omega)
  have hj : (k : ℚ) + 1 ≤ j := by exact_mod_cast hkj
  have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have b : (k : ℚ) / (2 * (1 + (j : ℚ))) ≤
      1 / (2 * (2 + (k : ℚ))) + (k : ℚ) / (2 * (2 + (j : ℚ))) := by
    have diff : (k : ℚ) / (2 * (1 + (j : ℚ))) - (k : ℚ) / (2 * (2 + (j : ℚ))) =
        (k : ℚ) / (2 * (1 + (j : ℚ)) * (2 + (j : ℚ))) := by field_simp; ring
    have le : (k : ℚ) / (2 * (1 + (j : ℚ)) * (2 + (j : ℚ))) ≤ 1 / (2 * (2 + (k : ℚ))) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  unfold lossE
  push_cast at h ⊢
  have id : ((1 : ℚ) + a) / (2 * (1 + (k : ℚ))) -
      (1 / (2 * (1 + (k : ℚ))) - 1 / (2 * (1 + (k : ℚ) + 1))) =
      (a : ℚ) / (2 * (1 + (k : ℚ))) + 1 / (2 * (2 + (k : ℚ))) := by field_simp; ring
  have hn : 1 + ((j : ℚ) + 1) + a = 1 + (j : ℚ) + (1 + a) := by ring
  have hn2 : 1 + ((j : ℚ) + 1) = 2 + (j : ℚ) := by ring
  rw [hn, hn2] at h
  linarith

theorem case_iii_E_loss {j d e r k : ℕ} (hjr : r + 1 ≤ j) (hkr : k ≤ r) (he : 1 ≤ e) :
    chi r (j + 1) + correction j r k ≤ PsiR j d e r k - lossE k 1 := by
  have he' := e_part_loss he (show k + 1 ≤ j by omega)
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

/-- Single-slot compensation, with the nonnegative surplus and its S9 bound explicit. -/
theorem single_J_loss {j d e r k : ℕ} (hj : 2 ≤ j) (hlarge : j ≤ r → 5 ≤ j)
    (hkr : k < r) {sigma : ℚ} (hs : 0 ≤ sigma)
    (hss : j ≤ r → 1 / (2 * (2 + (j : ℚ))) ≤ sigma) :
    2 < PsiR j d e r k - lossJ k 1 + sigma := by
  have hp := psiR_gt_two (d := d) (e := e) hj hlarge (by omega : k ≤ r)
  rcases le_or_gt j k with hjk | hkj
  · have h := (loss_one_case_i hjk).1
    have h' := hss (by omega)
    linarith
  · rcases le_or_gt j r with hjr | hrj
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · subst k
        have h := case_ii_zero (d := d) (e := e) (hlarge hjr) hjr
        norm_num [lossJ]
        linarith
      · have h := case_ii (d := d) (e := e) (hlarge hjr) hkj hjr
        have h' := (loss_one_case_ii hk).1
        have hd := delta_pos (d := d) (show 1 ≤ j by omega)
        linarith
    · have h := case_iii (d := d) (e := e) (by omega : r + 1 ≤ j) (by omega : k ≤ r)
      have h' := correction_pays_J (by omega : r + 1 ≤ j) hkr
      have hc := chi_mono (show r + 2 ≤ j + 1 by omega)
      have hc' := chi_base r
      linarith

theorem single_E_loss {j d e r k : ℕ} (hj : 2 ≤ j) (hlarge : j ≤ r → 5 ≤ j)
    (hkr : k < r) (he : 1 ≤ e) {sigma : ℚ} (hs : 0 ≤ sigma)
    (hss : j ≤ r → 1 / (2 * (2 + (j : ℚ))) ≤ sigma) :
    2 < PsiR j d e r k - lossE k 1 + sigma := by
  have hp := psiR_gt_two (d := d) (e := e) hj hlarge (by omega : k ≤ r)
  rcases le_or_gt j k with hjk | hkj
  · have h := (loss_one_case_i hjk).2
    have h' := hss (by omega)
    linarith
  · rcases le_or_gt j r with hjr | hrj
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · subst k
        have h := case_ii_zero (d := d) (e := e) (hlarge hjr) hjr
        norm_num [lossE]
        linarith
      · have h := case_ii (d := d) (e := e) (hlarge hjr) hkj hjr
        have h' := (loss_one_case_ii hk).2
        have hd := delta_pos (d := d) (show 1 ≤ j by omega)
        linarith
    · have h := case_iii_E_loss (d := d) (by omega : r + 1 ≤ j) (by omega : k ≤ r) he
      have hc := correction_nonneg (by omega : r + 1 ≤ j) (by omega : k ≤ r)
      have hm := chi_mono (show r + 2 ≤ j + 1 by omega)
      have hb := chi_base r
      linarith

def exceptionalLoss (inJ : Bool) (k m : ℕ) : ℚ := if inJ then lossJ k m else lossE k m

def surplus (S1 : ℚ) (m : ℕ) : ℚ := if m = 0 then 0 else if m = 1 then S1 - 1 else 1 / 3

/-- All arithmetic cases of S10, before applying the combinatorial lower bound on `U⁻ + S1`. -/
theorem loss_compensated {j d e r k m : ℕ} {inJ : Bool} {S1 : ℚ}
    (hj : 2 ≤ j) (hlarge : j ≤ r → 5 ≤ j) (hr : 1 ≤ r) (hkm : k + m ≤ r)
    (hE : inJ = false → 0 < m → 1 ≤ e) (hS1 : 1 ≤ S1)
    (hS9 : j ≤ r → 1 / (2 * (2 + (j : ℚ))) ≤ S1 - 1) :
    2 < PsiR j d e r k - exceptionalLoss inJ k m + surplus S1 m := by
  by_cases hm0 : m = 0
  · subst m
    have hp := psiR_gt_two (d := d) (e := e) hj hlarge (by omega : k ≤ r)
    simpa [exceptionalLoss, lossJ, lossE, surplus] using hp
  · by_cases hm1 : m = 1
    · subst m
      cases hJ : inJ
      · have h := single_E_loss (d := d) hj hlarge (by omega : k < r)
          (hE hJ (by omega)) (show 0 ≤ S1 - 1 by linarith) hS9
        simpa [exceptionalLoss, surplus] using h
      · have h := single_J_loss (d := d) (e := e) hj hlarge (by omega : k < r)
          (show 0 ≤ S1 - 1 by linarith) hS9
        simpa [exceptionalLoss, surplus] using h
    · have hl : exceptionalLoss inJ k m < 1 / (2 + (k : ℚ)) := by
        cases inJ
        · exact lossE_lt k m
        · exact lossJ_lt k m
      have h := many_loss (d := d) (e := e) hj hlarge (by omega : k ≤ r) hr hl
      simpa [surplus, hm0, hm1] using h

/-- Lemma S10's arithmetic implication. The host must supply S3/S7 bounds, S1 ≥ 1, and its actual loss location. -/
theorem lemmaS10_arith {j d e r k m : ℕ} {inJ : Bool} {S1 Uminus : ℚ}
    (hr : 1 ≤ r) (hkm : k + m ≤ r) (hE : inJ = false → 0 < m → 1 ≤ e)
    (hS1 : 1 ≤ S1) (hS3 : L9 j d r ≤ S1) (hdef : S1 < 13 / 12)
    (hbound : PsiR j d e r k - exceptionalLoss inJ k m ≤ Uminus + S1) :
    2 < Uminus + S1 + surplus S1 m := by
  have h9 := lemma9_arith hr hS3 hdef
  have h := loss_compensated (d := d) h9.1 (fun h => (h9.2 h).1) hr hkm hE hS1 (fun h => (h9.2 h).2)
  linarith

end Erdos643R3.GeneralizedPsi
