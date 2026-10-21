import Openmath.Erdos642.Proofs.Adaptive20261018.Parameters
namespace Erdos642.Adaptive20261018.Absorption
open Erdos642.CampaignFe72210bContinuation3
open MomentSAParameters MomentOccupationAbsorption Parameters

theorem aAstar_large : (10 : ℝ)^40 ≤ a*Astar :=
  MomentOccupationAbsorption.aA_large.trans (mul_le_mul_of_nonneg_left A_le_Astar a_pos.le)

private theorem coefficient_exp_le (C R B : ℝ) (hC : 0 < C)
    (hlog : Real.log C ≤ R - B) : C * Real.exp (-R) ≤ Real.exp (-B) := by
  calc
    _ = Real.exp (Real.log C - R) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hC]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hlog])

theorem fast_budget (N k t m : ℕ) (ell d : ℝ) (r : ℕ)
    (hell : 1 < ell) (hk : ell ≤ k) (hr : 1 ≤ r) (hrcap : (r : ℝ) ≤ 27*k)
    (hdegree : Astar * k * r ≤ d) (horder : Astar * (k : ℝ)^2 * ell ≤ N)
    (ht : a * N / (32 * k) ≤ (t : ℝ)) (hm : (m : ℝ) ≤ (N : ℝ) / d) :
    (m : ℝ) ≤ ((t : ℝ) / ((10 : ℝ)^35 * r)) / 4 ∧
      8 * ell ≤ (t : ℝ) / ((10 : ℝ)^35 * r) := by
  have hellpos : 0 < ell := by linarith
  have hkpos : (0 : ℝ) < k := hellpos.trans_le hk
  have hd : 0 < d := (mul_pos (mul_pos Astar_pos hkpos) (by exact_mod_cast (show 0 < r by omega))).trans_le hdegree
  have ht' : a * N ≤ (t : ℝ) * (32 * k) := (div_le_iff₀ (by positivity)).mp ht
  have hm' : (m : ℝ) * d ≤ N := (le_div_iff₀ hd).mp hm
  have hc : (6912 : ℝ) * (10 : ℝ)^35 ≤ a * Astar := by
    exact (by norm_num : (6912 : ℝ) * (10 : ℝ)^35 ≤ (10 : ℝ)^40).trans aAstar_large
  constructor
  · have hprod : (32 * (k : ℝ)) * (4 * (10 : ℝ)^35 * r * m) ≤ (32 * k) * t := by
      calc
        _ = (128 * (10 : ℝ)^35) * ((m : ℝ) * k * r) := by ring
        _ ≤ (a * Astar) * ((m : ℝ) * k * r) :=
          mul_le_mul_of_nonneg_right (by linarith only [hc]) (by positivity)
        _ = a * ((m : ℝ) * (Astar * k * r)) := by ring
        _ ≤ a * ((m : ℝ) * d) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdegree (Nat.cast_nonneg m)) a_pos.le
        _ ≤ a * N := mul_le_mul_of_nonneg_left hm' a_pos.le
        _ ≤ _ := by simpa only [mul_comm] using ht'
    have hcancel := le_of_mul_le_mul_left hprod (by positivity : 0 < 32 * (k : ℝ))
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    apply (le_div_iff₀ (by positivity : 0 < (10 : ℝ)^35 * (r : ℝ))).mpr
    nlinarith only [hcancel]
  · have hprod : (32 * (k : ℝ)) * ((8 * ell) * ((10 : ℝ)^35 * r)) ≤
        (32 * k) * t := by
      calc
        _ = (256 * (10 : ℝ)^35) * ((k : ℝ) * ell * r) := by ring
        _ ≤ (6912 * (10 : ℝ)^35) * ((k : ℝ)^2 * ell) := by
          have hh := mul_le_mul_of_nonneg_left hrcap (show 0 ≤ 256*(10:ℝ)^35*k*ell by positivity)
          nlinarith only [hh]
        _ ≤ (a * Astar) * ((k : ℝ)^2 * ell) := mul_le_mul_of_nonneg_right hc (by positivity)
        _ = a * (Astar * (k : ℝ)^2 * ell) := by ring
        _ ≤ a * N := mul_le_mul_of_nonneg_left horder a_pos.le
        _ ≤ _ := by simpa only [mul_comm] using ht'
    have hcancel := le_of_mul_le_mul_left hprod (by positivity : 0 < 32 * (k : ℝ))
    exact (le_div_iff₀ (by positivity : 0 < (10 : ℝ)^35 * (r : ℝ))).mpr hcancel

theorem fast_family_absorbed (N k t n r qF m : ℕ) (d μ : ℝ)
    (hN : 3 ≤ N) (hell : 1 < Real.log (N : ℝ)) (hk : Real.log (N : ℝ) ≤ k)
    (hdegree : Astar * k * r ≤ d)
    (horder : Astar * (k : ℝ)^2 * Real.log (N : ℝ) ≤ N)
    (ht : a * N / (32 * k) ≤ (t : ℝ)) (hn : (t : ℝ) / 3 ≤ n)
    (hr : 1 ≤ r) (hrcap : (r : ℝ) ≤ 27*k)
    (hμ : mu0 ≤ μ) (hμcap : μ ≤ 1 / 50)
    (hq : qF ≤ N) (hm : (m : ℝ) ≤ (N : ℝ) / d) :
    (qF : ℝ) * (2 : ℝ)^m * (1 + μ / 16) * Real.exp (-μ^2 * n / (256 * r)) ≤
      Real.exp (-(t : ℝ) / (2 * (10 : ℝ)^35 * r)) := by
  have hμpos : 0 < μ := mu0_pos.trans_le hμ
  have hF := fast_budget N k t m (Real.log N) d r hell hk hr hrcap hdegree horder ht hm
  have hrate := MomentOccupationAbsorption.fast_rate t n r (r : ℝ) μ (by exact_mod_cast (show 0 < r by omega)) hr (by nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]) hn hμ
  by_cases hq0 : qF = 0
  · simp only [hq0, Nat.cast_zero, zero_mul]
    exact (Real.exp_pos _).le
  · have hqpos : (0 : ℝ) < qF := by exact_mod_cast (Nat.pos_of_ne_zero hq0)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    let F := (t : ℝ) / ((10 : ℝ)^35 * r)
    let C := (2 * (qF : ℝ)) * (2 : ℝ)^m
    have hC : 0 < C := by dsimp [C]; positivity
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh ⊢
      exact hh
    have hlogq : Real.log (2 * (qF : ℝ)) ≤ 2 * Real.log (N : ℝ) := by
      calc
        _ ≤ Real.log (2 * (N : ℝ)) := Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left (by exact_mod_cast hq) (by norm_num))
        _ = Real.log 2 + Real.log (N : ℝ) := Real.log_mul (by norm_num) (ne_of_gt hNpos)
        _ ≤ _ := by linarith only [hlog2, hell]
    have hlogC : Real.log C ≤ F / 2 := by
      dsimp [C]
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have hmLog := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
      dsimp [F]
      nlinarith only [hlogq, hmLog, hF.1, hF.2]
    let R := μ^2 * n / (256 * r)
    change F ≤ R at hrate
    have hbound : C * Real.exp (-R) ≤ Real.exp (-(F / 2)) :=
      coefficient_exp_le C R (F / 2) hC (by linarith only [hlogC, hrate])
    calc
      _ = ((qF : ℝ) * (2 : ℝ)^m * Real.exp (-R)) * (1 + μ / 16) := by dsimp [R]; simp only [neg_mul, neg_div]; ring
      _ ≤ ((qF : ℝ) * (2 : ℝ)^m * Real.exp (-R)) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith only [hμcap] : 1 + μ / 16 ≤ 2) (by positivity)
      _ = C * Real.exp (-R) := by dsimp [C]; ring
      _ ≤ Real.exp (-(F / 2)) := hbound
      _ = _ := by congr 1; dsimp [F]; field_simp


theorem slow_family_absorbed (N k t n D : ℕ) (d γ Λ μ : ℝ)
    (hN : 3 ≤ N) (hell : 1 < Real.log (N : ℝ)) (hk : Real.log (N : ℝ) ≤ k)
    (hd : 0 < d) (hγ : 0 < γ)
    (hmoment : Astar * Λ * k * Real.log (N : ℝ)^2 ≤ d^2 * γ)
    (ht : a * N / (32 * k) ≤ (t : ℝ)) (hn : (t : ℝ) / 3 ≤ n)
    (hμ : mu0 ≤ μ) (hμcap : μ ≤ 1 / 50) (hD : 1 ≤ D)
    (hrank : (D : ℝ) ≤ Λ * N * Real.log (N : ℝ) / d^2) :
    (CoordinateGrid.alphabet N μ : ℝ)^D * (⌈2048 / μ⌉₊ : ℝ) * 100 * N *
        Real.exp (-γ * μ * n / 65536) ≤
      Real.exp (-γ * t / (2 * (10 : ℝ)^21)) := by
  have hellpos : 0 < Real.log (N : ℝ) := by linarith
  have hkpos : (0 : ℝ) < k := hellpos.trans_le hk
  have hkNat : 0 < k := by exact_mod_cast hkpos
  let L := Λ * Real.log (N : ℝ) / 16
  have hrankL : (D : ℝ) ≤ 16*L*N/d^2 := by dsimp [L]; convert hrank using 1 <;> ring
  have hL : 0 ≤ L := by
    have hpos : 0 < 16*L*N/d^2 := lt_of_lt_of_le (by exact_mod_cast (show 0 < D by omega)) hrankL
    by_contra hbad
    have hnL : L < 0 := lt_of_not_ge hbad
    have hnon : 16*L*N/d^2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg N)) (sq_nonneg d)
    linarith
  have hLambda : 0 ≤ Λ := by
    have hm : 0 ≤ Λ * Real.log (N : ℝ) := by dsimp [L] at hL; linarith
    exact nonneg_of_mul_nonneg_right (by simpa only [mul_comm] using hm) hellpos
  have hmomentL : A * L * k * Real.log (N : ℝ) ≤ d^2*γ := by
    calc
      _ = (A/16) * Λ * k * Real.log (N : ℝ)^2 := by dsimp [L]; ring
      _ ≤ Astar * Λ * k * Real.log (N : ℝ)^2 := by
        gcongr
        exact (by nlinarith [A_pos] : A/16 ≤ A).trans A_le_Astar
      _ ≤ _ := hmoment
  have hcoeff := slow_coefficient_log N D μ L d hN hell hμ hμcap hD hrankL
  have hbudget := slow_budget N k t (Real.log N) d γ L hellpos hkNat hd hγ hL hmomentL ht
  have hrate := slow_rate t n γ μ hγ hn hμ
  let C := (CoordinateGrid.alphabet N μ : ℝ)^D * levelCount μ * (100 * N)
  let R := γ * μ * n / 65536
  let S := γ * t / (10 : ℝ)^21
  have hlog : Real.log C ≤ S / 2 := by
    dsimp [C, S]
    calc
      _ ≤ 4800 * L * N * Real.log (N : ℝ) / d^2 := hcoeff.2
      _ ≤ γ * t / (2 * (10 : ℝ)^21) := hbudget
      _ = _ := by ring
  have hSR : S ≤ R := hrate
  have hbound : C * Real.exp (-R) ≤ Real.exp (-(S / 2)) :=
    coefficient_exp_le C R (S / 2) hcoeff.1 (by linarith only [hlog, hSR])
  calc
    _ = C * Real.exp (-R) := by dsimp [C, R, levelCount]; simp only [neg_mul, neg_div]; ring
    _ ≤ Real.exp (-(S / 2)) := hbound
    _ = _ := by congr 1; dsimp [S]; ring

end Erdos642.Adaptive20261018.Absorption
