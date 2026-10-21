import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentHostParameters
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentOccupationAbsorption

namespace Erdos642.Adaptive20261018.Parameters
open Erdos642.CampaignFe72210bContinuation3
open MomentSAParameters

noncomputable def Astar : ℝ := (10 : ℝ)^2000
noncomputable def theta (N : ℕ) : ℝ := 1 / Real.sqrt (Real.log (N : ℝ))
noncomputable def r (N : ℕ) : ℕ := ⌈4 * Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))⌉₊ + 100

structure Hstar (N d : ℕ) (γ Λ : ℝ) : Prop where
  hN : 3 ≤ N
  log_large : Real.exp 4 ≤ Real.log (N : ℝ)
  gamma_pos : 0 < γ
  gamma_cap : γ ≤ 1
  lambda_ge_one : 1 ≤ Λ
  degree : Astar * (MomentHostParameters.k N γ : ℝ) * r N ≤ d
  order : Astar * (MomentHostParameters.k N γ : ℝ)^2 * Real.log (N : ℝ) ≤ N
  moment : Astar * Λ * (MomentHostParameters.k N γ : ℝ) * Real.log (N : ℝ)^2 ≤ (d : ℝ)^2 * γ

theorem A_le_Astar : A ≤ Astar := by
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) (by norm_num : (1000 : ℕ) ≤ 2000)

theorem Astar_pos : 0 < Astar := by unfold Astar; positivity

theorem r_ge_one (N : ℕ) : 1 ≤ r N := by unfold r; omega

theorem loglog_ge_four {z : ℝ} (hz : Real.exp 4 ≤ z) : 4 ≤ Real.log z := by
  have hp : 0 < z := (Real.exp_pos _).trans_le hz
  exact (Real.le_log_iff_exp_le hp).mpr hz

theorem r_le_ratio (N : ℕ) (hz : Real.exp 4 ≤ Real.log (N : ℝ)) :
    (r N : ℝ) ≤ 105 * Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) := by
  let z := Real.log (N : ℝ)
  have hzpos : 0 < z := (Real.exp_pos _).trans_le hz
  have hl : 4 ≤ Real.log z := loglog_ge_four hz
  have hlpos : 0 < Real.log z := by linarith
  have hlog : Real.log z ≤ z := (Real.log_le_sub_one_of_pos hzpos).trans (by linarith)
  have hratio : 1 ≤ z / Real.log z := (le_div_iff₀ hlpos).mpr (by simpa using hlog)
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ 4*z/Real.log z by positivity)).le
  have hr : (r N : ℝ) = (⌈4*z/Real.log z⌉₊ : ℝ) + 100 := by simp [r,z]
  rw [hr]
  have he : 105*z/Real.log z = 105*(z/Real.log z) := by ring
  rw [he]
  have he' : 4*z/Real.log z = 4*(z/Real.log z) := by ring
  rw [he'] at hc
  rw [he']
  linarith

theorem r_le_block (N : ℕ) (γ : ℝ) (hN : 3 ≤ N)
    (hz : Real.exp 4 ≤ Real.log (N : ℝ)) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (r N : ℝ) ≤ 27 * (MomentHostParameters.k N γ : ℝ) := by
  have hr := r_le_ratio N hz
  have hl := loglog_ge_four hz
  have hp : 0 < Real.log (N : ℝ) := (Real.exp_pos _).trans_le hz
  have hk := (MomentHostParameters.block_length_bounds N hN γ hγ hγ1).2.1
  have hdiv : 105*Real.log (N : ℝ)/Real.log (Real.log (N : ℝ)) ≤ 27*Real.log (N : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log (Real.log (N : ℝ)))).mpr
    nlinarith [mul_le_mul_of_nonneg_left hl hp.le]
  linarith

theorem theta_bounds (N : ℕ) (hz : Real.exp 4 ≤ Real.log (N : ℝ)) :
    0 < theta N ∧ theta N < 1 ∧ (theta N)^2 = 1 / Real.log (N : ℝ) := by
  have h4 : (1 : ℝ) < Real.exp 4 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hz1 : 1 < Real.log (N : ℝ) := h4.trans_le hz
  have hs : 1 < Real.sqrt (Real.log (N : ℝ)) := by
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by simpa using hz1)
  unfold theta
  refine ⟨by positivity, (div_lt_one (by positivity)).mpr hs, ?_⟩
  rw [div_pow, one_pow, Real.sq_sqrt (by linarith)]

theorem reductions {N d : ℕ} {γ Λ : ℝ} (h : Hstar N d γ Λ) :
    100000000 ≤ d ∧ A*(MomentHostParameters.k N γ : ℝ) ≤ d ∧
    A*(MomentHostParameters.k N γ : ℝ)^2 ≤ N ∧
    A*Λ*(MomentHostParameters.k N γ : ℝ) ≤ (d : ℝ)^2*γ ∧ Λ ≤ (d : ℝ)^2 := by
  have hz := Erdos642.CampaignFe72210b.IntegrationParameters.log_order_gt_one N h.hN
  have hk := (MomentHostParameters.block_length_bounds N h.hN γ h.gamma_pos h.gamma_cap).1
  have hkreal : (4 : ℝ) ≤ MomentHostParameters.k N γ := by exact_mod_cast hk
  have hr : (1 : ℝ) ≤ r N := by exact_mod_cast r_ge_one N
  have hΛ : 0 ≤ Λ := by linarith [h.lambda_ge_one]
  have hA := A_pos
  have hAstar := Astar_pos
  have hd : A*(MomentHostParameters.k N γ : ℝ) ≤ d := calc
    _ ≤ Astar*(MomentHostParameters.k N γ : ℝ) := by gcongr; exact A_le_Astar
    _ ≤ Astar*(MomentHostParameters.k N γ : ℝ)*r N := le_mul_of_one_le_right (mul_nonneg hAstar.le (Nat.cast_nonneg _)) hr
    _ ≤ _ := h.degree
  have hN : A*(MomentHostParameters.k N γ : ℝ)^2 ≤ N := calc
    _ ≤ Astar*(MomentHostParameters.k N γ : ℝ)^2 := by gcongr; exact A_le_Astar
    _ ≤ Astar*(MomentHostParameters.k N γ : ℝ)^2*Real.log (N : ℝ) := le_mul_of_one_le_right (mul_nonneg hAstar.le (sq_nonneg _)) hz.le
    _ ≤ _ := h.order
  have hM : A*Λ*(MomentHostParameters.k N γ : ℝ) ≤ (d : ℝ)^2*γ := calc
    _ ≤ Astar*Λ*(MomentHostParameters.k N γ : ℝ) := by gcongr; exact A_le_Astar
    _ ≤ Astar*Λ*(MomentHostParameters.k N γ : ℝ)*Real.log (N : ℝ)^2 := le_mul_of_one_le_right (mul_nonneg (mul_nonneg hAstar.le hΛ) (Nat.cast_nonneg _)) (one_le_pow₀ hz.le)
    _ ≤ _ := h.moment
  have hcoeff : 1 ≤ A*(MomentHostParameters.k N γ : ℝ) := by nlinarith [MomentHostParameters.large_constants.1]
  have hdlarge : (100000000 : ℝ) ≤ d := by nlinarith [MomentHostParameters.large_constants.1]
  refine ⟨by exact_mod_cast hdlarge, hd, hN, hM, ?_⟩
  have hm := mul_le_mul_of_nonneg_right hcoeff hΛ
  have hg := mul_le_mul_of_nonneg_left h.gamma_cap (sq_nonneg (d : ℝ))
  nlinarith

theorem order_log {N d : ℕ} {γ Λ : ℝ} (h : Hstar N d γ Λ) :
    A*(MomentHostParameters.k N γ : ℝ)^2*Real.log (N : ℝ) ≤ N := by
  have hz := Erdos642.CampaignFe72210b.IntegrationParameters.log_order_gt_one N h.hN
  calc
    _ ≤ Astar*(MomentHostParameters.k N γ : ℝ)^2*Real.log (N : ℝ) := by gcongr; exact A_le_Astar
    _ ≤ _ := h.order

theorem smoothing_tail (N : ℕ) (hN : 3 ≤ N) (d Λ : ℝ)
    (hz : Real.exp 4 ≤ Real.log (N : ℝ)) (hd : 0 < d) (hΛ : 1 ≤ Λ)
    (hΛd : Λ ≤ d^2) :
    MomentSmoothingParameters.scale N d Λ * (theta N)^(r N-1) ≤
      MomentSmoothingParameters.mu0/1024 := by
  have hp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hzpos : 0 < Real.log (N : ℝ) := (Real.exp_pos _).trans_le hz
  have hl := loglog_ge_four hz
  have hlpos : 0 < Real.log (Real.log (N : ℝ)) := by linarith
  have ht := theta_bounds N hz
  have ha := MomentSmoothingParameters.argument_pos N hN d Λ hd hΛ
  have hbound := MomentSmoothingParameters.argument_le_power_sqrt N hN d Λ hd hΛ hΛd
  have hlog := Real.log_le_log ha hbound
  rw [Real.log_mul (by positivity : (10 : ℝ)^19 ≠ 0)
    (ne_of_gt (Real.sqrt_pos.mpr hp)), Real.log_pow, Real.log_sqrt hp.le] at hlog
  have harg : Real.log (MomentSmoothingParameters.argument N d Λ) ≤
      57 + Real.log (N : ℝ)/2 := by
    have hten := MomentSmoothingParameters.log_ten_lt_three
    norm_num only [Nat.cast_ofNat] at hlog
    linarith
  have htheta : Real.log (theta N) = -Real.log (Real.log (N : ℝ))/2 := by
    unfold theta
    rw [Real.log_div one_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hzpos)),
      Real.log_one, Real.log_sqrt hzpos.le]
    ring
  have hceil := Nat.le_ceil (4*Real.log (N : ℝ)/Real.log (Real.log (N : ℝ)))
  have hr : (r N-1 : ℕ) = ⌈4*Real.log (N : ℝ)/Real.log (Real.log (N : ℝ))⌉₊+99 := by
    unfold r; omega
  have hrbound : 4*Real.log (N : ℝ)+99*Real.log (Real.log (N : ℝ)) ≤
      (r N-1 : ℕ)*Real.log (Real.log (N : ℝ)) := by
    have hh := (div_le_iff₀ hlpos).mp hceil
    rw [hr, Nat.cast_add, Nat.cast_ofNat]
    nlinarith
  have hprod : 0 < MomentSmoothingParameters.argument N d Λ * (theta N)^(r N-1) := mul_pos ha (pow_pos ht.1 _)
  have hlogprod : Real.log (MomentSmoothingParameters.argument N d Λ * (theta N)^(r N-1)) ≤ 0 := by
    rw [Real.log_mul (ne_of_gt ha) (ne_of_gt (pow_pos ht.1 _)), Real.log_pow, htheta]
    nlinarith
  have hle : MomentSmoothingParameters.argument N d Λ * (theta N)^(r N-1) ≤ 1 := by
    apply (Real.log_le_log_iff hprod zero_lt_one).mp
    simpa using hlogprod
  have hmu := MomentSmoothingParameters.mu0_pos
  unfold MomentSmoothingParameters.argument at hle
  have hh := (div_le_iff₀ hmu).mp (show
      1024 * (MomentSmoothingParameters.scale N d Λ * (theta N)^(r N-1)) /
        MomentSmoothingParameters.mu0 ≤ 1 by convert hle using 1 <;> ring)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1024)).mpr
  nlinarith

end Erdos642.Adaptive20261018.Parameters
