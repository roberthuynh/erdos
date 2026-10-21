import Openmath.Erdos642.Proofs.Adaptive20261018.Parameters

namespace Erdos642.Joint20261019.Parameters
open Erdos642.CampaignFe72210bContinuation3
open MomentSAParameters

noncomputable def Anew : ℝ := (10 : ℝ)^3000

structure Hnew (N d : ℕ) (γ Λ : ℝ) : Prop where
  hN : 3 ≤ N
  log_large : Real.exp 4 ≤ Real.log (N : ℝ)
  gamma_pos : 0 < γ
  gamma_cap : γ ≤ 1
  lambda_ge_one : 1 ≤ Λ
  degree : Anew * (MomentHostParameters.k N γ : ℝ) ≤ d
  order : Anew * (MomentHostParameters.k N γ : ℝ)^2 * Real.log (N : ℝ) ≤ N
  moment : Anew * Λ * (MomentHostParameters.k N γ : ℝ) ≤ (d : ℝ)^2 * γ

theorem Anew_pos : 0 < Anew := by unfold Anew; positivity
theorem A_le_Anew : A ≤ Anew := by
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) (by norm_num : (1000 : ℕ) ≤ 3000)

theorem reductions {N d : ℕ} {γ Λ : ℝ} (h : Hnew N d γ Λ) :
    100000000 ≤ d ∧ A*(MomentHostParameters.k N γ : ℝ) ≤ d ∧
    A*(MomentHostParameters.k N γ : ℝ)^2 ≤ N ∧
    A*Λ*(MomentHostParameters.k N γ : ℝ) ≤ (d : ℝ)^2*γ ∧ Λ ≤ (d : ℝ)^2 := by
  have hz := Erdos642.CampaignFe72210b.IntegrationParameters.log_order_gt_one N h.hN
  have hk := (MomentHostParameters.block_length_bounds N h.hN γ h.gamma_pos h.gamma_cap).1
  have hkreal : (4 : ℝ) ≤ MomentHostParameters.k N γ := by exact_mod_cast hk
  have hΛ : 0 ≤ Λ := by linarith [h.lambda_ge_one]
  have hA := A_pos
  have hAn := Anew_pos
  have hd : A*(MomentHostParameters.k N γ : ℝ) ≤ d := calc
    _ ≤ Anew*(MomentHostParameters.k N γ : ℝ) := by gcongr; exact A_le_Anew
    _ ≤ _ := h.degree
  have hN : A*(MomentHostParameters.k N γ : ℝ)^2 ≤ N := calc
    _ ≤ Anew*(MomentHostParameters.k N γ : ℝ)^2 := by gcongr; exact A_le_Anew
    _ ≤ Anew*(MomentHostParameters.k N γ : ℝ)^2*Real.log (N : ℝ) :=
      le_mul_of_one_le_right (mul_nonneg hAn.le (sq_nonneg _)) hz.le
    _ ≤ _ := h.order
  have hM : A*Λ*(MomentHostParameters.k N γ : ℝ) ≤ (d : ℝ)^2*γ := calc
    _ ≤ Anew*Λ*(MomentHostParameters.k N γ : ℝ) := by gcongr; exact A_le_Anew
    _ ≤ _ := h.moment
  have hcoeff : 1 ≤ A*(MomentHostParameters.k N γ : ℝ) := by
    nlinarith [MomentHostParameters.large_constants.1]
  have hdlarge : (100000000 : ℝ) ≤ d := by
    nlinarith [MomentHostParameters.large_constants.1]
  refine ⟨by exact_mod_cast hdlarge, hd, hN, hM, ?_⟩
  have hm := mul_le_mul_of_nonneg_right hcoeff hΛ
  have hg := mul_le_mul_of_nonneg_left h.gamma_cap (sq_nonneg (d : ℝ))
  nlinarith

theorem order_log {N d : ℕ} {γ Λ : ℝ} (h : Hnew N d γ Λ) :
    A*(MomentHostParameters.k N γ : ℝ)^2*Real.log (N : ℝ) ≤ N := by
  have hz := Erdos642.CampaignFe72210b.IntegrationParameters.log_order_gt_one N h.hN
  calc
    _ ≤ Anew*(MomentHostParameters.k N γ : ℝ)^2*Real.log (N : ℝ) := by
      gcongr; exact A_le_Anew
    _ ≤ _ := h.order

end Erdos642.Joint20261019.Parameters
