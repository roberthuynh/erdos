import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentOccupationAbsorption
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos642.Joint20261019.EnergyRates

/-- The absolute forest mean used by the common-family estimate. -/
noncomputable abbrev mu0 : ℝ :=
  Erdos642.CampaignFe72210bContinuation3.MomentOccupationAbsorption.mu0

theorem mu0_pos : 0 < mu0 := by norm_num [mu0, Erdos642.CampaignFe72210bContinuation3.MomentOccupationAbsorption.mu0]

theorem fast_rate (μ n t : ℝ) (hμ : mu0 ≤ μ) (hn : 0 ≤ n)
    (hthird : t / 3 ≤ n) : t / (10 : ℝ)^35 ≤ μ^2*n/4096 := by
  have hμp : 0 ≤ μ := mu0_pos.le.trans hμ
  have hs : mu0^2 ≤ μ^2 := sq_le_sq₀ mu0_pos.le hμp |>.2 hμ
  have hc : 3 / (10 : ℝ)^35 ≤ μ^2/4096 := by
    norm_num [mu0, Erdos642.CampaignFe72210bContinuation3.MomentOccupationAbsorption.mu0] at hs ⊢
    nlinarith only [hs]
  have hh := mul_le_mul_of_nonneg_right hc hn
  have ht := mul_le_mul_of_nonneg_left hthird (by positivity : 0 ≤ 3/(10:ℝ)^35)
  nlinarith only [hh, ht]

theorem slow_rate (μ n t γ : ℝ) (hμ : mu0 ≤ μ) (hn : 0 ≤ n)
    (hthird : t / 3 ≤ n) (hγ : 0 ≤ γ) : γ*t/(10:ℝ)^35 ≤ γ*μ^2*n/32 := by
  have hf := fast_rate μ n t hμ hn hthird
  have hh := mul_le_mul_of_nonneg_left hf hγ
  have hp : 0 ≤ γ*μ^2*n := mul_nonneg (mul_nonneg hγ (sq_nonneg μ)) hn
  nlinarith only [hh, hp]

theorem log_net_base (μ : ℝ) (hμ : mu0 ≤ μ) : Real.log (65/μ) ≤ 200 := by
  have hp : 0 < μ := mu0_pos.trans_le hμ
  have hb : 65/μ ≤ (10:ℝ)^17 := by
    apply (div_le_iff₀ hp).mpr
    have hh := mul_le_mul_of_nonneg_left hμ (by positivity : 0 ≤ (10:ℝ)^17)
    norm_num [mu0, Erdos642.CampaignFe72210bContinuation3.MomentOccupationAbsorption.mu0] at hh ⊢
    linarith
  have hl := Real.log_le_log (by positivity : 0 < 65/μ) hb
  rw [Real.log_pow] at hl
  have h10 : Real.log (10:ℝ) ≤ 9 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10)
    norm_num at hh ⊢
    exact hh
  norm_num at hl
  linarith

theorem fast_exp (μ n t : ℝ) (hμ : mu0 ≤ μ) (hn : 0 ≤ n)
    (hthird : t/3 ≤ n) :
    Real.exp (-μ^2*n/4096) ≤ Real.exp (-t/(10:ℝ)^35) := by
  apply Real.exp_le_exp.mpr
  have h := fast_rate μ n t hμ hn hthird
  linarith

theorem slow_exp (μ n t γ : ℝ) (hμ : mu0 ≤ μ) (hn : 0 ≤ n)
    (hthird : t/3 ≤ n) (hγ : 0 ≤ γ) :
    Real.exp (-γ*μ^2*n/32) ≤ Real.exp (-γ*t/(10:ℝ)^35) := by
  apply Real.exp_le_exp.mpr
  have h := slow_rate μ n t γ hμ hn hthird hγ
  linarith

theorem net_card_exp (μ : ℝ) (D : ℕ) (hμ : mu0 ≤ μ) :
    (65/μ)^D ≤ Real.exp (200*(D:ℝ)) := by
  have hp : 0 < μ := mu0_pos.trans_le hμ
  calc
    _ = Real.exp (Real.log ((65/μ)^D)) := (Real.exp_log (by positivity)).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by
      rw [Real.log_pow]
      have h := mul_le_mul_of_nonneg_left (log_net_base μ hμ) (Nat.cast_nonneg D : (0:ℝ)≤D)
      nlinarith only [h])

end Erdos642.Joint20261019.EnergyRates
