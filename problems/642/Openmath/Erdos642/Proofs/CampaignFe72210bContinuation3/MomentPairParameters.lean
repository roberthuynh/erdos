import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentHostParameters
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentOccupationAbsorption

/-! Exact fixed-root prefactor and weighted threshold for the new moment-host times. -/
namespace Erdos642.CampaignFe72210bContinuation3.MomentPairParameters
open Erdos642.CampaignFe72210b
open MomentSAParameters
open MomentHostParameters

/-- The order criterion and actual ceiling pay the later fixed-root time scale. -/
theorem gamma_time_lower (N : ℕ) (hN : 3 ≤ N) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (horder : A*(k N γ:ℝ)^2*Real.log (N:ℝ) ≤ (N:ℝ)) :
    a*A*(Real.log (N:ℝ))^2/32 ≤ γ*(t N γ:ℝ) := by
  have hell := IntegrationParameters.log_order_gt_one N hN
  have hell0 : 0 < Real.log (N:ℝ) := by linarith
  have hA := A_pos
  have ha := a_pos
  have hb := block_length_bounds N hN γ hγ hγ1
  have hk : 0 < (k N γ:ℝ) := by exact_mod_cast (show 0<k N γ by omega)
  have hweak : A*(k N γ:ℝ)^2 ≤ (N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hell.le (show 0≤A*(k N γ:ℝ)^2 by positivity)
    nlinarith only [hh,horder]
  have ht := (time_bounds N γ (by omega) hweak).2.2.2.2.1
  have hts := (div_le_iff₀ (show 0<32*(k N γ:ℝ) by positivity)).mp ht
  have hNscaled := mul_le_mul_of_nonneg_left horder a_pos.le
  have htlarge : a*A*(k N γ:ℝ)*Real.log (N:ℝ) ≤ 32*(t N γ:ℝ) := by
    apply (mul_le_mul_iff_left₀ hk).mp
    nlinarith only [hts,hNscaled]
  have hgamma := mul_le_mul_of_nonneg_left htlarge hγ.le
  have hgk := mul_le_mul_of_nonneg_left hb.2.2.1
    (show 0≤a*A*Real.log (N:ℝ) by positivity)
  nlinarith only [hgamma,hgk]

/-- Actual200N prefactor is paid without a full-family occupation-time premise. -/
theorem fixed_root_prefactor_absorbed (N : ℕ) (hN : 3 ≤ N) (γ : ℝ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (horder : A*(k N γ:ℝ)^2*Real.log (N:ℝ) ≤ (N:ℝ)) :
    200*(N:ℝ)*Real.exp (-γ*(t N γ:ℝ)/(4*(10:ℝ)^14)) ≤
      Real.exp (-γ*(t N γ:ℝ)/(8*(10:ℝ)^14)) := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hell := IntegrationParameters.log_order_gt_one N hN
  have hell0 : 0 < Real.log (N:ℝ) := by linarith
  have hA := A_pos
  have ha := a_pos
  have htime := gamma_time_lower N hN γ hγ hγ1 horder
  have hc : (51200:ℝ)*(10:ℝ)^14 ≤ a*A :=
    (by norm_num : (51200:ℝ)*(10:ℝ)^14 ≤ (10:ℝ)^40).trans MomentOccupationAbsorption.aA_large
  have hcoef := mul_le_mul_of_nonneg_right hc (show 0≤Real.log (N:ℝ) by linarith)
  have hsquare : Real.log (N:ℝ) ≤ (Real.log (N:ℝ))^2 := by nlinarith
  have hsq := mul_le_mul_of_nonneg_left hsquare (show 0≤a*A by positivity)
  have hlog : Real.log (200*(N:ℝ)) ≤ 200*Real.log (N:ℝ) := by
    rw [Real.log_mul (by norm_num : (200:ℝ)≠0) (ne_of_gt hn)]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<200)
    linarith
  have hbudget : Real.log (200*(N:ℝ)) ≤ γ*(t N γ:ℝ)/(8*(10:ℝ)^14) := by
    have hsmall : 200*Real.log (N:ℝ) ≤ γ*(t N γ:ℝ)/(8*(10:ℝ)^14) := by
      apply (le_div_iff₀ (by positivity : (0:ℝ)<8*(10:ℝ)^14)).mpr
      nlinarith [htime,hcoef,hsq]
    exact hlog.trans hsmall
  calc
    _ = Real.exp (Real.log (200*(N:ℝ))-γ*(t N γ:ℝ)/(4*(10:ℝ)^14)) := by
      rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (by positivity)]
      simp only [neg_mul,neg_div]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [hbudget])

/-- New floor geometry and degree/order criteria pay the genuine3T edge threshold. -/
theorem weighted_threshold_ge_three_time (N d : ℕ) (hN : 3 ≤ N) (γ : ℝ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hdegree : A*(k N γ:ℝ)*Real.log (N:ℝ) ≤ (d:ℝ))
    (horder : A*(k N γ:ℝ)^2*Real.log (N:ℝ) ≤ (N:ℝ)) :
    3*(T N γ:ℝ) ≤ (d:ℝ)*(t N γ:ℝ)^2/((10:ℝ)^24*(N:ℝ)) := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hell := IntegrationParameters.log_order_gt_one N hN
  have hell0 : 0 < Real.log (N:ℝ) := by linarith
  have hA := A_pos
  have ha := a_pos
  have hb := block_length_bounds N hN γ hγ hγ1
  have hk : 0 < (k N γ:ℝ) := by exact_mod_cast (show 0<k N γ by omega)
  have hweak : A*(k N γ:ℝ)^2 ≤ (N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hell.le (show 0≤A*(k N γ:ℝ)^2 by positivity)
    nlinarith only [hh,horder]
  have hg := time_bounds N γ (by omega) hweak
  have hlow1 : (T N γ:ℝ)/16 ≤ (t N γ:ℝ) := hg.2.2.2.1
  have hlow2 : a*(N:ℝ)/(32*(k N γ:ℝ)) ≤ (t N γ:ℝ) := hg.2.2.2.2.1
  have hprod := mul_le_mul hlow1 hlow2
    (show 0≤a*(N:ℝ)/(32*(k N γ:ℝ)) by positivity) (Nat.cast_nonneg _)
  have hts : a*(N:ℝ)*(T N γ:ℝ) ≤ 512*(k N γ:ℝ)*(t N γ:ℝ)^2 := by
    have he : (T N γ:ℝ)/16*(a*(N:ℝ)/(32*(k N γ:ℝ))) =
      a*(N:ℝ)*(T N γ:ℝ)/(512*(k N γ:ℝ)) := by ring
    rw [he] at hprod
    have hh := (div_le_iff₀ (show 0<512*(k N γ:ℝ) by positivity)).mp hprod
    nlinarith
  have hdegreeBase : A*(k N γ:ℝ) ≤ (d:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hell.le (show 0≤A*(k N γ:ℝ) by positivity)
    nlinarith only [hh,hdegree]
  have hc : (1536:ℝ)*(10:ℝ)^24 ≤ a*A :=
    (by norm_num : (1536:ℝ)*(10:ℝ)^24 ≤ (10:ℝ)^40).trans MomentOccupationAbsorption.aA_large
  have hcNT := mul_le_mul_of_nonneg_right hc (show 0≤(N:ℝ)*(T N γ:ℝ) by positivity)
  have hdegreeScaled := mul_le_mul_of_nonneg_right hdegreeBase
    (show 0≤512*(t N γ:ℝ)^2 by positivity)
  have htimeScaled := mul_le_mul_of_nonneg_left hts A_pos.le
  have hfinal : 3*(T N γ:ℝ)*((10:ℝ)^24*(N:ℝ)) ≤ (d:ℝ)*(t N γ:ℝ)^2 := by
    nlinarith only [hcNT,hdegreeScaled,htimeScaled]
  exact (le_div_iff₀ (by positivity : (0:ℝ)<(10:ℝ)^24*(N:ℝ))).mpr hfinal

end Erdos642.CampaignFe72210bContinuation3.MomentPairParameters
