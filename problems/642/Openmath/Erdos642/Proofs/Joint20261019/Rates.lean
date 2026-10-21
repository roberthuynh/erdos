import Openmath.Erdos642.Proofs.Joint20261019.Parameters
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentRarityParameters

namespace Erdos642.Joint20261019.Rates
open Erdos642.CampaignFe72210bContinuation3
open MomentSAParameters MomentHostParameters

private theorem rate_bound (q : ℕ) (t C : ℝ) (hC : 0<C)
    (h16 : (q:ℝ) ≤ 16*t) (hc : 384*beta*C ≤ 1) :
    12*beta*(q:ℝ) ≤ t/(2*C) := by
  have hm := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg q : (0:ℝ)≤q)
  apply (le_div_iff₀ (by positivity : 0<2*C)).mpr
  nlinarith only [h16,hm]

theorem three_rates (N : ℕ) (hN : 3≤N) (γ : ℝ) (hγ : 0<γ) (hγ1 : γ≤1)
    (horder : A*(k N γ:ℝ)^2*Real.log (N:ℝ) ≤ (N:ℝ)) :
    Real.exp (-(t N γ:ℝ)/(2*(10:ℝ)^35)) ≤ Real.exp (-12*beta*(q N γ:ℝ)) ∧
    Real.exp (-γ*(t N γ:ℝ)/(2*(10:ℝ)^35)) ≤ Real.exp (-12*beta*(q N γ:ℝ)) ∧
    Real.exp (-γ*(t N γ:ℝ)/(8*(10:ℝ)^14)) ≤ Real.exp (-12*beta*(q N γ:ℝ)) := by
  have hell := Erdos642.CampaignFe72210b.IntegrationParameters.log_order_gt_one N hN
  have hb := block_length_bounds N hN γ hγ hγ1
  have hweak : A*(k N γ:ℝ)^2 ≤ (N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hell.le (mul_nonneg A_pos.le (sq_nonneg (k N γ:ℝ)))
    nlinarith only [hh,horder]
  have ht := (time_bounds N γ (by omega) hweak).2.2.2.1
  have h16 : (q N γ:ℝ)*(k N γ:ℝ) ≤ 16*(t N γ:ℝ) := by
    change ((q N γ*k N γ:ℕ):ℝ)/16 ≤ _ at ht
    push_cast at ht
    linarith only [ht]
  have hq : (0:ℝ) ≤ (q N γ:ℝ) := Nat.cast_nonneg _
  have hk1 : (1:ℝ)≤k N γ := by exact_mod_cast (show 1≤k N γ by have := hb.1; omega)
  have hf : (q N γ:ℝ)≤16*(t N γ:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hk1 hq
    nlinarith only [hh,h16]
  have hg16 := mul_le_mul_of_nonneg_left h16 hγ.le
  have hgk : (q N γ:ℝ) ≤ (q N γ:ℝ)*(γ*(k N γ:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hb.2.2.1 hq
    nlinarith [hell]
  have hg : (q N γ:ℝ) ≤ 16*(γ*(t N γ:ℝ)) := by nlinarith only [hg16,hgk]
  have hfast := rate_bound (q N γ) (t N γ:ℝ) ((10:ℝ)^35)
    (by positivity) hf (by norm_num [beta])
  have hslow := rate_bound (q N γ) (γ*(t N γ:ℝ)) ((10:ℝ)^35)
    (by positivity) hg (by norm_num [beta])
  have hroot := rate_bound (q N γ) (γ*(t N γ:ℝ)) (4*(10:ℝ)^14)
    (by positivity) hg (by norm_num [beta])
  refine ⟨Real.exp_le_exp.mpr ?_,Real.exp_le_exp.mpr ?_,Real.exp_le_exp.mpr ?_⟩
  · simpa only [neg_div,neg_mul] using neg_le_neg hfast
  · simpa only [neg_div,neg_mul] using neg_le_neg hslow
  · have he : γ*(t N γ:ℝ)/(2*(4*(10:ℝ)^14)) = γ*(t N γ:ℝ)/(8*(10:ℝ)^14) := by ring
    rw [he] at hroot
    simpa only [neg_div,neg_mul] using neg_le_neg hroot

end Erdos642.Joint20261019.Rates
