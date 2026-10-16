import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentPairParameters

set_option maxRecDepth 2048
namespace Erdos642.CampaignFe72210bContinuation3.MomentRarityParameters
open Erdos642.CampaignFe72210b MomentSAParameters MomentHostParameters

private theorem rate_bound (q : ℕ) (t ell C : ℝ) (hell : 0<ell) (hC : 0<C)
    (h16 : (q:ℝ)*ell ≤ 16*t) (hc : 384*beta*C ≤ 1) :
    12*beta*(q:ℝ) ≤ t/(2*C*ell) := by
  have hm := mul_le_mul_of_nonneg_right hc (show 0≤(q:ℝ)*ell by positivity)
  apply (le_div_iff₀ (by positivity : 0<2*C*ell)).mpr
  nlinarith only [h16,hm]

/-- The three actual occupation errors each fit the same rare-event budget. -/
theorem three_rates (N : ℕ) (hN : 3≤N) (γ : ℝ) (hγ : 0<γ) (hγ1 : γ≤1)
    (horder : A*(k N γ:ℝ)^2*Real.log (N:ℝ) ≤ (N:ℝ)) :
    Real.exp (-(t N γ:ℝ)/(2*(10:ℝ)^35*Real.log (N:ℝ))) ≤ Real.exp (-12*beta*(q N γ:ℝ)) ∧
    Real.exp (-γ*(t N γ:ℝ)/(2*(10:ℝ)^21)) ≤ Real.exp (-12*beta*(q N γ:ℝ)) ∧
    Real.exp (-γ*(t N γ:ℝ)/(8*(10:ℝ)^14)) ≤ Real.exp (-12*beta*(q N γ:ℝ)) := by
  have hell := IntegrationParameters.log_order_gt_one N hN
  have hA := A_pos
  have hb := block_length_bounds N hN γ hγ hγ1
  have hweak : A*(k N γ:ℝ)^2 ≤ (N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hell.le (mul_nonneg hA.le (sq_nonneg (k N γ:ℝ)))
    nlinarith only [hh,horder]
  have ht := (time_bounds N γ (by omega) hweak).2.2.2.1
  have h16 : (q N γ:ℝ)*(k N γ:ℝ) ≤ 16*(t N γ:ℝ) := by
    change ((q N γ*k N γ:ℕ):ℝ)/16 ≤ _ at ht
    push_cast at ht
    linarith only [ht]
  have hq : (0:ℝ) ≤ (q N γ:ℝ) := Nat.cast_nonneg _
  have hf : (q N γ:ℝ)*Real.log (N:ℝ) ≤ 16*(t N γ:ℝ) :=
    (mul_le_mul_of_nonneg_left hb.2.1 hq).trans h16
  have hg16 := mul_le_mul_of_nonneg_left h16 hγ.le
  have hgk : (q N γ:ℝ) ≤ (q N γ:ℝ)*(γ*(k N γ:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hb.2.2.1 hq
    nlinarith [hell]
  have hg : (q N γ:ℝ)*1 ≤ 16*(γ*(t N γ:ℝ)) := by nlinarith only [hg16,hgk]
  have hfast := rate_bound (q N γ) (t N γ:ℝ) (Real.log (N:ℝ)) ((10:ℝ)^35)
    (by linarith) (by positivity) hf (by norm_num [beta])
  have hslow := rate_bound (q N γ) (γ*(t N γ:ℝ)) 1 ((10:ℝ)^21)
    (by norm_num) (by positivity) hg (by norm_num [beta])
  have hroot := rate_bound (q N γ) (γ*(t N γ:ℝ)) 1 (4*(10:ℝ)^14)
    (by norm_num) (by positivity) hg (by norm_num [beta])
  refine ⟨Real.exp_le_exp.mpr ?_,Real.exp_le_exp.mpr ?_,Real.exp_le_exp.mpr ?_⟩
  · simpa only [neg_div,neg_mul] using neg_le_neg hfast
  · simpa only [mul_one,neg_div,neg_mul] using neg_le_neg hslow
  · have he : γ*(t N γ:ℝ)/(2*(4*(10:ℝ)^14)*1) = γ*(t N γ:ℝ)/(8*(10:ℝ)^14) := by ring
    rw [he] at hroot
    simpa only [neg_div,neg_mul] using neg_le_neg hroot

/-- Strict intersection has its finite rarity cost derived from the actual floor q. -/
theorem strict_intersection (N : ℕ) (hN : 3≤N) (γ : ℝ) (hγ : 0<γ) (hγ1 : γ≤1)
    (horder : A*(k N γ:ℝ)^2*Real.log (N:ℝ) ≤ (N:ℝ)) :
    6*Real.exp (-12*beta*(q N γ:ℝ)) < Real.exp (-6*beta*(q N γ:ℝ)) := by
  have hell := IntegrationParameters.log_order_gt_one N hN
  have hA := A_pos
  have hb := block_length_bounds N hN γ hγ hγ1
  have hweak : A*(k N γ:ℝ)^2 ≤ (N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hell.le (mul_nonneg hA.le (sq_nonneg (k N γ:ℝ)))
    nlinarith only [hh,horder]
  have hq := (q_large N γ (by omega) hweak).2.1
  have hexp : (6:ℝ) < Real.exp (6*beta*(q N γ:ℝ)) := by
    have hh := Real.add_one_le_exp (6*beta*(q N γ:ℝ))
    linarith
  have hm := mul_lt_mul_of_pos_right hexp (Real.exp_pos (-12*beta*(q N γ:ℝ)))
  have he : Real.exp (6*beta*(q N γ:ℝ))*Real.exp (-12*beta*(q N γ:ℝ)) =
      Real.exp (-6*beta*(q N γ:ℝ)) := by rw [← Real.exp_add]; congr 1; ring
  rw [he] at hm
  exact hm
end Erdos642.CampaignFe72210bContinuation3.MomentRarityParameters
