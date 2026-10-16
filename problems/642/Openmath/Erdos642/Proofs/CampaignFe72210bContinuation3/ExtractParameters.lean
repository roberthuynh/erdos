import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.CutExtractSubtype
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.RegularizationParameters
import Openmath.Erdos642.Proofs.CampaignFe72210b.IntegrationParameters

namespace Erdos642.CampaignFe72210bContinuation3.ExtractParameters
open Erdos642.CampaignFe72210b CutExtraction
noncomputable def c : ℝ := 1/400
noncomputable def b : ℝ := 1/(10:ℝ)^8
noncomputable def baseConstant : ℝ := (10:ℝ)^6
noncomputable def suppliedGap (n : ℕ) : ℝ := b/(Real.log (n:ℝ))^2

theorem gap_comparison (n : ℕ) (hn : 3≤n) :
    0 < suppliedGap n ∧ suppliedGap n ≤ (((lossParameter n/3)/100)^2)/8 := by
  have hell := IntegrationParameters.log_order_gt_one n hn
  have hl : 0 < Real.log (n:ℝ) := by linarith
  have he : (((lossParameter n/3)/100)^2)/8 =
      ((Real.log 2)^2/2880000)/(Real.log (n:ℝ))^2 := by
    unfold lossParameter
    field_simp [ne_of_gt hl]
    <;> ring
  have hc : b ≤ (Real.log 2)^2/2880000 := by
    unfold b
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2880000)).mpr
    nlinarith [RegularizationParameters.log_two_gt_half]
  constructor
  · unfold suppliedGap b
    positivity
  · rw [he]
    exact div_le_div_of_nonneg_right hc (sq_nonneg _)

theorem degree_scale_ge_two (n : ℕ) (hn : 3≤n) (D : ℝ)
    (hD : baseConstant*(Real.log (n:ℝ))^2 ≤ D) :
    2 ≤ D/(400*Real.log (n:ℝ)) := by
  have hell := IntegrationParameters.log_order_gt_one n hn
  have hl : 0 < Real.log (n:ℝ) := by linarith
  apply (le_div_iff₀ (by positivity : (0:ℝ)<400*Real.log (n:ℝ))).mpr
  norm_num only [baseConstant] at hD
  nlinarith [sq_nonneg (Real.log (n:ℝ)-1)]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem actual_gap_weaken (γ γ' : ℝ) (hgap : HasBipartiteSpectralGap G γ)
    (hγ' : 0<γ') (hle : γ'≤γ) : HasBipartiteSpectralGap G γ' := by
  rcases hgap with ⟨hγ,hγ1,hplus,hminus,hsp,hsm,hrest⟩
  refine ⟨hγ',hle.trans hγ1,hplus,hminus,hsp,hsm,?_⟩
  intro lam hlam hne1 hnem
  exact (hrest lam hlam hne1 hnem).trans (by linarith)

end Erdos642.CampaignFe72210bContinuation3.ExtractParameters
