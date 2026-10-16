import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.InitialDensity
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.LocalAvoidanceMomentNormalized
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.StrongGlobalApplicability
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentCycleProof

/-! Original-instance log-five density, with all spectral and local inputs derived. -/
namespace Erdos642.CampaignFe72210bContinuation3.OriginalBound
open Erdos642.CampaignFe72210b CutExtraction LocalAvoidanceMoment
set_option maxHeartbeats 4000000
universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem avoiding_min_degree_le (C : ℝ) (hP8 : AllAvoidingP8.{u} C)
    (ha : ¬ HasRichCycle G) (hN : 0 < Fintype.card V) :
    (G.minDegree : ℝ) ≤ 2*C*Real.log (2*(Fintype.card V:ℝ))^8 := by
  letI : Nonempty V := Fintype.card_pos_iff.mp hN
  have he := hP8 V G ha
  have havg := GraphExpansionConductance.average_degree_ge_min G
  change (G.minDegree : ℝ) ≤ graphAverage G at havg
  have hc : (0:ℝ) < Fintype.card V := by exact_mod_cast hN
  apply havg.trans
  unfold graphAverage
  rw [degreeVolume_eq_twice_edges]
  apply (div_le_iff₀ hc).mpr
  nlinarith only [he]

theorem normalized_parameter_ge_one (C : ℝ) (hC : 0 ≤ C) (d : ℝ) (hd : 1 ≤ d) :
    1 ≤ LocalAvoidanceMomentNormalized.momentConstant C*Real.log (2*d)^8 := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log (2:ℝ) ≤ Real.log (2*d) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hp := pow_le_pow_left₀ hlog2.le hlog 8
  have hC1 := LocalAvoidanceMomentNormalized.momentConstant_lower C hC
  have hC1pos : 0 < LocalAvoidanceMomentNormalized.momentConstant C :=
    (by positivity : (0:ℝ) < 1/(Real.log (2:ℝ))^8).trans_le hC1
  calc
    1 = (1/(Real.log (2:ℝ))^8)*(Real.log (2:ℝ))^8 := by field_simp
    _ ≤ LocalAvoidanceMomentNormalized.momentConstant C*Real.log (2*d)^8 :=
      mul_le_mul hC1 hp (by positivity) hC1pos.le

attribute [-instance] FinsetCoe.fintype in
/-- Constants are chosen before any original graph or its actual extracted host. -/
theorem exists_eventual_avoiding_average :
    ∃ K : ℝ, 0<K ∧ ∃ n0 : ℕ, 3≤n0 ∧
      ∀ (W : Type u) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj], n0≤Fintype.card W →
        ¬HasRichCycle H → graphAverage H ≤ K*Real.log (Fintype.card W:ℝ)^5 := by
  classical
  obtain ⟨C0,hC0,hP8⟩ := InitialDensity.exists_initial_density.{u}
  have hlog2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  let C1 := LocalAvoidanceMomentNormalized.momentConstant C0
  have hC1 : 0<C1 :=
    (by positivity : (0:ℝ)<1/(Real.log (2:ℝ))^8).trans_le
      (LocalAvoidanceMomentNormalized.momentConstant_lower C0 hC0.le)
  obtain ⟨K0,hK0,n0,hn0,happly⟩ := StrongGlobalApplicability.exists_uniform_strong_applicability
    ExtractParameters.c ExtractParameters.b C0 C1
    (by norm_num [ExtractParameters.c]) (by norm_num [ExtractParameters.b])
    (by norm_num [ExtractParameters.b]) hC0 hC1
  let K := max K0 ExtractParameters.baseConstant
  have hK : 0<K := hK0.trans_le (le_max_left _ _)
  refine ⟨K,hK,n0,hn0,?_⟩
  intro W _ _ H _ hn ha
  by_contra hnot
  have hD : K*Real.log (Fintype.card W:ℝ)^5 ≤ graphAverage H := le_of_lt (lt_of_not_ge hnot)
  let n := Fintype.card W
  let D := graphAverage H
  have hn3 : 3≤n := hn0.trans hn
  have hell := IntegrationParameters.log_order_gt_one n hn3
  have hellpos : 0<Real.log (n:ℝ) := by linarith
  have hpower : Real.log (n:ℝ)^2 ≤ Real.log (n:ℝ)^5 :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hbase : ExtractParameters.baseConstant*Real.log (n:ℝ)^2 ≤ D := by
    calc
      _ ≤ K*Real.log (n:ℝ)^2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
      _ ≤ K*Real.log (n:ℝ)^5 := mul_le_mul_of_nonneg_left hpower hK.le
      _ ≤ D := hD
  obtain ⟨S,hS,J,instJ,U,hU,f,hf,hN3,hNn,hpos,hmin,hratio,hbip,hconn,hgap⟩ :=
    SpectralExtraction.exists_spectral_host H hn3 hbase
  letI : DecidableRel J.Adj := instJ
  let F := J.induce (U:Set (S:Set W))
  let N := Fintype.card (U:Set (S:Set W))
  let d : ℝ := F.minDegree
  let Lambda : ℝ := C1*Real.log (2*d)^8
  have havoid : ¬HasRichCycle F := not_hasRichCycle_of_injective_hom f hf ha
  have hd2 : (2:ℝ) ≤ d := (ExtractParameters.degree_scale_ge_two n hn3 D hbase).trans hmin
  have hdreal1 : (1:ℝ) ≤ (F.minDegree:ℝ) := by change (1:ℝ)≤d; linarith
  have hd1 : 1 ≤ F.minDegree := by exact_mod_cast hdreal1
  have hLambda : 1≤Lambda := normalized_parameter_ge_one C0 hC0.le d (by linarith)
  have hdensity : d ≤ 2*C0*Real.log (2*(N:ℝ))^8 :=
    avoiding_min_degree_le F C0 hP8 havoid (by omega)
  have hscaleD : K0*Real.log (n:ℝ)^5 ≤ D :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hD
  have hscaled : ExtractParameters.c*D/Real.log (n:ℝ) ≤ d := by
    convert hmin using 1 <;> unfold ExtractParameters.c <;> ring
  have hp := happly n N D d Lambda hn hN3 hNn hscaleD hscaled hdensity hLambda le_rfl
  have hhost : MomentRichPath.StrongMomentHostPremises F (ExtractParameters.suppliedGap n) Lambda := by
    refine ⟨hN3,hconn,hbip,hratio,hgap,hLambda,?_,?_,?_,?_⟩
    · intro x
      exact LocalAvoidanceMomentNormalized.graph_fourth_return_normalized F C0 hC0.le hP8 havoid hbip hd1 hratio x
    · simpa only [MomentSAParameters.A, spectralBlockLength, ExtractParameters.suppliedGap] using hp.2.2.2.2.1
    · simpa only [MomentSAParameters.A, spectralBlockLength, ExtractParameters.suppliedGap] using hp.2.2.2.2.2.2
    · simpa only [MomentSAParameters.A, spectralBlockLength, ExtractParameters.suppliedGap] using hp.2.2.2.2.2.1
  exact ha (hasRichCycle_of_injective_hom f hf (MomentCycleProof.moment_host_has_rich_cycle F _ _ hhost))

/-- All orders and all original finite simple graphs; no host or moment premise. -/
theorem exists_original_avoiding_bound :
    ∃ C : ℝ, 0<C ∧ AllOrdersDensity.AllAvoidingEdgeDensity.{u} 5 C := by
  obtain ⟨K,hK,n0,hn0,hevent⟩ := exists_eventual_avoiding_average.{u}
  exact AllOrdersDensity.exists_all_orders_density 5 K n0 hK hn0 hevent

/-- Original edge-density trigger for an actual cycle with at least its length in chords. -/
theorem original_log_five_rich_cycle :
    ∃ C : ℝ, 0<C ∧
      ∀ (W : Type u) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj],
        C*(Fintype.card W:ℝ)*Real.log (2*(Fintype.card W:ℝ))^5 < (H.edgeFinset.card:ℝ) →
        HasRichCycle H := by
  obtain ⟨C,hC,hbound⟩ := exists_original_avoiding_bound.{u}
  refine ⟨C,hC,?_⟩
  intro W _ _ H _ hdense
  by_contra ha
  exact (not_lt_of_ge (hbound W H ha)) hdense

end Erdos642.CampaignFe72210bContinuation3.OriginalBound
