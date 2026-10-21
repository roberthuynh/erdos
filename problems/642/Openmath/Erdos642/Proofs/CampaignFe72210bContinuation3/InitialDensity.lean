import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.SpectralExtraction
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.OldGlobalApplicability
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.AllOrdersDensity
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.AvoidanceHeredity
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.LocalAvoidanceMoment
import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralCycleProof

                                                                                    

                                                                               
                                                                             
  
namespace Erdos642.CampaignFe72210bContinuation3.InitialDensity
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.CutExtraction
open Erdos642.CampaignFe72210bContinuation3.AllOrdersDensity
universe u

attribute [-instance] FinsetCoe.fintype in
/-- Genuine extraction and the old spectral theorem give an unconditional
eventual sixth-power average bound over every actual finite graph. -/
theorem exists_eventual_avoiding_average_six :
    ∃ K : ℝ, 0 < K ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
      EventualAvoidingAverage.{u} 6 K n0 := by
  obtain ⟨K0, hK0, n0, hn0, hpay⟩ :=
    OldGlobalApplicability.exists_uniform_old_applicability
      ExtractParameters.c ExtractParameters.b
      (by norm_num [ExtractParameters.c])
      (by norm_num [ExtractParameters.b])
      (by norm_num [ExtractParameters.b])
  let K : ℝ := max K0 ExtractParameters.baseConstant
  have hK0K : K0 ≤ K := le_max_left _ _
  have hbaseK : ExtractParameters.baseConstant ≤ K := le_max_right _ _
  have hK : 0 < K := hK0.trans_le hK0K
  refine ⟨K, hK, n0, hn0, ?_⟩
  intro V _ _ G _ hn havoid
  let n := Fintype.card V
  let L : ℝ := Real.log (n : ℝ)
  let D : ℝ := graphAverage G
  change D ≤ K * L ^ 6
  by_contra hsmall
  have hdense : K * L ^ 6 ≤ D := (lt_of_not_ge hsmall).le
  have hn3 : 3 ≤ n := hn0.trans hn
  have hL : 1 < L := IntegrationParameters.log_order_gt_one n hn3
  have hLpos : 0 < L := by linarith
  have hbasepos : 0 < ExtractParameters.baseConstant := by norm_num [ExtractParameters.baseConstant]
  have hbase : ExtractParameters.baseConstant * L ^ 2 ≤ D := by
    calc
      _ ≤ ExtractParameters.baseConstant * L ^ 6 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL.le (by norm_num)) hbasepos.le
      _ ≤ K * L ^ 6 := mul_le_mul_of_nonneg_right hbaseK (by positivity)
      _ ≤ D := hdense
  obtain ⟨S, hSne, J, instJ, W, hWne, f, hf, hN3, hNn,
      hHpos, hHmin, hHratio, hHbip, hHconn, hHgap⟩ :=
    SpectralExtraction.exists_spectral_host G hn3 hbase
  let : DecidableRel J.Adj := instJ
  let H := J.induce (W : Set (S : Set V))
  let N := Fintype.card (W : Set (S : Set V))
  let d : ℝ := H.minDegree
  let gamma := ExtractParameters.suppliedGap n
  have : Nonempty (W : Set (S : Set V)) := hWne.to_subtype
  have hNd : d + 1 ≤ (N : ℝ) := by
    change (H.minDegree : ℝ) + 1 ≤ (N : ℝ)
    let x : (W : Set (S : Set V)) := Classical.choice inferInstance
    have hmin := H.minDegree_le_degree x
    have hcard := H.degree_lt_card_verts x
    exact_mod_cast (show H.minDegree + 1 ≤ N by omega)
  have hdegree : ExtractParameters.c * K0 * L ^ 5 ≤ d := by
    calc
      _ = (K0 * L ^ 6) / (400 * L) := by
        dsimp [ExtractParameters.c]
        field_simp [hLpos.ne']
      _ ≤ (K * L ^ 6) / (400 * L) := by gcongr
      _ ≤ D / (400 * L) := by gcongr
      _ ≤ d := hHmin
  have hscalar := hpay n N d hn hN3 hNn hdegree hNd
  have hhost : SpectralHostPremises H gamma := by
    refine ⟨hN3, hHconn, hHbip, hHratio, hHgap, ?_, ?_⟩
    · exact hscalar.2.2.1
    · exact hscalar.2.2.2
  have hrich : HasRichCycle H := spectral_host_has_rich_cycle H gamma hhost
  exact havoid (hasRichCycle_of_injective_hom f hf hrich)

/-- Genuine unconditional all-graph P8, obtained without the new moment route. -/
theorem exists_initial_density :
    ∃ C : ℝ, 0 < C ∧ LocalAvoidanceMoment.AllAvoidingP8.{u} C := by
  obtain ⟨K, hK, n0, hn0, hevent6⟩ := exists_eventual_avoiding_average_six.{u}
  have hevent8 : EventualAvoidingAverage.{u} 8 K n0 := by
    intro V _ _ G _ hn havoid
    have hn3 : 3 ≤ Fintype.card V := hn0.trans hn
    have hlog := IntegrationParameters.log_order_gt_one (Fintype.card V) hn3
    exact (hevent6 V G hn havoid).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog.le (by norm_num : (6 : ℕ) ≤ 8)) hK.le)
  obtain ⟨C, hC, hbound⟩ := exists_all_orders_density 8 K n0 hK hn0 hevent8
  exact ⟨C, hC, hbound⟩

end Erdos642.CampaignFe72210bContinuation3.InitialDensity
