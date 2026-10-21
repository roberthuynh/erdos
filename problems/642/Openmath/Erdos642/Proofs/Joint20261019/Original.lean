import Openmath.Erdos642.Proofs.Joint20261019.OriginalPayment
import Openmath.Erdos642.Proofs.Joint20261019.RichCycle
import Openmath.Erdos642.Proofs.Joint20261019.AllOrders
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.OriginalBound

namespace Erdos642.Joint20261019.Original
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3
open CutExtraction LocalAvoidanceMoment
universe u
set_option maxHeartbeats 4000000

attribute [-instance] FinsetCoe.fintype in
theorem exists_eventual_avoiding_edges :
    ∃ K : ℝ, 0<K ∧ ∃ n0 : ℕ,
      ∀ (W : Type u) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj], n0≤Fintype.card W →
        ¬HasRichCycle H → (H.edgeFinset.card:ℝ) ≤ K*AllOrders.psi (Fintype.card W) := by
  classical
  obtain ⟨C0,hC0,hP8⟩ := InitialDensity.exists_initial_density.{u}
  let C1 := LocalAvoidanceMomentNormalized.momentConstant C0
  have hC1 : 0<C1 :=
    (by positivity : (0:ℝ)<1/(Real.log (2:ℝ))^8).trans_le
      (LocalAvoidanceMomentNormalized.momentConstant_lower C0 hC0.le)
  obtain ⟨K0,hK0,n0,hn0,happly⟩ := OriginalPayment.exists_uniform_host_applicability
    ExtractParameters.c ExtractParameters.b C0 C1
    (by norm_num [ExtractParameters.c]) (by norm_num [ExtractParameters.b])
    (by norm_num [ExtractParameters.b]) hC0 hC1
  let K := max K0 ExtractParameters.baseConstant
  let n1 := max n0 (⌈Real.exp (Real.exp 1)⌉₊ + ⌈Real.exp 2⌉₊ + 3)
  have hK : 0<K := hK0.trans_le (le_max_left _ _)
  refine ⟨K,hK,n1,?_⟩
  intro W _ _ H _ hn ha
  let n := Fintype.card W
  have hnold : n0 ≤ n := (le_max_left _ _).trans hn
  have hnextra : ⌈Real.exp (Real.exp 1)⌉₊ + ⌈Real.exp 2⌉₊ + 3 ≤ n :=
    (le_max_right _ _).trans hn
  have hn3 : 3≤n := hn0.trans hnold
  have hnreal : (2:ℝ) ≤ n := by exact_mod_cast (show 2≤n by omega)
  have hnpos : (0:ℝ)<n := by linarith
  have hexp : Real.exp (Real.exp 1) ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp (Real.exp 1)⌉₊≤n by omega))
  have hexp2 : Real.exp 2 ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp 2⌉₊≤n by omega))
  have hL : (2:ℝ)≤Real.log (n:ℝ) := (Real.le_log_iff_exp_le hnpos).mpr hexp2
  have hLpos : 0<Real.log (n:ℝ) := by linarith
  have hLLpos : 0<Real.log (Real.log (n:ℝ)) := Real.log_pos (by linarith)
  have havg : graphAverage H ≤ K*Real.log (n:ℝ)^4 := by
    by_contra hnot
    have hD : K*Real.log (n:ℝ)^4 ≤ graphAverage H :=
      le_of_lt (lt_of_not_ge hnot)
    have hpower : Real.log (n:ℝ)^2 ≤ Real.log (n:ℝ)^4 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    have hbase : ExtractParameters.baseConstant*Real.log (n:ℝ)^2 ≤ graphAverage H := by
      calc
        _ ≤ K*Real.log (n:ℝ)^2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
        _ ≤ K*(Real.log (n:ℝ)^4) := mul_le_mul_of_nonneg_left hpower hK.le
        _ = K*Real.log (n:ℝ)^4 := by ring
        _ ≤ _ := hD
    obtain ⟨S,hS,J,instJ,U,hU,f,hf,hN3,hNn,hpos,hmin,hratio,hbip,hconn,hgap⟩ :=
      SpectralExtraction.exists_spectral_host H hn3 hbase
    letI : DecidableRel J.Adj := instJ
    let F := J.induce (U:Set (S:Set W))
    let N := Fintype.card (U:Set (S:Set W))
    letI : Nonempty (U:Set (S:Set W)) := Fintype.card_pos_iff.mp (show 0<N by omega)
    let d : ℕ := F.minDegree
    let Lambda : ℝ := C1*Real.log (2*(d:ℝ))^8
    have havoid : ¬HasRichCycle F := not_hasRichCycle_of_injective_hom f hf ha
    have hd2 : (2:ℝ) ≤ d := (ExtractParameters.degree_scale_ge_two n hn3 (graphAverage H) hbase).trans hmin
    have hd1 : 1 ≤ F.minDegree := by exact_mod_cast (show (1:ℝ)≤d by linarith)
    have hLambda : 1≤Lambda := OriginalBound.normalized_parameter_ge_one C0 hC0.le d (by linarith)
    have hdensity : (d:ℝ) ≤ 2*C0*Real.log (2*(N:ℝ))^8 :=
      OriginalBound.avoiding_min_degree_le F C0 hP8 havoid (by omega)
    have hscaleD : K0*Real.log (n:ℝ)^4 ≤ graphAverage H := by
      exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hD
    have hscaled : ExtractParameters.c*graphAverage H/Real.log (n:ℝ) ≤ (d:ℝ) := by
      convert hmin using 1 <;> unfold ExtractParameters.c <;> ring
    have hp := happly n N (graphAverage H) d Lambda hnold hN3 hNn F.minDegree_lt_card
      hscaleD hscaled hdensity hLambda le_rfl
    have hhost : RichCycle.JointHostPremises F (ExtractParameters.suppliedGap n) Lambda := by
      refine ⟨hN3,hconn,hbip,hratio,hgap,hLambda,?_,?_⟩
      · intro x
        exact LocalAvoidanceMomentNormalized.graph_fourth_return_normalized F C0 hC0.le hP8 havoid hbip hd1 hratio x
      · simpa only [ExtractParameters.suppliedGap] using hp
    exact ha (hasRichCycle_of_injective_hom f hf (RichCycle.joint_host_has_rich_cycle F _ _ hhost))
  have hidentity : graphAverage H*(n:ℝ)=2*(H.edgeFinset.card:ℝ) := by
    unfold graphAverage
    rw [degreeVolume_eq_twice_edges]
    exact div_mul_cancel₀ _ hnpos.ne'
  calc
    (H.edgeFinset.card:ℝ) = graphAverage H*(n:ℝ)/2 := by linarith
    _ ≤ (K*Real.log (n:ℝ)^4)*(n:ℝ)/2 := by gcongr
    _ = K*((n:ℝ)*Real.log (n:ℝ)^4/2) := by ring
    _ ≤ K*AllOrders.psi n := mul_le_mul_of_nonneg_left
      (AllOrders.psi_comparison n (by omega)) hK.le

theorem original_joint_rich_cycle :
    ∃ C : ℝ, 0<C ∧ ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      C*AllOrders.psi (Fintype.card W) < (H.edgeFinset.card:ℝ) → HasRichCycle H := by
  obtain ⟨K,hK,n0,hevent⟩ := exists_eventual_avoiding_edges.{u}
  obtain ⟨C,hC,hbound⟩ := Erdos642.Adaptive20261018.AllOrders.all_orders_of_eventual AllOrders.psi AllOrders.psi_zero
    AllOrders.psi_pos K hK n0 hevent
  refine ⟨C,hC,?_⟩
  intro W _ _ H _ hdense
  by_contra ha
  exact (not_lt_of_ge (hbound W H ha)) hdense

end Erdos642.Joint20261019.Original
