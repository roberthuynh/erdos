import Openmath.Erdos642.Proofs.Adaptive20261018.Forest
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentPairParameters
import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphForestOccupation
import Openmath.Erdos642.Proofs.CampaignFe72210b.TwoWindowTransfer

/-! Actual chronological two-window moment-host occupation, without old full-family premises. -/
namespace Erdos642.Adaptive20261018.Windows
open Erdos642.FiniteMarkov Erdos642.OccupationTail Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3
open MomentSAParameters
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Chronological second-stage transfer from the supplied first-family bound; the later fixed-root bound is derived from the actual graph. -/
theorem graph_two_window_absorbed (A B : Finset V)
    (hbi : G.IsBipartiteWith (A:Set V) (B:Set V)) (d : ℕ) (γ Λ : ℝ)
    (hdeg : ∀ z : V, 0 < G.degree z)
    (hN3 : 3 ≤ Fintype.card V) (hgap : HasBipartiteSpectralGap G γ) (hΛ : 1 ≤ Λ)
    (hmin : ∀ z, d ≤ G.degree z) (hmax : ∀ z, G.degree z ≤ 100*d)
    (hmoment : ∀ z, (graphTransition G^4) z z ≤ Λ/(d:ℝ)^2)
    (hdlarge : 100000000 ≤ d)
    (horder : MomentSAParameters.A*(spectralBlockLength (Fintype.card V) γ:ℝ)^2*Real.log (Fintype.card V:ℝ) ≤ (Fintype.card V:ℝ))
    (r : ℕ)
    (F : ForestBundle G A B (ForestParameters.q d)
      (ForestParameters.m (Fintype.card V) d) (ForestParameters.b d)) (g : ℕ) (x : V)
    (hfirstRaw : ∀ y : V,
      (graphChain G hdeg).eventMass (MomentHostParameters.t (Fintype.card V) γ-1)
        (fun z p => ∃ f : Fin (ForestParameters.q d),
          (ForestParameters.m (Fintype.card V) d+1)/2 ≤
          (F.badInForest f ((MomentHostParameters.t (Fintype.card V) γ:ℝ)*
            (ForestParameters.b d:ℝ)/(600*(Fintype.card V:ℝ))) z p).card) y ≤
      Real.exp (-(MomentHostParameters.t (Fintype.card V) γ:ℝ)/(2*(10:ℝ)^35*(r:ℝ))) +
      Real.exp (-γ*(MomentHostParameters.t (Fintype.card V) γ:ℝ)/(2*(10:ℝ)^21))) :
    let t := MomentHostParameters.t (Fintype.card V) γ
    (graphChain G hdeg).eventMass (((t-1)+g)+(t-1))
      (fun y w => F.windowWeightedCount (graphChain G hdeg) (t-1) g (t-1) y w <
        (d:ℝ)*(t:ℝ)^2/((10:ℝ)^24*(Fintype.card V:ℝ))) x ≤
      (Real.exp (-(t:ℝ)/(2*(10:ℝ)^35*(r:ℝ))) +
        Real.exp (-γ*(t:ℝ)/(2*(10:ℝ)^21))) + Real.exp (-γ*(t:ℝ)/(8*(10:ℝ)^14)) := by
  classical
  let N := Fintype.card V
  let t := MomentHostParameters.t N γ
  let C := graphChain G hdeg
  let leafcut := (t:ℝ)*(ForestParameters.b d:ℝ)/(600*(N:ℝ))
  let u := ForestOccupationParameters.u N d
  let eps := Real.exp (-(t:ℝ)/(2*(10:ℝ)^35*(r:ℝ))) +
    Real.exp (-γ*(t:ℝ)/(2*(10:ℝ)^21))
  let delta := Real.exp (-γ*(t:ℝ)/(8*(10:ℝ)^14))
  have hγ := hgap.1
  have horderWeak : MomentSAParameters.A*(MomentHostParameters.k N γ:ℝ)^2 ≤ (N:ℝ) := by
    have hl := IntegrationParameters.log_order_gt_one N hN3
    have hh := mul_le_mul_of_nonneg_left hl.le
      (mul_nonneg MomentSAParameters.A_pos.le (sq_nonneg (MomentHostParameters.k N γ:ℝ)))
    have horder' : MomentSAParameters.A*(MomentHostParameters.k N γ:ℝ)^2*Real.log (N:ℝ) ≤ (N:ℝ) := horder
    nlinarith only [hh,horder']
  have hd : 0 < (d:ℝ) := by exact_mod_cast (show 0<d by omega)
  have hNd := MomentHostParameters.bipartite_order_lower G d (by omega) hbi.isBipartite hmin
  have hblocks := MomentHostParameters.block_length_bounds N hN3 γ hgap.1 hgap.2.1
  have ht : 2 ≤ t := (MomentHostParameters.time_bounds N γ (by omega) horderWeak).2.1
  have hN : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hminR : ∀ z, (d:ℝ) ≤ (G.degree z:ℝ) := by intro z; exact_mod_cast hmin z
  have hmaxR : ∀ z, (G.degree z:ℝ) ≤ 100*(d:ℝ) := by intro z; exact_mod_cast hmax z
  have hfirst : C.eventMass (t-1) (fun _ p => ¬F.firstStageSuccess leafcut x p) x ≤ eps := by
    have hh := hfirstRaw x
    have he : C.eventMass (t-1) (fun _ p => ¬F.firstStageSuccess leafcut x p) x =
      C.eventMass (t-1) (fun y p => ∃ f : Fin (ForestParameters.q d),
        (ForestParameters.m N d+1)/2 ≤ (F.badInForest f leafcut y p).card) x := by
      unfold Chain.eventMass
      apply Finset.sum_congr rfl
      intro p _
      simp only [ForestBundle.firstStageSuccess,not_not]
      split_ifs <;> rfl
    rw [he]
    exact hh
  have hu : (N:ℝ)/(4*(10:ℝ)^10) ≤ (u:ℝ) := by
    simpa only [u, show (4:ℝ)*(10:ℝ)^10=40000000000 by norm_num] using
      (ForestOccupationParameters.support_bounds N d hdlarge hNd).1
  have hfixed : ∀ U : Finset V, U ⊆ A → u ≤ U.card → ∀ y : V,
      C.eventMass (t-1) (fun z p => occupation U z p < (t:ℝ)*(U.card:ℝ)/(300*(N:ℝ))) y ≤ delta := by
    intro U hU hcard y
    have hh := graph_occupation_tail_finset G B A hbi.symm hdeg (d:ℝ) hd hminR hmaxR γ hgap U hU t ht y
    apply hh.trans
    have hc : (u:ℝ) ≤ (U.card:ℝ) := by exact_mod_cast hcard
    have hUlarge := hu.trans hc
    have hs := (div_le_iff₀ (by positivity : (0:ℝ)<4*(10:ℝ)^10)).mp hUlarge
    have hmult := mul_le_mul_of_nonneg_left hs (show 0≤γ*(t:ℝ) by positivity)
    have hrate : γ*(t:ℝ)/(4*(10:ℝ)^14) ≤ γ*(t:ℝ)*(U.card:ℝ)/(10000*(N:ℝ)) := by
      apply (le_div_iff₀ (by positivity : (0:ℝ)<10000*(N:ℝ))).mpr
      nlinarith [hmult]
    have hexp := Real.exp_le_exp.mpr (neg_le_neg hrate)
    have hraw : 200*(N:ℝ)*Real.exp (-γ*(t:ℝ)*(U.card:ℝ)/(10000*(N:ℝ))) ≤
      200*(N:ℝ)*Real.exp (-γ*(t:ℝ)/(4*(10:ℝ)^14)) := by
      simpa only [neg_div,neg_mul] using mul_le_mul_of_nonneg_left hexp (show 0≤200*(N:ℝ) by positivity)
    exact hraw.trans (MomentPairParameters.fixed_root_prefactor_absorbed N hN3 γ hgap.1 hgap.2.1 horder)
  have hcore := F.low_windowWeightedCount_eventMass_le C (t-1) g t leafcut (N:ℝ) delta eps
    (by dsimp [leafcut]; positivity) hN u (F.firstStageSuccess leafcut x) x (Real.exp_nonneg _)
    (fun p hp => F.firstStageSuccess_goodRootSet_card leafcut x p hp) hfirst hfixed
  have hprod : (d:ℝ)*(t:ℝ)^2/((10:ℝ)^24*(N:ℝ)) ≤ leafcut*((t:ℝ)*(u:ℝ)/(300*(N:ℝ))) := by
    simpa only [leafcut,u,show (10:ℝ)^24=1000000000000000000000000 by norm_num] using
      ForestOccupationParameters.threshold_product N d t hdlarge hNd
  change C.eventMass (((t-1)+g)+(t-1))
    (fun y w => F.windowWeightedCount C (t-1) g (t-1) y w <
      (d:ℝ)*(t:ℝ)^2/((10:ℝ)^24*(N:ℝ))) x ≤ eps+delta
  rw [C.eventMass_freeze_start]
  have hm := C.eventMass_mono
    (fun _ w => F.windowWeightedCount C (t-1) g (t-1) x w <
      (d:ℝ)*(t:ℝ)^2/((10:ℝ)^24*(N:ℝ)))
    (fun _ w => F.windowWeightedCount C (t-1) g (t-1) x w < leafcut*((t:ℝ)*(u:ℝ)/(300*(N:ℝ))))
    (fun _ _ hw => hw.trans_le hprod) x
  exact hm.trans hcore

end Erdos642.Adaptive20261018.Windows
