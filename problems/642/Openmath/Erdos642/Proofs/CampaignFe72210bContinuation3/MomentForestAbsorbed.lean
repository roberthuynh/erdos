import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentForestOccupation
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentHostParameters
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentOccupationAbsorption

/-! Full actual first-stage forest occupation under the strong moment-host criteria. -/
namespace Erdos642.CampaignFe72210bContinuation3.MomentForestAbsorbed
open Erdos642.FiniteMarkov Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 800000 in
/-- The actual rounded forest bad-half mass, with no supplied smoothing/rank/net/probability input. -/
theorem graph_bad_half_absorbed (A B : Finset V)
    (hbi : G.IsBipartiteWith (A:Set V) (B:Set V)) (d : ℕ) (γ Λ : ℝ)
    (hN3 : 3 ≤ Fintype.card V) (hgap : HasBipartiteSpectralGap G γ) (hΛ : 1 ≤ Λ)
    (hmin : ∀ x, d ≤ G.degree x)
    (hmax : ∀ x, G.degree x ≤ 100*d)
    (hmoment : ∀ x, (graphTransition G^4) x x ≤ Λ/(d:ℝ)^2)
    (hdegree : MomentSAParameters.A*(spectralBlockLength (Fintype.card V) γ:ℝ)*
      Real.log (Fintype.card V:ℝ) ≤ (d:ℝ))
    (horder : MomentSAParameters.A*(spectralBlockLength (Fintype.card V) γ:ℝ)^2*
      Real.log (Fintype.card V:ℝ) ≤ (Fintype.card V:ℝ))
    (hmomentScale : MomentSAParameters.A*Λ*(spectralBlockLength (Fintype.card V) γ:ℝ)*
      Real.log (Fintype.card V:ℝ) ≤ (d:ℝ)^2*γ)
    (F : ForestBundle G A B (ForestParameters.q d)
      (ForestParameters.m (Fintype.card V) d) (ForestParameters.b d)) (x : V) :
    let t := MomentHostParameters.t (Fintype.card V) γ
    (graphChain G (fun z => by
      have hh := MomentHostParameters.strong_reductions (Fintype.card V) d hN3 γ Λ hgap.1 hgap.2.1 hΛ
        hdegree horder hmomentScale
      exact lt_of_lt_of_le (by omega : 0<d) (hmin z))).eventMass (t-1)
      (fun y p => (∃ f : Fin (ForestParameters.q d),
        (ForestParameters.m (Fintype.card V) d+1)/2 ≤
        (F.badInForest f ((t:ℝ)*(ForestParameters.b d:ℝ)/(600*(Fintype.card V:ℝ))) y p).card)) x ≤
    Real.exp (-(t:ℝ)/(2*(10:ℝ)^35*Real.log (Fintype.card V:ℝ))) +
      Real.exp (-γ*(t:ℝ)/(2*(10:ℝ)^21)) := by
  classical
  let N := Fintype.card V
  let k := MomentHostParameters.k N γ
  let t := MomentHostParameters.t N γ
  let μ := MomentHostParameters.mu N d
  let r := MomentSmoothingParameters.smoothingTime N (d:ℝ) Λ
  have hred := MomentHostParameters.strong_reductions N d hN3 γ Λ hgap.1 hgap.2.1 hΛ
    hdegree horder hmomentScale
  have hdlarge : 100000000 ≤ d := hred.1
  have hdp : 0 < d := by omega
  have hd : 0 < (d:ℝ) := by exact_mod_cast hdp
  let hdeg : ∀ z : V, 0 < G.degree z := fun z => hdp.trans_le (hmin z)
  have hminR : ∀ z, (d:ℝ) ≤ (G.degree z:ℝ) := by intro z; exact_mod_cast hmin z
  have hmaxR : ∀ z, (G.degree z:ℝ) ≤ 100*(d:ℝ) := by intro z; exact_mod_cast hmax z
  have hNd : 2*d ≤ N := MomentHostParameters.bipartite_order_lower G d hdp hbi.isBipartite hmin
  have hμbounds := MomentHostParameters.forest_mean_bounds N d hdlarge hNd
  have hblocks := MomentHostParameters.block_length_bounds N hN3 γ hgap.1 hgap.2.1
  have hgeom := MomentHostParameters.time_bounds N γ (by omega) hred.2.2.1
  have ht : 2 ≤ t := hgeom.2.1
  have htime : MomentSAParameters.a*(N:ℝ)/(32*(k:ℝ)) ≤ (t:ℝ) := hgeom.2.2.2.2.1
  have hell := IntegrationParameters.log_order_gt_one N hN3
  have hrbounds := MomentSmoothingParameters.smoothingTime_bounds N hN3 (d:ℝ) Λ hd hΛ hred.2.2.2.2
  have hr : 1 ≤ r := hrbounds.1
  have hrsmall : Real.sqrt (50*Λ*(N:ℝ))/(d:ℝ)*(1/4:ℝ)^(r-1) ≤ μ/1024 := by
    have hh := div_le_div_of_nonneg_right hμbounds.2.2.1 (by norm_num : (0:ℝ)≤1024)
    exact hrbounds.2.1.trans hh
  have hqF : 1 ≤ ForestParameters.q d := by have hh := ForestParameters.q_pos d hdlarge; omega
  have hm : 1 ≤ ForestParameters.m N d := (ForestParameters.m_bounds N d hdlarge hNd).1
  have hb : 1 ≤ ForestParameters.b d := by have hh := ForestParameters.ten_le_b d hdlarge; omega
  have hB : Nonempty (B:Set V) := by
    let f : Fin (ForestParameters.q d) := ⟨0,by omega⟩
    let j : Fin (ForestParameters.m N d) := ⟨0,by omega⟩
    have hh : (F.leaves (f,j)).Nonempty := Finset.card_pos.mp (by rw [F.leaves_card]; omega)
    obtain ⟨z,hz⟩ := hh
    exact ⟨⟨z,F.leaves_subset (f,j) hz⟩⟩
  have := hB
  obtain ⟨D,hD,hDN,hRank,hraw⟩ := MomentForestOccupation.graph_bad_half_raw G F hbi.symm hdeg γ (d:ℝ) Λ
    hgap hd hΛ hminR hmaxR hmoment hqF hm hb r hr hrsmall t ht
  have hn : (t:ℝ)/3 ≤ (t/2:ℕ) := by
    have hh : t ≤ 3*(t/2) := by omega
    have hc : (t:ℝ) ≤ 3*((t/2:ℕ):ℝ) := by exact_mod_cast hh
    linarith
  have hmu0 : MomentOccupationAbsorption.mu0 ≤ μ := by
    simpa only [MomentOccupationAbsorption.mu0, MomentSmoothingParameters.mu0] using hμbounds.2.2.1
  have hqFN : ForestParameters.q d ≤ N := by
    exact_mod_cast ForestOccupationParameters.q_le_order N d hdlarge hNd
  have hfast := MomentOccupationAbsorption.fast_family_absorbed N k t (t/2) r
    (ForestParameters.q d) (ForestParameters.m N d) (d:ℝ) μ hN3 hell hblocks.2.1
    hdegree horder htime hn hr hrbounds.2.2 hmu0 hμbounds.2.1 hqFN hμbounds.2.2.2
  have hslow := MomentOccupationAbsorption.slow_family_absorbed N k t (t/2) D
    (d:ℝ) γ Λ μ hN3 hell hblocks.2.1 hdegree hgap.1 hmomentScale htime hn
    hmu0 hμbounds.2.1 hD hRank
  have hlevel : 2/(μ/1024) = 2048/μ := by ring
  have hs : (CoordinateGrid.alphabet N μ^D:ℕ)*(⌈2/(μ/1024)⌉₊:ℝ)*(100*(N:ℝ))*
      Real.exp (-γ*μ*(t/2:ℕ)/65536) ≤ Real.exp (-γ*(t:ℝ)/(2*(10:ℝ)^21)) := by
    rw [hlevel]
    simpa only [Nat.cast_pow,mul_assoc] using hslow
  have hrx := hraw x
  change (graphChain G hdeg).eventMass (t-1)
      (fun y p => ∃ f : Fin (ForestParameters.q d), (ForestParameters.m N d+1)/2 ≤
        (F.badInForest f ((t:ℝ)*(ForestParameters.b d:ℝ)/(600*(N:ℝ))) y p).card) x ≤ _ at hrx
  exact hrx.trans (add_le_add hfast hs)

end Erdos642.CampaignFe72210bContinuation3.MomentForestAbsorbed
