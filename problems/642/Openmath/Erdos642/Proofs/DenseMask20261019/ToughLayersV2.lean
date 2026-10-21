import Openmath.Erdos642.Proofs.DenseMask20261019.Toughness
import Openmath.Erdos642.Proofs.DenseMask20261019.UniformLayers
import Openmath.Erdos642.Proofs.DenseMask20261019.Sampler
import Mathlib.Analysis.Complex.ExponentialBounds

/-! One actual label outcome gives disjoint ordinary-tough layers and every fixed query. -/
noncomputable section
namespace Erdos642.DenseMask20261019.ToughLayersV2
open Finset SimpleGraph MeasureTheory ProbabilityTheory Real
open OAI.ErdosGallai.Sampling
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3
open Erdos642.CampaignFe72210bContinuation3.CutExtraction
open Erdos642.DenseMask20261019
open ComponentObstruction DeletionComponents AvoidanceOrder InitialMass InitialConcentration
attribute [local instance] Classical.propDecidable
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

attribute [-instance] FinsetCoe.fintype in
private theorem induced_boundary (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (U : Finset (Set.Elem (A : Set V))) :
    FixedObstruction.lift A
        ((closedNeighborhood (G.induce (A : Set V)) U \ U : Finset (Set.Elem (A : Set V)))) =
      sampleBoundary G A (FixedObstruction.lift A U) := by
  classical
  let H := G.induce (A : Set V)
  let T := FixedObstruction.lift A U
  ext v
  constructor
  · intro hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hxPhi, hxU⟩ := Finset.mem_sdiff.mp hx
    have hxT : x.val ∉ T := by
      intro h
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp h
      exact hxU ((Subtype.ext he : y = x) ▸ hy)
    have hneighbor : ∃ y ∈ U, G.Adj y.val x.val := by
      rcases Finset.mem_union.mp hxPhi with h | h
      · exact False.elim (hxU h)
      · obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp h
        exact ⟨y, hy, (H.mem_neighborFinset y x).mp hxy⟩
    obtain ⟨y, hy, hyx⟩ := hneighbor
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨x.property, hxT⟩,
      y.val, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hyx⟩
  · intro hv
    obtain ⟨hvA, hvT⟩ := Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1
    obtain ⟨y, hyT, hyv⟩ := (Finset.mem_filter.mp hv).2
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hyT
    let x : (A : Set V) := ⟨v, hvA⟩
    have hxU : x ∉ U := by
      intro h
      exact hvT (Finset.mem_image.mpr ⟨x, h, rfl⟩)
    have hzx : H.Adj z x := by change G.Adj z.val v; rwa [he]
    exact Finset.mem_image.mpr ⟨x, Finset.mem_sdiff.mpr
      ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨z, hz, (H.mem_neighborFinset z x).mpr hzx⟩), hxU⟩, rfl⟩

attribute [-instance] FinsetCoe.fintype in
private theorem expands_induce_of_no_failure (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V → Bool) (s : ℝ) (hno : a ∉ sampledExpansionFailure G s) :
    CutEscape.Expands (G.induce (sampleVertices a : Set V)) s := by
  classical
  let A := sampleVertices a
  intro U hhalf
  let T := FixedObstruction.lift A U
  have hTc : T.card = U.card := FixedObstruction.card_lift A U
  have hTA : T ⊆ A := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  have hcardA : Fintype.card (A : Set V) = A.card :=
    Fintype.card_of_finset' A (fun _ => Iff.rfl)
  have hhalfT : 2*T.card ≤ A.card := by rw [hTc]; rwa [hcardA] at hhalf
  have hbound : s*(T.card : ℝ) ≤ ((sampleBoundary G A T).card : ℝ) := by
    by_cases hT : T.Nonempty
    · apply le_of_not_gt
      intro h
      exact hno ⟨T,hTA,hT,hhalfT,h⟩
    · have he := Finset.not_nonempty_iff_eq_empty.mp hT
      simp [he]
  have hc := congrArg Finset.card (induced_boundary G A U)
  rw [FixedObstruction.card_lift] at hc
  rw [← hc, hTc] at hbound
  exact hbound

private theorem calibration (C eps a : ℝ) (hC : 0 < C) (heps : 0 < eps) (ha : 0 < a) :
    ∃ K : ℝ, 1000000 ≤ K ∧
      ∀ (n : ℕ) (L : ℝ) (p : unitInterval) (d lam : ℝ),
        2 ≤ n → log (2*n) ≤ L → 0 < (p : ℝ) → 0 < d →
        0 < lam → lam ≤ 1 → K*L ≤ (p : ℝ)*d → a/L^2 ≤ (p : ℝ)*lam →
        4 ≤ (p : ℝ)*d/2 ∧
        5 ≤ (eps*(p : ℝ)*lam)*orderLower C (((p : ℝ)*d/2)/4) := by
  let E := max (1 : ℝ) (1/eps)
  have hE : 1 ≤ E := le_max_left _ _
  have hE0 : 0 < E := by linarith
  obtain ⟨K, _, hK, _, _, _, hparams⟩ := SamplingParameters.exists_sampling_parameters
    (C/8) E a (by positivity) hE ha
  refine ⟨K, hK, ?_⟩
  intro n L p d lam hn hL hp hd hlam hlam1 hscale hpl
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL1 : 1 ≤ L := by
    have hlog : log (4 : ℝ) ≤ L := (log_le_log (by norm_num) (by linarith)).trans hL
    rw [Real.log_four_eq] at hlog
    have htwo := Real.log_two_gt_d9
    linarith
  obtain ⟨_, hmass, _, _⟩ := hparams n L (p : ℝ) d lam hn hL hp p.property.2 hd
    hlam hlam1 hscale hpl
  have hbase : 1000000*L ≤ (p : ℝ)*d :=
    (mul_le_mul_of_nonneg_right hK (by linarith : 0 ≤ L)).trans hscale
  have hident : orderLower (C/8) (((p : ℝ)*d)/64) =
      orderLower C (((p : ℝ)*d/2)/4) := by
    have hinner : (((p : ℝ)*d)/64)/(2*(C/8)) = (((p : ℝ)*d/2)/4)/(2*C) := by
      field_simp
      <;> ring
    simp only [orderLower, hinner]
  rw [hident] at hmass
  have heE : 1 ≤ eps*E := by
    have hh := (div_le_iff₀ heps).mp (le_max_right (1 : ℝ) (1/eps))
    nlinarith
  have hscalar : 100*L/(1/(64000*E)) = 6400000*E*L := by field_simp; ring
  rw [hscalar] at hmass
  have hh := mul_le_mul_of_nonneg_left hmass heps.le
  have hh' := mul_le_mul_of_nonneg_right heE (show 0 ≤ 6400000*L by positivity)
  refine ⟨by linarith, ?_⟩
  nlinarith

/-- All centers and queries refer to original vertices; toughness is on the literal induced layer. -/
def LayerGood (G : SimpleGraph V) [DecidableRel G.Adj] (rho D : ℝ)
    (S : I → Finset V) (A : Finset V) : Prop :=
  A.Nonempty ∧
  (∀ v, rho/2 ≤ (restrictedDegree G A v : ℝ)) ∧
  (∀ v, (restrictedDegree G A v : ℝ) ≤ 2*D*rho) ∧
  OrdinaryTough (G.induce (A : Set V)) (1/(64*D)) ∧
  ∀ i, rho/2 ≤ ((S i ∩ A).card : ℝ)

attribute [-instance] FinsetCoe.fintype in
/-- A single actual uniform label outcome supplies every tough layer and every fixed query. -/
theorem exists_tough_layers (D a : ℝ) (hD : 1 ≤ D) (ha : 0 < a) :
    ∃ K : ℝ, 1000000 ≤ K ∧
    ∀ (V I : Type*) [Fintype V] [DecidableEq V] [Fintype I]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬HasRichCycle G →
    ∀ (b : ℕ) (hb : 1 ≤ b) (d lam L : ℝ) (S : I → Finset V),
      2 ≤ Fintype.card V → b ≤ Fintype.card V → 0 < d → 0 < lam → lam ≤ 1 →
      CutEscape.Expands G lam →
      (∀ v, d ≤ (G.degree v : ℝ)) → (∀ v, (G.degree v : ℝ) ≤ D*d) →
      Fintype.card I ≤ 2*Fintype.card V → (∀ i, d ≤ ((S i).card : ℝ)) →
      log (2*Fintype.card V) ≤ L → K*L ≤ (UniformLayers.rate b hb : ℝ)*d →
      a/L^2 ≤ (UniformLayers.rate b hb : ℝ)*lam →
      ∃ omega : V → Fin b,
        (∀ i, LayerGood G ((UniformLayers.rate b hb : ℝ)*d) D S (UniformLayers.layer omega i)) ∧
        Pairwise (fun i j => Disjoint (UniformLayers.layer omega i) (UniformLayers.layer omega j)) ∧
        Finset.univ.biUnion (UniformLayers.layer omega) = Finset.univ := by
  obtain ⟨C, hC, htough⟩ := Toughness.exists_toughness_constant
  obtain ⟨Ks, eps, hKs, heps, _, hsampler⟩ := Sampler.exists_sampler_constants D a hD ha
  obtain ⟨Kg, hKg, hcalib⟩ := calibration C eps a hC heps ha
  let K := max Ks Kg
  refine ⟨K, hKs.trans (le_max_left _ _), ?_⟩
  intro V I _ _ _ G _ havoid b hb d lam L S hn hbn hd hlam hlam1 hexp hlo hhi hI hS hL hscale hpl
  classical
  let p := UniformLayers.rate b hb
  let rho := (p : ℝ)*d
  let n := Fintype.card V
  have hp : 0 < (p : ℝ) := by
    have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    change 0 < 1/(b : ℝ)
    positivity
  have hrho : 0 < rho := mul_pos hp hd
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL0 : 0 < L := (log_pos (by linarith : (1 : ℝ) < 2*n)).trans_le hL
  have hKsL : Ks*L ≤ (p : ℝ)*d :=
    (mul_le_mul_of_nonneg_right (le_max_left Ks Kg) hL0.le).trans hscale
  have hKgL : Kg*L ≤ (p : ℝ)*d :=
    (mul_le_mul_of_nonneg_right (le_max_right Ks Kg) hL0.le).trans hscale
  have hr : 1000000*log (2*Fintype.card V) ≤ rho := by
    calc
      _ ≤ 1000000*L := mul_le_mul_of_nonneg_left hL (by norm_num)
      _ ≤ Ks*L := mul_le_mul_of_nonneg_right hKs hL0.le
      _ ≤ _ := hKsL
  obtain ⟨hdelta, hsize⟩ := hcalib n L p d lam hn hL hp hd hlam hlam1 hKgL hpl
  have hfail := hsampler V G havoid p d lam L hn hp hd hlam hlam1 hexp hlo hhi hL hKsL hpl
  have hgood := InitialConcentration.bad_goodSample_probability G p d D (by omega)
    hd.le hD hlo hhi hr
  have hquery := UniformLayers.fixed_query_failure_bound p d S hn hI hS hr
  have hconstruct (z : V → Bool) (hg : GoodSample G p d D z)
      (hf : z ∉ sampledExpansionFailure G (eps*(p : ℝ)*lam))
      (hq : ∀ i, rho/2 ≤ ((S i ∩ sampleVertices z).card : ℝ)) :
      LayerGood G rho D S (sampleVertices z) := by
    let A := sampleVertices z
    let H := G.induce (A : Set V)
    have hA : A.Nonempty := by
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
      have hl := hg.2.1 v
      have hc : (restrictedDegree G A v : ℝ) ≤ A.card := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      have hcpos : (0 : ℝ) < A.card := by dsimp [rho] at hrho; linarith
      exact Finset.card_pos.mp (by exact_mod_cast hcpos)
    have hnA : 1 ≤ Fintype.card (A : Set V) := by
      have hc := Fintype.card_of_finset' A (fun _ => Iff.rfl)
      rw [hc]
      exact Nat.succ_le_of_lt (Finset.card_pos.mpr hA)
    let f : H →g G := { toFun := Subtype.val, map_rel' := fun h => h }
    have havH : ¬HasRichCycle H := not_hasRichCycle_of_injective_hom f Subtype.val_injective havoid
    have hminH : ∀ v : (A : Set V), rho/2 ≤ (H.degree v : ℝ) := by
      intro v
      rw [← restrictedDegree_eq_induce G A v]
      exact hg.2.1 v.val
    have hmaxH : ∀ v : (A : Set V), (H.degree v : ℝ) ≤ (4*D)*(rho/2) := by
      intro v
      rw [← restrictedDegree_eq_induce G A v]
      have hh := hg.2.2 v.val
      dsimp [rho]
      nlinarith only [hh]
    have ht := htough (A : Set V) H havH (rho/2) (4*D) (eps*(p : ℝ)*lam)
      hnA hdelta (by linarith) (by positivity)
      (expands_induce_of_no_failure G z (eps*(p : ℝ)*lam) hf) hminH hmaxH hsize
    have heta : 1/(16*(4*D)) = (1/(64*D) : ℝ) := by ring
    rw [heta] at ht
    exact ⟨hA, hg.2.1, hg.2.2, ht, hq⟩
  have hprob : (sampleMeasure V p).real
      {z | ¬LayerGood G rho D S (sampleVertices z)} ≤ 2/(n : ℝ)^4 := by
    let E := sampledExpansionFailure G (eps*(p : ℝ)*lam)
    let B := {z | ¬GoodSample G p d D z}
    let Q := {z | ∃ i, ((S i ∩ sampleVertices z).card : ℝ) < rho/2}
    have hsub : {z | ¬LayerGood G rho D S (sampleVertices z)} ⊆ (E ∪ B) ∪ Q := by
      intro z hz
      by_cases he : z ∈ E
      · exact Or.inl (Or.inl he)
      by_cases hb' : z ∈ B
      · exact Or.inl (Or.inr hb')
      by_cases hq : z ∈ Q
      · exact Or.inr hq
      have hg : GoodSample G p d D z := not_not.mp hb'
      have hq' : ∀ i, rho/2 ≤ ((S i ∩ sampleVertices z).card : ℝ) := by
        intro i
        exact le_of_not_gt (fun h => hq ⟨i, h⟩)
      exact False.elim (hz (hconstruct z hg he hq'))
    have hu := (measureReal_mono (μ := sampleMeasure V p) hsub (measure_ne_top _ _)).trans
      (measureReal_union_le (E ∪ B) Q)
    have hu' := measureReal_union_le (μ := sampleMeasure V p) E B
    change (sampleMeasure V p).real E < 1/(n : ℝ)^4 at hfail
    change (sampleMeasure V p).real B ≤ 1/(2*(n : ℝ)^4) at hgood
    change (sampleMeasure V p).real Q ≤ 1/(2*(n : ℝ)^4) at hquery
    have hnorm : 1/(n : ℝ)^4 + 1/(2*(n : ℝ)^4) + 1/(2*(n : ℝ)^4) =
        2/(n : ℝ)^4 := by ring
    linarith only [hu, hu', hfail, hgood, hquery, hnorm]
  have hbR : (b : ℝ) ≤ n := by exact_mod_cast hbn
  have hn3 : (8 : ℝ) ≤ (n : ℝ)^3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnR 3
    norm_num at hh
    exact hh
  have hn4 : 8*(n : ℝ) ≤ (n : ℝ)^4 := by
    have hh := mul_le_mul_of_nonneg_right hn3 hn0.le
    nlinarith only [hh]
  have hbudget : (b : ℝ)*(2/(n : ℝ)^4) ≤ 1/4 := by
    rw [show (b : ℝ)*(2/(n : ℝ)^4) = 2*b/(n : ℝ)^4 by ring]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)^4) (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith only [hbR,hn4]
  apply UniformLayers.exists_all_layers_good b hb
    (fun _ A => LayerGood G rho D S A) (fun _ => 2/(n : ℝ)^4) (fun _ => hprob)
  have he : (∑ _i : Fin b, 2/(n : ℝ)^4) = (b : ℝ)*(2/(n : ℝ)^4) := by simp
  rw [he]
  exact lt_of_le_of_lt hbudget (by norm_num)

end Erdos642.DenseMask20261019.ToughLayersV2
