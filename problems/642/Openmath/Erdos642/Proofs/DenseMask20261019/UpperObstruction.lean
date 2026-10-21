import Openmath.Erdos642.Proofs.DenseMask20261019.ObstructionCollections
import Openmath.Erdos642.Proofs.DenseMask20261019.SprinklingTransport
import Openmath.Erdos642.Proofs.DenseMask20261019.CutEscape

/-! Global probability of the actual original-component obstruction. -/
noncomputable section
namespace Erdos642.DenseMask20261019.UpperObstruction
open Finset SimpleGraph MeasureTheory ProbabilityTheory Real
open OAI.ErdosGallai.Sampling
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.CutExtraction
open Erdos642.DenseMask20261019
open FixedObstruction GlobalObstruction ComponentObstruction ComponentEntropy AvoidanceOrder
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem union_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q : Finset V) (F : Finset (mask G Q).ConnectedComponent) :
    unionVertices G Q F ⊆ Q := by
  intro v hv
  obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hv
  exact ((mem_componentVertices G Q c v).mp hc).1

/-- Actual component collections and the actual sprinkler defeat every section. -/
theorem section_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ℝ) (p : unitInterval) (d D lam k : ℝ) (Q : Finset V)
    (hn : 2 ≤ Fintype.card V) (hp : 0 < (p : ℝ)) (hd : 0 < d)
    (hD : 1 ≤ D) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hexp : CutEscape.Expands G lam) (hk : 0 < k)
    (hkN : k ≤ 3*(p : ℝ)*Fintype.card V/5)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ))
    (hm : 0 < orderLower C (((p : ℝ)*d)/64))
    (hmk : orderLower C (((p : ℝ)*d)/64) ≤ k) :
    (sampleMeasure V (NestedSampling.sprinkle p)).real
      {z | Obstruction G C ((p : ℝ)*d) (2*D*((p : ℝ)*d)) k
        Q (Q ∪ sampleVertices z)} ≤
      exp (2*k*log (Fintype.card V)/orderLower C (((p : ℝ)*d)/64) -
        (p : ℝ)*lam*k/(128000*D)) := by
  classical
  let m := orderLower C (((p : ℝ)*d)/64)
  let nu := sampleMeasure V (NestedSampling.sprinkle p)
  by_cases hcap : ∀ v, (restrictedDegree G Q v : ℝ) ≤ 2*D*((p : ℝ)*d)
  · let T := (collections G Q m k).filter (fun F =>
      k/5 ≤ ((unionVertices G Q F).card : ℝ) ∧
      ((unionVertices G Q F).card : ℝ) ≤ 9*k/17)
    let E := fun F : Finset (mask G Q).ConnectedComponent =>
      {z : V → Bool |
        ((componentUnion G (Q ∪ sampleVertices z) (unionVertices G Q F)).card : ℝ) ≤ 9*k/17 ∧
        componentUnion G (Q ∪ sampleVertices z) (unionVertices G Q F) ⊆
          closedNeighborhood G (unionVertices G Q F)}
    have hsub : {z | Obstruction G C ((p : ℝ)*d) (2*D*((p : ℝ)*d)) k
        Q (Q ∪ sampleVertices z)} ⊆ ⋃ F ∈ T, E F := by
      intro z hz
      obtain ⟨F, hF, _, _, hlo, hhi, hreach, hphi⟩ :=
        ObstructionCollections.obstruction_collection G C ((p : ℝ)*d)
          (2*D*((p : ℝ)*d)) k Q (Q ∪ sampleVertices z) hk.le hz
      exact Set.mem_iUnion.mpr ⟨F, Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨hF, hlo, hhi⟩, hreach, hphi⟩⟩
    have hsection : ∀ F ∈ T, nu.real (E F) ≤ exp (-(p : ℝ)*lam*k/(128000*D)) := by
      intro F hF
      obtain ⟨_, hlo, hhi⟩ := Finset.mem_filter.mp hF
      apply CutEscape.fixed_union_escape G Q (unionVertices G Q F) p d D lam k
        hp hd hD hlam hlam1 hexp hk hkN (union_subset G Q F) hdeg _ hlo hhi
      intro v
      calc
        _ ≤ 2*D*((p : ℝ)*d) := hcap v
        _ = _ := by ring
    have hcount : (T.card : ℝ) ≤ exp (2*k*log (Fintype.card V)/m) := by
      exact (show (T.card : ℝ) ≤ (collections G Q m k).card from by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)).trans
          (collections_card_exp G Q m k hm hmk hn)
    calc
      _ ≤ nu.real (⋃ F ∈ T, E F) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ F ∈ T, nu.real (E F) := measureReal_biUnion_finset_le T E
      _ ≤ ∑ _F ∈ T, exp (-(p : ℝ)*lam*k/(128000*D)) :=
        Finset.sum_le_sum hsection
      _ = (T.card : ℝ)*exp (-(p : ℝ)*lam*k/(128000*D)) := by simp
      _ ≤ exp (2*k*log (Fintype.card V)/m)*exp (-(p : ℝ)*lam*k/(128000*D)) :=
        mul_le_mul_of_nonneg_right hcount (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1; dsimp [m]; ring
  · have he : {z | Obstruction G C ((p : ℝ)*d) (2*D*((p : ℝ)*d)) k
        Q (Q ∪ sampleVertices z)} = ∅ := by
      ext z
      constructor
      · intro hz; exact hcap hz.2.2.1
      · intro hz; exact False.elim hz
    rw [he, measureReal_empty]
    positivity

/-- Full original experiment upper bound, with actual event transport and integration. -/
theorem obstruction_probability_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ℝ) (p : unitInterval) (d D lam k : ℝ)
    (hn : 2 ≤ Fintype.card V) (hp : 0 < (p : ℝ)) (hd : 0 < d)
    (hD : 1 ≤ D) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hexp : CutEscape.Expands G lam) (hk : 0 < k)
    (hkN : k ≤ 3*(p : ℝ)*Fintype.card V/5)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ))
    (hm : 0 < orderLower C (((p : ℝ)*d)/64))
    (hmk : orderLower C (((p : ℝ)*d)/64) ≤ k) :
    (experiment V p).real (obstructionEvent G C ((p : ℝ)*d) D k) ≤
      exp (2*k*log (Fintype.card V)/orderLower C (((p : ℝ)*d)/64) -
        (p : ℝ)*lam*k/(128000*D)) := by
  let delta := exp (2*k*log (Fintype.card V)/orderLower C (((p : ℝ)*d)/64) -
    (p : ℝ)*lam*k/(128000*D))
  have ht := SprinklingTransport.experiment_event_eq p
    (fun Q M => Obstruction G C ((p : ℝ)*d) (2*D*((p : ℝ)*d)) k Q M)
  change (experiment V p).real (obstructionEvent G C ((p : ℝ)*d) D k) = _ at ht
  rw [ht, Erdos585.Attempt6.RegularizationTransport.finite_product_failure]
  calc
    _ ≤ ∫ _a : V → Bool, delta ∂sampleMeasure V (NestedSampling.quarter p) := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro a
      exact section_upper G C p d D lam k (sampleVertices a) hn hp hd hD
        hlam hlam1 hexp hk hkN hdeg hm hmk
    _ = _ := by simp [delta]

end Erdos642.DenseMask20261019.UpperObstruction
