import Openmath.Erdos642.Proofs.DenseMask20261019.GlobalObstruction

/-! The actual right-associated sampling experiment has the sprinkler joint law. -/
noncomputable section
namespace Erdos642.DenseMask20261019.SprinklingTransport
open MeasureTheory ProbabilityTheory Finset
open OAI.ErdosGallai.Sampling
open Erdos585.Attempt6.SourcePools
open Erdos642.DenseMask20261019.NestedSampling
open Erdos642.DenseMask20261019.GlobalObstruction
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem experiment_pair_map (p : unitInterval) :
    (experiment V p).map (fun x => (thin (thin x.1 x.2.1) x.2.2, thin x.1 x.2.1)) =
    ((sampleMeasure V (quarter p)).prod (sampleMeasure V (sprinkle p))).map
      (fun x => (x.1,fun v => x.1 v || x.2 v)) := by
  have ha := (measurePreserving_prodAssoc (sampleMeasure V p)
    (sampleMeasure V half) (sampleMeasure V half)).map_eq
  rw [experiment, ← ha, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  exact nested_mask_joint_law p

/-- Equality for every predicate of the two actual original vertex finsets. -/
theorem experiment_event_eq (p : unitInterval) (P : Finset V → Finset V → Prop) :
    (experiment V p).real {x | P
      (sampleVertices x.1 ∩ sampleVertices (thin x.2.1 x.2.2))
      (sampleVertices x.1 ∩ sampleVertices x.2.1)} =
    ((sampleMeasure V (quarter p)).prod (sampleMeasure V (sprinkle p))).real
      {x | P (sampleVertices x.1) (sampleVertices x.1 ∪ sampleVertices x.2)} := by
  classical
  have h := congrArg (fun μ : Measure ((V → Bool) × (V → Bool)) =>
    μ.real {x | P (sampleVertices x.1) (sampleVertices x.2)}) (experiment_pair_map (V := V) p)
  simp only [Measure.real, Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete] at h
  have hthin (a b : V → Bool) : sampleVertices (thin a b) = sampleVertices a ∩ sampleVertices b := by
    ext v; simp [sampleVertices,thin]
  have hor (a b : V → Bool) : sampleVertices (fun v => a v || b v) =
      sampleVertices a ∪ sampleVertices b := by
    ext v; simp [sampleVertices]
  simpa only [Measure.real, Set.preimage_setOf_eq, hthin, hor, Finset.inter_assoc] using h

end Erdos642.DenseMask20261019.SprinklingTransport
