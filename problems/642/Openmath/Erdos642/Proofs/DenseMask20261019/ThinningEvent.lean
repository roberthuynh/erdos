import Openmath.Erdos642.Proofs.DenseMask20261019.NestedSampling

/-! Fixed-history boundary avoidance is independent of both surviving masks. -/
noncomputable section
namespace Erdos642.DenseMask20261019.ThinningEvent
open MeasureTheory ProbabilityTheory Finset
open OAI.ErdosGallai.Sampling
open Erdos642.DenseMask20261019.NestedSampling
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def restrictedPair (W : Finset V) (x : (V → Bool) × (V → Bool)) :
    (W → Bool) × (W → Bool) := (fun w => x.1 w,fun w => x.2 w)

lemma restrict_sample_map (W : Finset V) (p : unitInterval) :
    (sampleMeasure V p).map (fun x (w : W) => x w) = sampleMeasure W p := by
  have hi : iIndepFun (fun v : V => fun x : V → Bool => x v) (sampleMeasure V p) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
  have hj := hi.precomp (g := fun w : W => (w : V)) Subtype.val_injective
  rw [hj.map_fun_eq_pi_map (fun _ => (measurable_of_finite _).aemeasurable)]
  unfold sampleMeasure
  congr 1
  funext w
  exact (measurePreserving_eval (fun _ : V => bernoulliMeasure true false p) (w : V)).map_eq

lemma restrictedPair_map (W : Finset V) (p q : unitInterval) :
    ((sampleMeasure V p).prod (sampleMeasure V q)).map (restrictedPair W) =
      (sampleMeasure W p).prod (sampleMeasure W q) := by
  rw [← restrict_sample_map W p, ← restrict_sample_map W q,
    Measure.map_prod_map _ _ (measurable_of_finite _) (measurable_of_finite _)]
  rfl

/-- Independence on disjoint fixed coordinate sets for the full pair of masks. -/
lemma boundary_factorization (T W : Finset V) (hTW : Disjoint T W)
    (p q : unitInterval) (E : Set ((W → Bool) × (W → Bool))) :
    ((sampleMeasure V p).prod (sampleMeasure V q)).real
      {x | Disjoint T (sampleVertices x.1) ∧ restrictedPair W x ∈ E} =
    ((sampleMeasure V p).prod (sampleMeasure V q)).real
      {x | Disjoint T (sampleVertices x.1)} *
    ((sampleMeasure V p).prod (sampleMeasure V q)).real
      {x | restrictedPair W x ∈ E} := by
  let μ : Measure (V → Bool × Bool) := Measure.pi
    (fun _ : V => (bernoulliMeasure true false p).prod (bernoulliMeasure true false q))
  let split := MeasurableEquiv.arrowProdEquivProdArrow Bool Bool V
  have hmap : μ.map split = (sampleMeasure V p).prod (sampleMeasure V q) :=
    (measurePreserving_arrowProdEquivProdArrow Bool Bool V
      (fun _ => bernoulliMeasure true false p) (fun _ => bernoulliMeasure true false q)).map_eq
  have hi : iIndepFun (fun v : V => fun x : V → Bool × Bool => x v) μ :=
    iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
  have hj := hi.indepFun_finset T W hTW (fun _ => measurable_of_finite _)
  let ET : Set (T → Bool × Bool) := {x | ∀ t, (x t).1 = false}
  let EW : Set (W → Bool × Bool) := {x | (fun w => (x w).1,fun w => (x w).2) ∈ E}
  have hh := hj.measure_inter_preimage_eq_mul ET EW
    MeasurableSet.of_discrete MeasurableSet.of_discrete
  have hr := congrArg ENNReal.toReal hh
  rw [ENNReal.toReal_mul] at hr
  have hT : {x : V → Bool × Bool | Disjoint T (sampleVertices (split x).1)} =
      (fun x (t : T) => x t) ⁻¹' ET := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ET]
    simp only [Finset.disjoint_left, sampleVertices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h t
      have ht := h t.property
      change ¬ (x t).1 = true at ht
      cases he : (x t).1 <;> simp_all
    · intro h v hv
      have ht := h ⟨v,hv⟩
      change (x v).1 = false at ht
      change ¬ (x v).1 = true
      simp [ht]
  have hW : {x : V → Bool × Bool | restrictedPair W (split x) ∈ E} =
      (fun x (w : W) => x w) ⁻¹' EW := by rfl
  rw [← hmap]
  simp only [Measure.real, Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  have hBoth : split ⁻¹' {x | Disjoint T (sampleVertices x.1) ∧ restrictedPair W x ∈ E} =
      {x : V → Bool × Bool | Disjoint T (sampleVertices (split x).1)} ∩
      {x : V → Bool × Bool | restrictedPair W (split x) ∈ E} := by rfl
  rw [hBoth, hT, hW]
  change _ = (μ {x | Disjoint T (sampleVertices (split x).1)}).toReal *
    (μ {x | restrictedPair W (split x) ∈ E}).toReal
  rw [hT, hW]
  exact hr

/-- Exact avoidance factor times the genuine within-survivor two-mask law. -/
theorem fixed_boundary_event (T W : Finset V) (hTW : Disjoint T W)
    (p q : unitInterval) (E : Set ((W → Bool) × (W → Bool))) :
    ((sampleMeasure V p).prod (sampleMeasure V q)).real
      {x | Disjoint T (sampleVertices x.1) ∧ restrictedPair W x ∈ E} =
    (1-(p : ℝ))^T.card * ((sampleMeasure W p).prod (sampleMeasure W q)).real E := by
  rw [boundary_factorization T W hTW p q E]
  have hT : {x : (V → Bool) × (V → Bool) | Disjoint T (sampleVertices x.1)} =
      {x : V → Bool | Disjoint T (sampleVertices x)} ×ˢ Set.univ := by ext x; simp
  rw [hT, measureReal_prod_prod, probReal_univ, mul_one, sample_miss_probability]
  congr 1
  rw [← restrictedPair_map W p q]
  simp only [Measure.real,
    Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  rfl

/-- Two independent fair thinnings of fixed A: deleting T at the first stage
costs exactly 2 to the power minus |T|, independently of every event on A minus T. -/
theorem fair_thinning_event (A T : Finset V) (hTA : T ⊆ A)
    (E : Set ((↥(A \ T) → Bool) × (↥(A \ T) → Bool))) :
    ((sampleMeasure V half).prod (sampleMeasure V half)).real
      {x | Disjoint T (A ∩ sampleVertices x.1) ∧ restrictedPair (A \ T) x ∈ E} =
    (1/2 : ℝ)^T.card *
      ((sampleMeasure ↥(A \ T) half).prod (sampleMeasure ↥(A \ T) half)).real E := by
  have hd : Disjoint T (A \ T) := by
    apply Finset.disjoint_left.mpr
    intro v ht hw
    exact (Finset.mem_sdiff.mp hw).2 ht
  have he : ∀ x : V → Bool, Disjoint T (A ∩ sampleVertices x) ↔
      Disjoint T (sampleVertices x) := by
    intro x
    simp only [Finset.disjoint_left, Finset.mem_inter]
    constructor
    · intro h v ht hx
      exact h ht ⟨hTA ht,hx⟩
    · intro h v ht hx
      exact h ht hx.2
  simp_rw [he]
  have hh := fixed_boundary_event T (A \ T) hd half half E
  have hv : 1 - (half : ℝ) = (1 / 2 : ℝ) := by norm_num [half]
  rw [hv] at hh
  exact hh

end Erdos642.DenseMask20261019.ThinningEvent
