import Openmath.Attempt6.SourcePools

                                                 
noncomputable section
namespace Erdos642.DenseMask20261019.NestedSampling
open MeasureTheory ProbabilityTheory
open OAI.ErdosGallai.Sampling
open Erdos585.Attempt6.SourcePools
attribute [local instance] Classical.propDecidable

def half : unitInterval := ⟨1/2, by norm_num, by norm_num⟩
def quarter (p : unitInterval) : unitInterval := ⟨(p : ℝ)/4, by
  constructor <;> nlinarith [p.property.1, p.property.2]⟩
def sprinkle (p : unitInterval) : unitInterval := ⟨(p : ℝ)/(4-p), by
  have hp := p.property
  have hd : (0 : ℝ) < 4-p := by linarith [p.property.2]
  exact ⟨div_nonneg hp.1 hd.le, (div_le_one hd).mpr (by linarith [p.property.2])⟩⟩

def descend (x : Bool × Bool) : Bool × Bool := (x.1 && x.2, x.1)
def ascend (x : Bool × Bool) : Bool × Bool := (x.1, x.1 || x.2)

lemma coordinate_joint_law (p : unitInterval) :
    ((bernoulliMeasure true false (mulProbability p half)).prod
      (bernoulliMeasure true false half)).map descend =
    ((bernoulliMeasure true false (quarter p)).prod
      (bernoulliMeasure true false (sprinkle p))).map ascend := by
  let μ := (bernoulliMeasure true false (mulProbability p half)).prod
    (bernoulliMeasure true false half)
  let ν := (bernoulliMeasure true false (quarter p)).prod
    (bernoulliMeasure true false (sprinkle p))
  haveI : IsProbabilityMeasure (μ.map descend) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable
  haveI : IsProbabilityMeasure (ν.map ascend) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable
  change μ.map descend = ν.map ascend
  apply Measure.ext_of_singleton
  intro x
  suffices he : (μ.map descend).real {x} = (ν.map ascend).real {x} by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (μ.map descend) {x}),
      ← ENNReal.ofReal_toReal (measure_ne_top (ν.map ascend) {x})]
    exact congrArg ENNReal.ofReal he
  simp only [Measure.real, Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  change μ.real (descend ⁻¹' {x}) = ν.real (ascend ⁻¹' {x})
  have hd : (4-(p : ℝ)) ≠ 0 := by linarith [p.property.2]
  rcases x with ⟨a,b⟩
  cases a <;> cases b
  · have h₁ : descend ⁻¹' {(false,false)} = ({false} : Set Bool) ×ˢ Set.univ := by
      ext ⟨a,b⟩; cases a <;> cases b <;> simp [descend]
    have h₂ : ascend ⁻¹' {(false,false)} = ({false} : Set Bool) ×ˢ {false} := by
      ext ⟨a,b⟩; cases a <;> cases b <;> simp [ascend]
    rw [h₁,h₂]
    simp only [μ,ν,measureReal_prod_prod]
    simp [bernoulliMeasure_real_apply,mulProbability,half,quarter,sprinkle]
    field_simp [hd]
    <;> ring
  · have h₁ : descend ⁻¹' {(false,true)} = ({true} : Set Bool) ×ˢ {false} := by
      ext ⟨a,b⟩; cases a <;> cases b <;> simp [descend]
    have h₂ : ascend ⁻¹' {(false,true)} = ({false} : Set Bool) ×ˢ {true} := by
      ext ⟨a,b⟩; cases a <;> cases b <;> simp [ascend]
    rw [h₁,h₂]
    simp only [μ,ν,measureReal_prod_prod]
    simp [bernoulliMeasure_real_apply,mulProbability,half,quarter,sprinkle]
    field_simp [hd]
    <;> ring
  · have h₁ : descend ⁻¹' {(true,false)} = ∅ := by
      ext ⟨a,b⟩; cases a <;> cases b <;> simp [descend]
    have h₂ : ascend ⁻¹' {(true,false)} = ∅ := by
      ext ⟨a,b⟩; cases a <;> cases b <;> simp [ascend]
    rw [h₁,h₂]
    simp
  · have h₁ : descend ⁻¹' {(true,true)} = ({true} : Set Bool) ×ˢ {true} := by
      ext ⟨a,b⟩; cases a <;> cases b <;> simp [descend]
    have h₂ : ascend ⁻¹' {(true,true)} = ({true} : Set Bool) ×ˢ Set.univ := by
      ext ⟨a,b⟩; cases a <;> cases b <;> simp [ascend]
    rw [h₁,h₂]
    simp only [μ,ν,measureReal_prod_prod]
    simp [bernoulliMeasure_real_apply,mulProbability,half,quarter,sprinkle]
    ring

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma coordinate_map (p q : unitInterval) (f : Bool × Bool → Bool × Bool) :
    ((sampleMeasure V p).prod (sampleMeasure V q)).map
      (fun x v => f (x.1 v,x.2 v)) =
    Measure.pi (fun _ : V => ((bernoulliMeasure true false p).prod
      (bernoulliMeasure true false q)).map f) := by
  have hpair := (measurePreserving_arrowProdEquivProdArrow Bool Bool V
    (fun _ => bernoulliMeasure true false p) (fun _ => bernoulliMeasure true false q)).map_eq
  change (Measure.pi (fun _ : V => (bernoulliMeasure true false p).prod
    (bernoulliMeasure true false q))).map
      (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool V) =
    (sampleMeasure V p).prod (sampleMeasure V q) at hpair
  rw [← hpair, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  exact Measure.pi_map_pi (fun _ => (measurable_of_finite _).aemeasurable)

/-- Full joint law of a half thinning and its parent mask. -/
theorem two_mask_joint_law (p : unitInterval) :
    ((sampleMeasure V (mulProbability p half)).prod (sampleMeasure V half)).map
      (fun x => (thin x.1 x.2,x.1)) =
    ((sampleMeasure V (quarter p)).prod (sampleMeasure V (sprinkle p))).map
      (fun x => (x.1,fun v => x.1 v || x.2 v)) := by
  have h : ((sampleMeasure V (mulProbability p half)).prod (sampleMeasure V half)).map
      (fun x v => descend (x.1 v,x.2 v)) =
    ((sampleMeasure V (quarter p)).prod (sampleMeasure V (sprinkle p))).map
      (fun x v => ascend (x.1 v,x.2 v)) := by
    rw [coordinate_map,coordinate_map,coordinate_joint_law]
  have hh := congrArg (fun μ : Measure (V → Bool × Bool) =>
    μ.map (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool V)) h
  simp only [Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    Function.comp_def, MeasurableEquiv.arrowProdEquivProdArrow,
    MeasurableEquiv.coe_mk, Equiv.arrowProdEquivProdArrow,
    Equiv.coe_fn_mk, descend, ascend, thin] at hh
  convert hh using 1 <;> congr 1 <;> funext x <;> apply Prod.ext <;> funext v <;> rfl

/-- The original three independent masks have the same entire joint law as
an iid quarter mask and its independent sprinkling extension. -/
theorem nested_mask_joint_law (p : unitInterval) :
    (((sampleMeasure V p).prod (sampleMeasure V half)).prod (sampleMeasure V half)).map
      (fun x => (thin (thin x.1.1 x.1.2) x.2,thin x.1.1 x.1.2)) =
    ((sampleMeasure V (quarter p)).prod (sampleMeasure V (sprinkle p))).map
      (fun x => (x.1,fun v => x.1 v || x.2 v)) := by
  have h := two_mask_joint_law (V := V) p
  rw [← thin_map p half] at h
  have he := Measure.map_prod_map
    ((sampleMeasure V p).prod (sampleMeasure V half)) (sampleMeasure V half)
    (measurable_of_finite (fun x => thin x.1 x.2)) measurable_id
  simp only [Measure.map_id] at he
  rw [he,Measure.map_map (measurable_of_finite _) (measurable_of_finite _)] at h
  exact h

end Erdos642.DenseMask20261019.NestedSampling
