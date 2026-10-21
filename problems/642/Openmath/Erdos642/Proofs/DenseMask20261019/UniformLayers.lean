import Openmath.Attempt6.CategoricalPools
import Openmath.Attempt6.PublicBernoulli

/-! Independent uniform vertex labels, exact Bernoulli layer marginals,
and simultaneous fixed-query lower bounds. -/
noncomputable section
namespace Erdos642.DenseMask20261019.UniformLayers
open MeasureTheory ProbabilityTheory Finset Real
open OAI.ErdosGallai.Sampling
open Erdos585.Attempt6.CategoricalPools
attribute [local instance] Classical.propDecidable
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

def rate (b : ℕ) (hb : 1 ≤ b) : unitInterval :=
  ⟨1/(b : ℝ), by
    have h : (1 : ℝ) ≤ b := by exact_mod_cast hb
    constructor
    · positivity
    · exact (div_le_one (by positivity : (0 : ℝ) < b)).mpr h⟩

lemma uniform_weight_sum (b : ℕ) (hb : 1 ≤ b) :
    ∑ _i : Fin b, (1/(b : ℝ)) = 1 := by
  have h : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  simp [h]

def labelLaw (b : ℕ) (hb : 1 ≤ b) : Measure (V → Fin b) :=
  Measure.pi (fun _ : V => finiteLaw (fun _ : Fin b => 1/(b : ℝ))
    (fun _ => by positivity) (uniform_weight_sum b hb))

instance labelLaw_probability (b : ℕ) (hb : 1 ≤ b) :
    IsProbabilityMeasure (labelLaw (V := V) b hb) := by
  unfold labelLaw
  infer_instance

def layerMask {b : ℕ} (ω : V → Fin b) (i : Fin b) : V → Bool :=
  fun v => decide (ω v = i)

def layer {b : ℕ} (ω : V → Fin b) (i : Fin b) : Finset V :=
  sampleVertices (layerMask ω i)

@[simp] lemma mem_layer {b : ℕ} (ω : V → Fin b) (i : Fin b) (v : V) :
    v ∈ layer ω i ↔ ω v = i := by simp [layer, layerMask, sampleVertices]

theorem label_coordinates_independent (b : ℕ) (hb : 1 ≤ b) :
    iIndepFun (fun v : V => fun ω : V → Fin b => ω v) (labelLaw b hb) :=
  iIndepFun_pi (X := fun _ : V => id) (fun _ => measurable_id.aemeasurable)

theorem layerMask_map (b : ℕ) (hb : 1 ≤ b) (i : Fin b) :
    (labelLaw (V := V) b hb).map (fun ω => layerMask ω i) =
      sampleMeasure V (rate b hb) := by
  let μ := finiteLaw (fun _ : Fin b => 1/(b : ℝ))
    (fun _ => by positivity) (uniform_weight_sum b hb)
  have hi := label_coordinates_independent (V := V) b hb
  have hj := hi.comp (fun _ : V => fun j : Fin b => decide (j = i))
    (fun _ => measurable_of_finite _)
  change iIndepFun (fun v : V => fun ω : V → Fin b => decide (ω v = i))
    (labelLaw b hb) at hj
  change (labelLaw (V := V) b hb).map (fun ω v => decide (ω v = i)) = _
  rw [hj.map_fun_eq_pi_map (fun _ => (measurable_of_finite _).aemeasurable)]
  unfold sampleMeasure
  congr 1
  funext v
  have hcoord := (measurePreserving_eval (fun _ : V => μ) v).map_eq
  have hcomp : (labelLaw (V := V) b hb).map (fun ω => decide (ω v = i)) =
      μ.map (fun j => decide (j = i)) := by
    rw [← hcoord, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
    rfl
  rw [hcomp]
  haveI : IsProbabilityMeasure (μ.map (fun j => decide (j = i))) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable
  apply Erdos585.Attempt6.RegularizationTransport.bool_measure_eq_bernoulli
  rw [Measure.real, Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  change μ.real {j | decide (j = i) = true} = _
  have he : {j : Fin b | decide (j = i) = true} = {i} := by ext j; simp
  rw [he]
  exact finiteLaw_singleton _ _ _ i

theorem layer_event_probability (b : ℕ) (hb : 1 ≤ b) (i : Fin b)
    (P : Finset V → Prop) :
    (labelLaw b hb).real {ω | P (layer ω i)} =
      (sampleMeasure V (rate b hb)).real {a | P (sampleVertices a)} := by
  rw [← layerMask_map b hb i]
  simp only [Measure.real]
  rw [Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  rfl

theorem layers_disjoint {b : ℕ} (ω : V → Fin b) :
    Pairwise (fun i j => Disjoint (layer ω i) (layer ω j)) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro v hi hj
  exact hij (((mem_layer ω i v).mp hi).symm.trans ((mem_layer ω j v).mp hj))

theorem layers_cover {b : ℕ} (ω : V → Fin b) :
    Finset.univ.biUnion (layer ω) = Finset.univ := by
  ext v
  simp

theorem all_layers_failure_bound (b : ℕ) (hb : 1 ≤ b)
    (P : Fin b → Finset V → Prop) (δ : Fin b → ℝ)
    (hP : ∀ i, (sampleMeasure V (rate b hb)).real
      {a | ¬ P i (sampleVertices a)} ≤ δ i) :
    (labelLaw b hb).real {ω | ∃ i, ¬ P i (layer ω i)} ≤ ∑ i, δ i := by
  have he : {ω | ∃ i, ¬ P i (layer ω i)} = ⋃ i, {ω | ¬ P i (layer ω i)} := by
    ext ω; simp
  rw [he]
  refine (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum ?_)
  intro i _
  rw [layer_event_probability b hb i (fun A => ¬ P i A)]
  exact hP i

theorem exists_all_layers_good (b : ℕ) (hb : 1 ≤ b)
    (P : Fin b → Finset V → Prop) (δ : Fin b → ℝ)
    (hP : ∀ i, (sampleMeasure V (rate b hb)).real
      {a | ¬ P i (sampleVertices a)} ≤ δ i)
    (hsmall : ∑ i, δ i < 1) :
    ∃ ω : V → Fin b, (∀ i, P i (layer ω i)) ∧
      Pairwise (fun i j => Disjoint (layer ω i) (layer ω j)) ∧
      Finset.univ.biUnion (layer ω) = Finset.univ := by
  have hs : ∑ i : Fin b, (labelLaw b hb).real {ω | ¬ P i (layer ω i)} < 1 := by
    refine lt_of_le_of_lt (Finset.sum_le_sum ?_) hsmall
    intro i _
    rw [layer_event_probability b hb i (fun A => ¬ P i A)]
    exact hP i
  obtain ⟨ω, hω⟩ := exists_avoiding_finite_events (μ := labelLaw (V := V) b hb)
    Finset.univ (fun i => {ω | ¬ P i (layer ω i)}) hs
  exact ⟨ω, fun i => not_not.mp (hω i (Finset.mem_univ i)),
    layers_disjoint ω, layers_cover ω⟩

private lemma query_budget (n : ℕ) (hn : 2 ≤ n) (rho : ℝ)
    (hr : 1000000*log (2*n) ≤ rho) :
    2*(n : ℝ)*exp (-rho/100) ≤ 1/(2*(n : ℝ)^4) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl : 0 ≤ log (2*n) := log_nonneg (by linarith)
  have he : 4*(n : ℝ)^5 ≤ exp (rho/100) := by
    calc
      _ ≤ (2*(n : ℝ))^6 := by
        have h := mul_le_mul_of_nonneg_right
          (show (4 : ℝ) ≤ 64*n by linarith) (pow_nonneg hn0.le 5)
        nlinarith only [h]
      _ = exp (6*log (2*n)) := by
        rw [show (6 : ℝ)*log (2*n) = (6 : ℕ)*log (2*n) by norm_num,
          exp_nat_mul, exp_log (by positivity)]
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  rw [show -rho/100 = -(rho/100) by ring, exp_neg]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*(n : ℝ)^4)).mpr
  have hx := exp_pos (rho/100)
  have hi : exp (rho/100)*(exp (rho/100))⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
  have hm := mul_le_mul_of_nonneg_right he (inv_nonneg.mpr hx.le)
  nlinarith only [hm,hi]

/-- Every query is fixed in advance, and all original centers may index queries.
No independence between the query failure events is assumed. -/
theorem fixed_query_failure_bound (p : unitInterval) (d : ℝ)
    (S : I → Finset V) (hn : 2 ≤ Fintype.card V)
    (hI : Fintype.card I ≤ 2*Fintype.card V)
    (hsize : ∀ i, d ≤ ((S i).card : ℝ))
    (hr : 1000000*log (2*Fintype.card V) ≤ (p : ℝ)*d) :
    (sampleMeasure V p).real
      {a | ∃ i, ((S i ∩ sampleVertices a).card : ℝ) < (p : ℝ)*d/2} ≤
      1/(2*(Fintype.card V : ℝ)^4) := by
  let rho := (p : ℝ)*d
  have hnR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hrho : 0 ≤ rho := le_trans
    (mul_nonneg (by norm_num) (log_nonneg (by linarith))) hr
  let E : I → Set (V → Bool) := fun i =>
    {a | ((S i ∩ sampleVertices a).card : ℝ) < rho/2}
  have ht : ∀ i, (sampleMeasure V p).real (E i) ≤ exp (-rho/100) := by
    intro i
    have hmean := mul_le_mul_of_nonneg_left (hsize i) p.property.1
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans
      ((sample_card_lower_tail p (S i)).trans ?_)
    · intro a ha
      change ((S i ∩ sampleVertices a).card : ℝ) < rho/2 at ha
      change ((S i ∩ sampleVertices a).card : ℝ) ≤ (p : ℝ)*(S i).card/2
      dsimp [rho] at ha
      linarith
    · apply exp_le_exp.mpr
      change (p : ℝ)*d ≤ (p : ℝ)*(S i).card at hmean
      dsimp [rho] at hrho ⊢
      linarith
  have he : {a | ∃ i, ((S i ∩ sampleVertices a).card : ℝ) < (p : ℝ)*d/2} =
      ⋃ i, E i := by ext a; simp [E,rho]
  rw [he]
  calc
    _ ≤ ∑ i, (sampleMeasure V p).real (E i) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _i : I, exp (-rho/100) := Finset.sum_le_sum (fun i _ => ht i)
    _ = (Fintype.card I : ℝ)*exp (-rho/100) := by simp
    _ ≤ 2*(Fintype.card V : ℝ)*exp (-rho/100) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hI) (exp_pos _).le
    _ ≤ _ := query_budget (Fintype.card V) hn rho hr

end Erdos642.DenseMask20261019.UniformLayers
