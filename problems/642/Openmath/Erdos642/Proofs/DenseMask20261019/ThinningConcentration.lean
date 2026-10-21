import Openmath.Erdos642.Proofs.DenseMask20261019.ThinningEvent

/-! Actual joint concentration of two fair masks on a fixed finite graph. -/
noncomputable section
namespace Erdos642.DenseMask20261019.ThinningConcentration
open MeasureTheory ProbabilityTheory Finset Real
open OAI.ErdosGallai.Sampling
open Erdos585.Attempt6.SourcePools
open Erdos642.DenseMask20261019.NestedSampling
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma lower_count (U : Finset V) (k : ℝ) (hk : 0 ≤ k)
    (hU : 9*k/10 ≤ (U.card : ℝ)) :
    (sampleMeasure V (mulProbability half half)).real
      {x | ((U ∩ sampleVertices x).card : ℝ) < k/5} ≤ exp (-k/5000) := by
  let p := mulProbability half half
  have hp : (p : ℝ) = 1/4 := by norm_num [p,mulProbability,half]
  have hi := sampleIndicator_indep (V := V) p
  have hInt : Integrable (fun x => exp ((-1/10 : ℝ) *
      (∑ v ∈ U, sampleIndicator v) x)) (sampleMeasure V p) :=
    hi.integrable_exp_mul_sum sampleIndicator_measurable (fun i _ =>
      integrable_exp_mul_of_mem_Icc (sampleIndicator_measurable i).aemeasurable
        (ae_of_all _ (indicator_mem_Icc (sampleIndicator_values i))))
  have hb := measure_le_le_exp_mul_mgf (X := ∑ v ∈ U, sampleIndicator v)
    (k/5) (by norm_num : (-1/10 : ℝ) ≤ 0) hInt
  have hm := mgf_indicator_sum_bound U sampleIndicator_measurable hi
    sampleIndicator_values (p : ℝ) (-1/10) (sampleIndicator_integral p)
  have he : exp (-1/10 : ℝ) ≤ 91/100 := by
    have h := (abs_le.mp (abs_exp_sub_one_sub_id_le
      (by norm_num : |(-1/10 : ℝ)| ≤ 1))).2
    linarith
  have hn := exp_pos (-1/10 : ℝ)
  have hscalar : k/50 + (U.card : ℝ)/4*(exp (-1/10 : ℝ)-1) ≤ -k/5000 := by
    have hmul := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (U.card : ℝ)/4)
    nlinarith
  calc
    _ ≤ (sampleMeasure V p).real {x | (∑ v ∈ U, sampleIndicator v) x ≤ k/5} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro x hx
      change ((U ∩ sampleVertices x).card : ℝ) < k/5 at hx
      change (∑ v ∈ U, sampleIndicator v) x ≤ k/5
      simpa only [Finset.sum_apply, sampleIndicator_sum] using hx.le
    _ ≤ _ := hb
    _ ≤ exp (-(-1/10 : ℝ)*(k/5)) *
        exp ((U.card : ℝ)*(p : ℝ)*(exp (-1/10 : ℝ)-1)) :=
      mul_le_mul_of_nonneg_left hm (exp_pos _).le
    _ ≤ exp (-k/5000) := by
      rw [← exp_add, hp]
      apply exp_le_exp.mpr
      nlinarith [hscalar]

private lemma upper_count (U : Finset V) (k : ℝ) (hk : 0 ≤ k)
    (hU : (U.card : ℝ) ≤ k) :
    (sampleMeasure V half).real
      {x | 9*k/17 < ((U ∩ sampleVertices x).card : ℝ)} ≤ exp (-k/5000) := by
  have hi := sampleIndicator_indep (V := V) half
  have hInt : Integrable (fun x => exp ((1/100 : ℝ) *
      (∑ v ∈ U, sampleIndicator v) x)) (sampleMeasure V half) :=
    hi.integrable_exp_mul_sum sampleIndicator_measurable (fun i _ =>
      integrable_exp_mul_of_mem_Icc (sampleIndicator_measurable i).aemeasurable
        (ae_of_all _ (indicator_mem_Icc (sampleIndicator_values i))))
  have hb := measure_ge_le_exp_mul_mgf (X := ∑ v ∈ U, sampleIndicator v)
    (9*k/17) (by norm_num : (0 : ℝ) ≤ 1/100) hInt
  have hm := mgf_indicator_sum_bound U sampleIndicator_measurable hi
    sampleIndicator_values (half : ℝ) (1/100) (sampleIndicator_integral half)
  have he : exp (1/100 : ℝ) ≤ 10101/10000 := by
    have h := (abs_le.mp (abs_exp_sub_one_sub_id_le
      (by norm_num : |(1/100 : ℝ)| ≤ 1))).2
    linarith
  have hscalar : -(1/100 : ℝ)*(9*k/17) +
      (U.card : ℝ)/2*(exp (1/100 : ℝ)-1) ≤ -k/5000 := by
    have hmul := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (U.card : ℝ)/2)
    nlinarith
  calc
    _ ≤ (sampleMeasure V half).real {x | 9*k/17 ≤ (∑ v ∈ U, sampleIndicator v) x} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro x hx
      change 9*k/17 < ((U ∩ sampleVertices x).card : ℝ) at hx
      change 9*k/17 ≤ (∑ v ∈ U, sampleIndicator v) x
      simpa only [Finset.sum_apply, sampleIndicator_sum] using hx.le
    _ ≤ _ := hb
    _ ≤ exp (-(1/100 : ℝ)*(9*k/17)) *
        exp ((U.card : ℝ)*(half : ℝ)*(exp (1/100 : ℝ)-1)) :=
      mul_le_mul_of_nonneg_left hm (exp_pos _).le
    _ ≤ exp (-k/5000) := by
      rw [← exp_add]
      apply exp_le_exp.mpr
      change -(1/100 : ℝ)*(9*k/17) + (U.card : ℝ)*(1/2)*(exp (1/100 : ℝ)-1) ≤ _
      nlinarith [hscalar]

private lemma degree_tail (S : Finset V) (rho : ℝ)
    (hS : rho/8 ≤ (S.card : ℝ)) :
    (sampleMeasure V (mulProbability half half)).real
      {x | ((S ∩ sampleVertices x).card : ℝ) < rho/64} ≤ exp (-rho/256) := by
  have hp : ((mulProbability half half : unitInterval) : ℝ) = 1/4 := by
    norm_num [mulProbability,half]
  have hh := sample_card_lower_tail (mulProbability half half) S
  rw [hp] at hh
  refine (measureReal_mono (fun x hx => ?_)).trans (hh.trans ?_)
  · change ((S ∩ sampleVertices x).card : ℝ) ≤ 1/4*(S.card : ℝ)/2
    change ((S ∩ sampleVertices x).card : ℝ) < rho/64 at hx
    linarith
  · apply exp_le_exp.mpr
    linarith

private lemma error_budget (n : ℕ) (hn : 1 ≤ n) (rho k : ℝ)
    (hr : 1000000*log (2*n) ≤ rho) (hk : rho/4 ≤ k) :
    2*exp (-k/5000) + n*exp (-rho/256) ≤ 1/2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : (1/2 : ℝ) ≤ log (2*n) := by
    have h2 : (1/2 : ℝ) ≤ log 2 := by
      have h := log_two_gt_d9
      linarith
    exact h2.trans (log_le_log (by norm_num) (by linarith))
  have hcount : exp (-k/5000) ≤ 1/8 := by
    have he : (8 : ℝ) ≤ exp (k/5000) := by
      have h := add_one_le_exp (k/5000)
      linarith
    rw [show -k/5000 = -(k/5000) by ring, exp_neg]
    exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by norm_num; exact he)
  have hdegree : (n : ℝ)*exp (-rho/256) ≤ 1/4 := by
    have hrr : 2*log (2*n) ≤ rho/256 := by linarith
    have he : (2*(n : ℝ))^2 ≤ exp (rho/256) := by
      calc
        _ = exp (2*log (2*n)) := by
          rw [show (2 : ℝ)*log (2*n) = (2 : ℕ)*log (2*n) by norm_num,
            exp_nat_mul, exp_log (by positivity)]
        _ ≤ _ := exp_le_exp.mpr hrr
    rw [show -rho/256 = -(rho/256) by ring, exp_neg]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    have hd := exp_pos (rho/256)
    have hi : exp (rho/256) * (exp (rho/256))⁻¹ = 1 := mul_inv_cancel₀ hd.ne'
    have hm := mul_le_mul_of_nonneg_right he (inv_nonneg.mpr hd.le)
    have hn2 := mul_le_mul_of_nonneg_right
      (show (n : ℝ) ≤ (n : ℝ)^2 by nlinarith) (inv_nonneg.mpr hd.le)
    nlinarith
  linarith

/-- Actual simultaneous count and all-center degree event under two fair masks.
The vertex type is the fixed surviving set W; G has its actual original edges. -/
theorem good_two_mask_probability (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (rho k : ℝ) (hn : 1 ≤ Fintype.card V)
    (hUlo : 9*k/10 ≤ (U.card : ℝ)) (hUhi : (U.card : ℝ) ≤ k)
    (hdeg : ∀ v, rho/8 ≤ (G.degree v : ℝ))
    (hk : rho/4 ≤ k) (hr : 1000000*log (2*Fintype.card V) ≤ rho) :
    1/2 ≤ ((sampleMeasure V half).prod (sampleMeasure V half)).real
      {x | k/5 ≤ ((U ∩ sampleVertices (thin x.1 x.2)).card : ℝ) ∧
        ((U ∩ sampleVertices x.1).card : ℝ) ≤ 9*k/17 ∧
        ∀ v, rho/64 ≤ ((G.neighborFinset v ∩ sampleVertices (thin x.1 x.2)).card : ℝ)} := by
  let μ := (sampleMeasure V half).prod (sampleMeasure V half)
  let B₁ : Set ((V → Bool) × (V → Bool)) :=
    {x | ((U ∩ sampleVertices (thin x.1 x.2)).card : ℝ) < k/5}
  let B₂ : Set ((V → Bool) × (V → Bool)) :=
    {x | 9*k/17 < ((U ∩ sampleVertices x.1).card : ℝ)}
  let B₃ : V → Set ((V → Bool) × (V → Bool)) := fun v =>
    {x | ((G.neighborFinset v ∩ sampleVertices (thin x.1 x.2)).card : ℝ) < rho/64}
  have hk0 : 0 ≤ k := (Nat.cast_nonneg U.card).trans hUhi
  have h₁ : μ.real B₁ ≤ exp (-k/5000) := by
    change ((sampleMeasure V half).prod (sampleMeasure V half)).real
      {x | ((U ∩ sampleVertices (thin x.1 x.2)).card : ℝ) < k/5} ≤ _
    rw [thin_event_probability half half (fun x => ((U ∩ sampleVertices x).card : ℝ) < k/5)]
    exact lower_count U k hk0 hUlo
  have h₂ : μ.real B₂ ≤ exp (-k/5000) := by
    have he : B₂ = {x : V → Bool | 9*k/17 < ((U ∩ sampleVertices x).card : ℝ)} ×ˢ Set.univ := by
      ext x; simp [B₂]
    rw [he]
    change ((sampleMeasure V half).prod (sampleMeasure V half)).real _ ≤ _
    rw [measureReal_prod_prod, probReal_univ, mul_one]
    exact upper_count U k hk0 hUhi
  have h₃ : ∀ v, μ.real (B₃ v) ≤ exp (-rho/256) := by
    intro v
    change ((sampleMeasure V half).prod (sampleMeasure V half)).real
      {x | ((G.neighborFinset v ∩ sampleVertices (thin x.1 x.2)).card : ℝ) < rho/64} ≤ _
    rw [thin_event_probability half half
      (fun x => ((G.neighborFinset v ∩ sampleVertices x).card : ℝ) < rho/64)]
    apply degree_tail
    simpa using hdeg v
  have hbad : μ.real (B₁ ∪ B₂ ∪ ⋃ v, B₃ v) ≤ 1/2 := by
    have hb := measureReal_union_le (μ := μ) (B₁ ∪ B₂) (⋃ v, B₃ v)
    have hb' := measureReal_union_le (μ := μ) B₁ B₂
    have hb'' := measureReal_iUnion_fintype_le (μ := μ) B₃
    have hs : (∑ v, μ.real (B₃ v)) ≤ (Fintype.card V : ℝ)*exp (-rho/256) := by
      calc
        _ ≤ ∑ v : V, exp (-rho/256) := Finset.sum_le_sum (fun v _ => h₃ v)
        _ = _ := by simp
    have he := error_budget (Fintype.card V) hn rho k hr hk
    linarith
  have hc := measureReal_compl (μ := μ) (s := B₁ ∪ B₂ ∪ ⋃ v, B₃ v) MeasurableSet.of_discrete
  rw [probReal_univ] at hc
  have hg : (B₁ ∪ B₂ ∪ ⋃ v, B₃ v)ᶜ =
      {x | k/5 ≤ ((U ∩ sampleVertices (thin x.1 x.2)).card : ℝ) ∧
        ((U ∩ sampleVertices x.1).card : ℝ) ≤ 9*k/17 ∧
        ∀ v, rho/64 ≤ ((G.neighborFinset v ∩ sampleVertices (thin x.1 x.2)).card : ℝ)} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_iUnion, B₁, B₂, B₃,
      Set.mem_setOf_eq, not_or, not_exists, not_lt]
    tauto
  rw [hg] at hc
  change 1/2 ≤ μ.real _
  linarith

end Erdos642.DenseMask20261019.ThinningConcentration
