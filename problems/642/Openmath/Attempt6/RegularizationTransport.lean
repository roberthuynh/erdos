import Openmath.Attempt6.RegularizationIteration

/-! Exact transport from the adaptive regularization coupling to the standard
independent vertex sampler. All graph witnesses remain original subgraphs. -/

noncomputable section

namespace Erdos585.Attempt6.RegularizationTransport

open MeasureTheory ProbabilityTheory Finset Real
open OAI.ErdosGallai.Sampling
open Erdos585.Attempt6.RegularizationIteration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma bool_measure_eq_bernoulli (μ : Measure Bool) [IsProbabilityMeasure μ]
    (p : unitInterval) (hp : μ.real {true} = (p : ℝ)) :
    μ = bernoulliMeasure true false p := by
  apply Measure.ext_of_singleton
  intro b
  have hr : μ.real {b} = (bernoulliMeasure true false p).real {b} := by
    cases b
    · have hc : ({false} : Set Bool) = ({true} : Set Bool)ᶜ := by
        ext b
        cases b <;> simp
      have ht : (bernoulliMeasure true false p).real {true} = (p : ℝ) := by
        simp [bernoulliMeasure_real_apply]
      rw [hc, measureReal_compl MeasurableSet.of_discrete,
        measureReal_compl MeasurableSet.of_discrete, probReal_univ, probReal_univ, hp, ht]
    · simpa [bernoulliMeasure_real_apply] using hp
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {b}),
    ← ENNReal.ofReal_toReal (measure_ne_top (bernoulliMeasure true false p) {b})]
  exact congrArg ENNReal.ofReal hr

                                                                                 
                                                                   
theorem retained_map_eq_sampleMeasure (ν : Measure (State G))
    [IsProbabilityMeasure ν] (p : unitInterval)
    (hi : iIndepSet (fun v : V => {s : State G | s.2 v = true}) ν)
    (hm : ∀ v, ν.real {s : State G | s.2 v = true} = (p : ℝ)) :
    ν.map Prod.snd = sampleMeasure V p := by
  have hf : iIndepFun (fun v : V => fun s : State G => s.2 v) ν := by
    have hh := hi.iIndepFun_indicator (β := Bool) (m := inferInstance)
    have he : (fun v : V => ({s : State G | s.2 v = true}).indicator
        (fun _ => (1 : Bool))) = (fun v : V => fun s : State G => s.2 v) := by
      funext v s
      cases hv : s.2 v <;> simp [hv] <;> rfl
    rwa [he] at hh
  change ν.map (fun s v => s.2 v) = _
  rw [hf.map_fun_eq_pi_map (fun _ => (measurable_of_finite _).aemeasurable)]
  unfold sampleMeasure
  congr 1
  funext v
  haveI : IsProbabilityMeasure (ν.map (fun s : State G => s.2 v)) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable
  apply bool_measure_eq_bernoulli
  rw [Measure.real, Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  exact hm v

/-- An explicit choice of the polynomial retention constant in CJMM Lemma 2.1. -/
def retentionProbability (Λ : ℝ) (hΛ : 1 ≤ Λ) : unitInterval :=
  ⟨1 / (1000000 * Λ ^ 5), by
    have h5 : 1 ≤ Λ ^ 5 := one_le_pow₀ hΛ
    have hC : 1 ≤ 1000000 * Λ ^ 5 := by nlinarith
    have hC0 : 0 < 1000000 * Λ ^ 5 := by linarith
    exact ⟨by positivity, (div_le_one hC0).mpr hC⟩⟩

theorem exists_nearly_regular_bernoulli_coupling (N : ℕ) (Λ d : ℝ)
    (hN : 2 ≤ N) (hcard : Fintype.card V ≤ N) (hΛ : 1 ≤ Λ) (hd : 0 ≤ d)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Λ * d) :
    ∃ ν : Measure (State G), IsProbabilityMeasure ν ∧
      ν.map Prod.snd = sampleMeasure V (retentionProbability Λ hΛ) ∧
      ν.real {s | ¬ NearlyRegularGood G d (1000000 * Λ ^ 5)
        (100000 * Λ ^ 5 * log N) s} ≤ 1 / N := by
  obtain ⟨ν, hν, hi, hm, hf⟩ := exists_nearly_regular_law G N Λ d hN hcard hΛ hd hdeg
  letI := hν
  exact ⟨ν, hν, retained_map_eq_sampleMeasure G ν _ hi hm, hf⟩

/-- The event supplied to later random-pool arguments has no auxiliary law
parameter: it asks for an actual subgraph for the standard Bernoulli sample. -/
def AdmitsNearlyRegular (A : V → Bool) (d C err : ℝ) : Prop :=
  ∃ H : G.Subgraph, NearlyRegularGood G d C err (H, A)

theorem sample_admits_nearly_regular (N : ℕ) (Λ d : ℝ)
    (hN : 2 ≤ N) (hcard : Fintype.card V ≤ N) (hΛ : 1 ≤ Λ) (hd : 0 ≤ d)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Λ * d) :
    (sampleMeasure V (retentionProbability Λ hΛ)).real
      {A | ¬ AdmitsNearlyRegular G A d (1000000 * Λ ^ 5)
        (100000 * Λ ^ 5 * log N)} ≤ 1 / N := by
  obtain ⟨ν, hν, heq, hf⟩ := exists_nearly_regular_bernoulli_coupling G N Λ d
    hN hcard hΛ hd hdeg
  letI := hν
  rw [← heq, Measure.real, Measure.map_apply (measurable_of_finite _)
    MeasurableSet.of_discrete]
  apply le_trans _ hf
  apply measureReal_mono _ (measure_ne_top _ _)
  intro s hs hg
  exact hs ⟨s.1, hg⟩

/-- Finite averaging selects one good state with every conditional failure small.
No independence between the different failure types is needed. -/
theorem exists_good_with_small_failures {S I : Type*} [Fintype S] [Fintype I]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (ν : Measure S) [IsProbabilityMeasure ν] (Good : S → Prop)
    (f : I → S → ℝ) (δ t : I → ℝ) (b : ℝ)
    (hnonneg : ∀ i s, 0 ≤ f i s) (ht : ∀ i, 0 < t i)
    (havg : ∀ i, ∫ s, f i s ∂ν ≤ δ i)
    (hbad : ν.real {s | ¬ Good s} ≤ b)
    (hbudget : b + ∑ i, δ i / t i < 1) :
    ∃ s, Good s ∧ ∀ i, f i s ≤ t i := by
  by_contra h
  have hfail : ∀ s, Good s → ∃ i, t i < f i s := by
    intro s hs
    by_contra hh
    push_neg at hh
    exact h ⟨s, hs, hh⟩
  let X : S → ℝ := {s | ¬ Good s}.indicator (fun _ => 1)
  have hpoint (s : S) : 1 ≤ X s + ∑ i, f i s / t i := by
    have hsum : 0 ≤ ∑ i, f i s / t i :=
      Finset.sum_nonneg (fun i _ => div_nonneg (hnonneg i s) (ht i).le)
    by_cases hs : Good s
    · obtain ⟨i, hi⟩ := hfail s hs
      have hsingle : f i s / t i ≤ ∑ j, f j s / t j :=
        Finset.single_le_sum (fun j _ => div_nonneg (hnonneg j s) (ht j).le)
          (Finset.mem_univ i)
      have hlarge : 1 < f i s / t i := (one_lt_div (ht i)).mpr hi
      have hx : X s = 0 := by simp [X, hs]
      rw [hx]
      linarith
    · have hx : X s = 1 := by simp [X, hs]
      rw [hx]
      linarith
  have hX : ∫ s, X s ∂ν = ν.real {s | ¬ Good s} := by
    exact integral_indicator_one MeasurableSet.of_discrete
  have hsumInt : (∫ s, ∑ i, f i s / t i ∂ν) =
      ∑ i, (∫ s, f i s ∂ν) / t i := by
    rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_div _ _
  have hb : 1 ≤ b + ∑ i, δ i / t i := calc
    1 = ∫ _ : S, (1 : ℝ) ∂ν := by simp
    _ ≤ ∫ s, X s + ∑ i, f i s / t i ∂ν :=
      integral_mono (integrable_const _) Integrable.of_finite hpoint
    _ = ν.real {s | ¬ Good s} + ∑ i, (∫ s, f i s ∂ν) / t i := by
      rw [integral_add Integrable.of_finite Integrable.of_finite, hX, hsumInt]
    _ ≤ b + ∑ i, δ i / t i := add_le_add hbad
      (Finset.sum_le_sum (fun i _ => div_le_div_of_nonneg_right (havg i) (ht i).le))
  linarith

/-- Fubini for the actual independent finite sampling experiment. -/
lemma finite_product_failure {A R : Type*} [Fintype A] [Fintype R]
    [MeasurableSpace A] [MeasurableSpace R]
    [MeasurableSingletonClass A] [MeasurableSingletonClass R]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (ρ : Measure R) [IsProbabilityMeasure ρ] (E : Set (A × R)) :
    (μ.prod ρ).real E = ∫ a, ρ.real {r | (a, r) ∈ E} ∂μ := by
  rw [Measure.real, Measure.prod_apply MeasurableSet.of_discrete]
  exact (integral_toReal (measurable_of_finite _).aemeasurable
    (ae_of_all _ (fun a => measure_lt_top ρ {r | (a, r) ∈ E}))).symm

/-- The averaging step in CJMM Lemma 5.4: a joint graph/subset law with exact
Bernoulli subset marginal, together with independently sampled pool failures,
supplies one good original subgraph and subset with all conditional failures
small. Hypotheses concern unconditional failure in the original experiment. -/
theorem select_good_regularization_and_pools {I R : Type*} [Fintype I] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R]
    (ν : Measure (State G)) [IsProbabilityMeasure ν]
    (p : unitInterval) (hmap : ν.map Prod.snd = sampleMeasure V p)
    (ρ : Measure R) [IsProbabilityMeasure ρ]
    (Good : State G → Prop) (E : I → Set ((V → Bool) × R))
    (δ t : I → ℝ) (b : ℝ) (ht : ∀ i, 0 < t i)
    (hfail : ∀ i, ((sampleMeasure V p).prod ρ).real (E i) ≤ δ i)
    (hbad : ν.real {s | ¬ Good s} ≤ b)
    (hbudget : b + ∑ i, δ i / t i < 1) :
    ∃ s : State G, Good s ∧ ∀ i, ρ.real {r | (s.2, r) ∈ E i} ≤ t i := by
  apply exists_good_with_small_failures ν Good
    (fun i s => ρ.real {r | (s.2, r) ∈ E i}) δ t b
      (fun _ _ => measureReal_nonneg) ht _ hbad hbudget
  intro i
  have havg : (∫ s : State G, ρ.real {r | (s.2, r) ∈ E i} ∂ν) =
      ∫ A : V → Bool, ρ.real {r | (A, r) ∈ E i} ∂sampleMeasure V p := by
    rw [← hmap]
    exact (integral_map (μ := ν)
      (measurable_of_finite (Prod.snd : State G → V → Bool)).aemeasurable
      (measurable_of_finite (fun A : V → Bool =>
        ρ.real {r | (A, r) ∈ E i})).aestronglyMeasurable).symm
  rw [havg, ← finite_product_failure]
  exact hfail i

/-- Fully supplied regularization plus finite pool conditioning. Only the
unconditional pool estimates remain hypotheses; the good graph law is built
by the original-edge iteration, not assumed. -/
theorem exists_regularization_with_small_pool_failures {I R : Type*}
    [Fintype I] [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    (N : ℕ) (Λ d : ℝ) (hN : 2 ≤ N) (hcard : Fintype.card V ≤ N)
    (hΛ : 1 ≤ Λ) (hd : 0 ≤ d)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Λ * d)
    (ρ : Measure R) [IsProbabilityMeasure ρ]
    (E : I → Set ((V → Bool) × R)) (δ t : I → ℝ) (ht : ∀ i, 0 < t i)
    (hfail : ∀ i, ((sampleMeasure V (retentionProbability Λ hΛ)).prod ρ).real (E i) ≤ δ i)
    (hbudget : 1 / (N : ℝ) + ∑ i, δ i / t i < 1) :
    ∃ (H : G.Subgraph) (A : V → Bool),
      NearlyRegularGood G d (1000000 * Λ ^ 5) (100000 * Λ ^ 5 * log N) (H, A) ∧
      ∀ i, ρ.real {r | (A, r) ∈ E i} ≤ t i := by
  obtain ⟨ν, hν, hmap, hbad⟩ := exists_nearly_regular_bernoulli_coupling G N Λ d
    hN hcard hΛ hd hdeg
  letI := hν
  obtain ⟨s, hs, hf⟩ := select_good_regularization_and_pools G ν
    (retentionProbability Λ hΛ) hmap ρ
    (NearlyRegularGood G d (1000000 * Λ ^ 5) (100000 * Λ ^ 5 * log N))
    E δ t (1 / N) ht hfail hbad hbudget
  exact ⟨s.1, s.2, hs, hf⟩

end Erdos585.Attempt6.RegularizationTransport
