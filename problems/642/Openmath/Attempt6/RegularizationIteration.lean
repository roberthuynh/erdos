import Openmath.Attempt6.RegularizationStep

/-!
Adaptive finite iteration of the original-edge CJMM regularization step.
This module keeps the ambient vertex type fixed, including the retained set in
state, so every resulting graph remains a subgraph of the original graph.
-/

noncomputable section

namespace Erdos585.Attempt6.RegularizationIteration

open MeasureTheory ProbabilityTheory Finset Real
open OAI.ErdosGallai.Sampling
open Erdos585.Attempt6.RegularizationStep

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- One step inside an ambient subgraph never reintroduces a deleted vertex. -/
def ambientStep (H : G.Subgraph) (γ d : ℝ) (ω : Coin V → Bool) : G.Subgraph where
  verts := H.verts ∩ retained (lowVertices H.spanningCoe γ d) ω
  Adj := (sampledSubgraph H.spanningCoe (lowVertices H.spanningCoe γ d) ω).Adj
  adj_sub h := H.adj_sub h.1
  edge_vert h := ⟨H.edge_vert h.1,
    (sampledSubgraph H.spanningCoe (lowVertices H.spanningCoe γ d) ω).edge_vert h⟩
  symm := (sampledSubgraph H.spanningCoe (lowVertices H.spanningCoe γ d) ω).symm

lemma ambientStep_le (H : G.Subgraph) (γ d : ℝ) (ω : Coin V → Bool) :
    ambientStep G H γ d ω ≤ H := by
  constructor
  · exact fun _ h => h.1
  · exact fun _ _ h => h.1

lemma ambientStep_spanningCoe (H : G.Subgraph) (γ d : ℝ) (ω : Coin V → Bool) :
    (ambientStep G H γ d ω).spanningCoe =
      (sampledSubgraph H.spanningCoe (lowVertices H.spanningCoe γ d) ω).spanningCoe := rfl

/-- Degree bounds apply only to retained vertices. -/
def DegreeWindow (H : G.Subgraph) (d M : ℝ) : Prop :=
  ∀ v, v ∈ H.verts → d ≤ (H.spanningCoe.degree v : ℝ) ∧
    (H.spanningCoe.degree v : ℝ) ≤ M

/-- The sharp probability estimate remains valid inside any actual original
subgraph; isolated ambient vertices are not erroneously required to have degree d. -/
theorem ambient_step_failure (H : G.Subgraph) (p : unitInterval) (ε γ d : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hγ : 10 * ε ≤ γ) (hd : 0 ≤ d)
    (hp : (p : ℝ) = 1 - ε) (hdeg : DegreeWindow G H d ((1 + γ) * d)) :
    (sampleMeasure (Coin V) p).real
      {ω | ¬ DegreeWindow G (ambientStep G H γ d ω)
        ((1 - 5 * ε / 4) * d)
        ((1 - ε / 2) * (1 + γ) * ((1 - 5 * ε / 4) * d))} ≤
      (Fintype.card V : ℝ) * (2 * exp (-ε * d / 200)) := by
  let E : V → Set (Coin V → Bool) := fun v =>
    {ω | v ∈ H.verts ∧ v ∈ retained (lowVertices H.spanningCoe γ d) ω ∧
      (((ambientStep G H γ d ω).spanningCoe.degree v : ℝ) < (1 - 5 * ε / 4) * d ∨
      (1 - 7 * ε / 4) * ((1 + γ) * d) <
        ((ambientStep G H γ d ω).spanningCoe.degree v : ℝ))}
  have hb (v : V) : (sampleMeasure (Coin V) p).real (E v) ≤ 2 * exp (-ε * d / 200) := by
    by_cases hv : v ∈ H.verts
    · have heq : E v = {ω | v ∈ retained (lowVertices H.spanningCoe γ d) ω ∧
        (((sampledSubgraph H.spanningCoe (lowVertices H.spanningCoe γ d) ω).spanningCoe.degree v : ℝ) <
          (1 - 5 * ε / 4) * d ∨ (1 - 7 * ε / 4) * ((1 + γ) * d) <
        ((sampledSubgraph H.spanningCoe (lowVertices H.spanningCoe γ d) ω).spanningCoe.degree v : ℝ))} := by
        have hdegree (ω : Coin V → Bool) : (ambientStep G H γ d ω).spanningCoe.degree v =
            (sampledSubgraph H.spanningCoe (lowVertices H.spanningCoe γ d) ω).spanningCoe.degree v := by
          unfold SimpleGraph.degree
          congr 1
          ext u
          simp only [SimpleGraph.mem_neighborFinset]
          rfl
        simp only [E, hv, true_and, hdegree]
      rw [heq]
      exact step_vertex_failure_bound H.spanningCoe p v ε γ d hε0 hε1 hγ hd hp (hdeg v hv)
    · have heq : E v = ∅ := by simp [E, hv]
      rw [heq]
      simp only [measureReal_empty]
      positivity
  calc
    _ ≤ (sampleMeasure (Coin V) p).real (⋃ v ∈ (Finset.univ : Finset V), E v) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      simp only [Set.mem_ofPred_eq, DegreeWindow, not_forall, not_and_or, not_le] at hω
      obtain ⟨v, hv, hbad⟩ := hω
      have hvH : v ∈ H.verts := hv.1
      have hvR : v ∈ retained (lowVertices H.spanningCoe γ d) ω := hv.2
      have hvE : ω ∈ E v := by
        refine ⟨hvH, hvR, ?_⟩
        rcases hbad with h | h
        · exact Or.inl h
        · exact Or.inr (lt_of_le_of_lt
            (degree_window_improves_ratio ε γ d hε0 (by linarith) hd).2.2 h)
      exact Set.mem_iUnion_of_mem v (Set.mem_iUnion_of_mem (Finset.mem_univ v) hvE)
    _ ≤ ∑ v ∈ (Finset.univ : Finset V), (sampleMeasure (Coin V) p).real (E v) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ (Finset.univ : Finset V), 2 * exp (-ε * d / 200) :=
      Finset.sum_le_sum (fun v _ => hb v)
    _ = _ := by simp


/-- Finite adaptive state: an original subgraph together with the thinned subset. -/
abbrev State := G.Subgraph × (V → Bool)

instance stateFintype : Fintype (State G) := inferInstanceAs (Fintype (G.Subgraph × (V → Bool)))
instance stateMeasurable : MeasurableSpace (State G) := ⊤
instance stateMeasurableSingleton : MeasurableSingletonClass (State G) := ⟨fun _ => trivial⟩

def transition (γ d : ℝ) (s : State G) (ω : Coin V → Bool) : State G :=
  (ambientStep G s.1 γ d ω, fun v => s.2 v && ω (Sum.inl v))

def transitionLaw (p : unitInterval) (γ d : ℝ) (s : State G) : Measure (State G) :=
  (sampleMeasure (Coin V) p).map (transition G γ d s)

instance transitionLaw_probability (p : unitInterval) (γ d : ℝ) (s : State G) :
    IsProbabilityMeasure (transitionLaw G p γ d s) := by
  unfold transitionLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

/-- Real probabilities of a finite adaptive mixture are actual integrals. -/
lemma finite_bind_real {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : S → Measure S)
    [∀ s, IsProbabilityMeasure (K s)] (E : Set S) :
    (μ.bind K).real E = ∫ s, (K s).real E ∂μ := by
  rw [Measure.real, Measure.bind_apply MeasurableSet.of_discrete
    (measurable_of_finite K).aemeasurable]
  exact (integral_toReal (measurable_of_finite _).aemeasurable
    (ae_of_all _ (fun s => measure_lt_top (K s) E))).symm

lemma finite_bind_probability {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : S → Measure S)
    [∀ s, IsProbabilityMeasure (K s)] : IsProbabilityMeasure (μ.bind K) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ (measurable_of_finite K).aemeasurable]
  simp

/-- General adaptive failure accumulation: a bad prior state costs its whole
probability, while every good prior state pays at most q in the next transition. -/
theorem adaptive_failure_bound {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (μ : Measure S) [IsProbabilityMeasure μ]
    (K : S → Measure S) [∀ s, IsProbabilityMeasure (K s)]
    (P Q : S → Prop) (q : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ s, P s → (K s).real {s | ¬ Q s} ≤ q) :
    (μ.bind K).real {s | ¬ Q s} ≤ μ.real {s | ¬ P s} + q := by
  rw [finite_bind_real]
  let X : S → ℝ := fun s => if P s then 0 else 1
  have hpoint (s : S) : (K s).real {s | ¬ Q s} ≤ X s + q := by
    by_cases hs : P s
    · simpa [X, hs] using hstep s hs
    · have hh : (K s).real {s | ¬ Q s} ≤ 1 := by
        calc
          _ ≤ (K s).real Set.univ := measureReal_mono (Set.subset_univ _)
          _ = 1 := probReal_univ
      simp only [X, hs, ↓reduceIte]
      linarith
  have hX : ∫ s, X s ∂μ = μ.real {s | ¬ P s} := by
    have hx : X = {s | ¬ P s}.indicator (fun _ => (1 : ℝ)) := by
      funext s
      by_cases hs : P s <;> simp [X, hs]
    rw [hx, integral_indicator_const _ MeasurableSet.of_discrete]
    simp
  calc
    _ ≤ ∫ s, (X s + q) ∂μ := integral_mono Integrable.of_finite Integrable.of_finite hpoint
    _ = _ := by rw [integral_add Integrable.of_finite (integrable_const _), hX]; simp

def degreeScale (ε d : ℝ) (i : ℕ) : ℝ := (1 - 5 * ε / 4) ^ i * d
def ratioScale (ε Λ : ℝ) (i : ℕ) : ℝ := Λ * (1 - ε / 2) ^ i

/-- Explicit finite adaptive Markov law, with fresh independent coins at every
transition. The initial retained set is the whole original vertex set. -/
def iterationLaw (p : unitInterval) (ε Λ d : ℝ) : ℕ → Measure (State G)
  | 0 => Measure.dirac ((⊤ : G.Subgraph), fun _ => true)
  | i + 1 => (iterationLaw p ε Λ d i).bind
      (transitionLaw G p (ratioScale ε Λ i - 1) (degreeScale ε d i))

instance iterationLaw_probability (p : unitInterval) (ε Λ d : ℝ) (i : ℕ) :
    IsProbabilityMeasure (iterationLaw G p ε Λ d i) := by
  induction i with
  | zero =>
    constructor
    exact Measure.dirac_apply_of_mem (Set.mem_univ _)
  | succ i ih =>
    letI := ih
    exact finite_bind_probability _ _

def GoodState (ε Λ d : ℝ) (i : ℕ) (s : State G) : Prop :=
  (∀ v, s.2 v = true → v ∈ s.1.verts) ∧
    DegreeWindow G s.1 (degreeScale ε d i) (ratioScale ε Λ i * degreeScale ε d i)

lemma transition_preserves_containment (γ d : ℝ) (s : State G) (ω : Coin V → Bool)
    (h : ∀ v, s.2 v = true → v ∈ s.1.verts) :
    ∀ v, (transition G γ d s ω).2 v = true →
      v ∈ (transition G γ d s ω).1.verts := by
  intro v hv
  have hvb : s.2 v = true ∧ ω (Sum.inl v) = true := by
    simpa [transition] using hv
  exact ⟨h v hvb.1, Or.inr hvb.2⟩

theorem transition_failure_bound (p : unitInterval) (n ε Λ d : ℝ) (i : ℕ)
    (hn : 2 ≤ n) (hcard : (Fintype.card V : ℝ) ≤ n)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hd : 0 ≤ d)
    (hp : (p : ℝ) = 1 - ε)
    (hgap : 10 * ε ≤ ratioScale ε Λ i - 1)
    (hlog : 10000 * log n ≤ ε * degreeScale ε d i)
    (s : State G) (hs : GoodState G ε Λ d i s) :
    (transitionLaw G p (ratioScale ε Λ i - 1) (degreeScale ε d i) s).real
      {s | ¬ GoodState G ε Λ d (i + 1) s} ≤ 1 / n ^ 2 := by
  have hdi : 0 ≤ degreeScale ε d i := by
    unfold degreeScale
    exact mul_nonneg (pow_nonneg (by linarith) _) hd
  have hdeg : DegreeWindow G s.1 (degreeScale ε d i)
      ((1 + (ratioScale ε Λ i - 1)) * degreeScale ε d i) := by
    simpa using hs.2
  have hb := ambient_step_failure G s.1 p ε (ratioScale ε Λ i - 1)
    (degreeScale ε d i) hε0 hε1 hgap hdi hp hdeg
  have hscale : degreeScale ε d (i + 1) = (1 - 5 * ε / 4) * degreeScale ε d i := by
    unfold degreeScale
    rw [pow_succ]
    ring
  have hratio : ratioScale ε Λ (i + 1) = (1 - ε / 2) * ratioScale ε Λ i := by
    unfold ratioScale
    rw [pow_succ]
    ring
  have hmap : (transitionLaw G p (ratioScale ε Λ i - 1) (degreeScale ε d i) s).real
      {s | ¬ GoodState G ε Λ d (i + 1) s} =
      (sampleMeasure (Coin V) p).real
      {ω | ¬ GoodState G ε Λ d (i + 1)
        (transition G (ratioScale ε Λ i - 1) (degreeScale ε d i) s ω)} := by
    rw [transitionLaw, Measure.real, Measure.map_apply (measurable_of_finite _)
      MeasurableSet.of_discrete]
    rfl
  rw [hmap]
  apply le_trans _ ((hb.trans (mul_le_mul_of_nonneg_right hcard (by positivity))).trans
    (exponential_budget_le_inverse_square n ε (degreeScale ε d i) hn hlog))
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hbad hgood
  apply hbad
  refine ⟨transition_preserves_containment G _ _ s ω hs.1, ?_⟩
  change DegreeWindow G (ambientStep G s.1 _ _ ω) _ _
  rw [hscale, hratio]
  convert hgood using 1 <;> ring

/-- Closed finite-step degree bounds under the actual adaptive law. The theorem
assumes only numerical validity of each step, not existence of any final graph. -/
theorem iteration_failure_bound (p : unitInterval) (n ε Λ d : ℝ) (k : ℕ)
    (hn : 2 ≤ n) (hcard : (Fintype.card V : ℝ) ≤ n)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hd : 0 ≤ d)
    (hp : (p : ℝ) = 1 - ε)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Λ * d)
    (hgap : ∀ i < k, 10 * ε ≤ ratioScale ε Λ i - 1)
    (hlog : ∀ i < k, 10000 * log n ≤ ε * degreeScale ε d i) :
    (iterationLaw G p ε Λ d k).real {s | ¬ GoodState G ε Λ d k s} ≤ k / n ^ 2 := by
  induction k with
  | zero =>
    have hgood : GoodState G ε Λ d 0 ((⊤ : G.Subgraph), fun _ => true) := by
      constructor
      · simp
      · intro v hv
        have heq : (⊤ : G.Subgraph).spanningCoe.degree v = G.degree v := by
          unfold SimpleGraph.degree
          congr 1
          ext u
          simp only [SimpleGraph.mem_neighborFinset]
          rfl
        simpa only [degreeScale, ratioScale, pow_zero, mul_one, one_mul, heq] using hdeg v
    rw [iterationLaw, Measure.real, @Measure.dirac_apply (State G) _ _]
    simp [hgood]
  | succ k ih =>
    have hprev := ih (fun i hi => hgap i (by omega)) (fun i hi => hlog i (by omega))
    have hstep := adaptive_failure_bound (iterationLaw G p ε Λ d k)
      (transitionLaw G p (ratioScale ε Λ k - 1) (degreeScale ε d k))
      (GoodState G ε Λ d k) (GoodState G ε Λ d (k + 1)) (1 / n ^ 2) (by positivity)
      (fun s hs => transition_failure_bound G p n ε Λ d k hn hcard hε0 hε1 hd hp
        (hgap k (by omega)) (hlog k (by omega)) s hs)
    change ((iterationLaw G p ε Λ d k).bind _).real _ ≤ _
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ (iterationLaw G p ε Λ d k).real {s | ¬ GoodState G ε Λ d k s} + 1 / n ^ 2 := hstep
      _ ≤ (k : ℝ) / n ^ 2 + 1 / n ^ 2 := add_le_add hprev le_rfl
      _ = _ := by ring

def Contains (S : Finset V) (s : State G) : Prop := ∀ v ∈ S, s.2 v = true

lemma transition_contains_probability (p : unitInterval) (γ d : ℝ)
    (s : State G) (S : Finset V) :
    (transitionLaw G p γ d s).real {s | Contains G S s} =
      if Contains G S s then (p : ℝ) ^ S.card else 0 := by
  have hmap : (transitionLaw G p γ d s).real {s | Contains G S s} =
      (sampleMeasure (Coin V) p).real {ω | Contains G S (transition G γ d s ω)} := by
    rw [transitionLaw, Measure.real, Measure.map_apply (measurable_of_finite _)
      MeasurableSet.of_discrete]
    rfl
  rw [hmap]
  by_cases hs : Contains G S s
  · rw [if_pos hs]
    have heq : {ω | Contains G S (transition G γ d s ω)} =
        {ω | ∀ v ∈ S, ω (Sum.inl v) = true} := by
      ext ω
      simp only [Contains, transition, Bool.and_eq_true, Set.mem_ofPred_eq]
      constructor
      · exact fun h v hv => (h v hv).2
      · exact fun h v hv => ⟨hs v hv, h v hv⟩
    rw [heq]
    exact coupled_vertex_contains_probability p S
  · rw [if_neg hs]
    have heq : {ω | Contains G S (transition G γ d s ω)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      apply hs
      intro v hv
      exact (Bool.and_eq_true_iff.mp (h v hv)).1
    rw [heq, measureReal_empty]

/-- Exact retained-set moments under the actual adaptive graph distribution.
No independence between the current graph and its retained set is assumed. -/
theorem iteration_contains_probability (p : unitInterval) (ε Λ d : ℝ)
    (k : ℕ) (S : Finset V) :
    (iterationLaw G p ε Λ d k).real {s | Contains G S s} =
      ((p : ℝ) ^ k) ^ S.card := by
  induction k with
  | zero =>
    rw [iterationLaw, Measure.real, Measure.dirac_apply_of_mem (by simp [Contains])]
    simp
  | succ k ih =>
    change ((iterationLaw G p ε Λ d k).bind _).real _ = _
    rw [finite_bind_real]
    simp_rw [transition_contains_probability]
    have heq : (fun s : State G => if Contains G S s then (p : ℝ) ^ S.card else 0) =
        {s | Contains G S s}.indicator (fun _ => (p : ℝ) ^ S.card) := by
      funext s
      simp [Set.indicator_apply]
    rw [heq, integral_indicator_const _ MeasurableSet.of_discrete]
    simp only [smul_eq_mul, ih, pow_succ, mul_pow]

lemma iteration_contains_measure (p : unitInterval) (ε Λ d : ℝ)
    (k : ℕ) (S : Finset V) :
    (iterationLaw G p ε Λ d k) {s | Contains G S s} =
      ENNReal.ofReal (((p : ℝ) ^ k) ^ S.card) := by
  rw [← iteration_contains_probability G p ε Λ d k S, Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The retained set is iid with inclusion density p^k, even though graph
choices adapt to all previous outcomes. -/
theorem iteration_vertices_independent (p : unitInterval) (ε Λ d : ℝ) (k : ℕ) :
    iIndepSet (fun v : V => {s : State G | s.2 v = true})
      (iterationLaw G p ε Λ d k) := by
  rw [iIndepSet_iff_meas_biInter (fun _ => MeasurableSet.of_discrete)]
  intro S
  have heq : (⋂ v ∈ S, {s : State G | s.2 v = true}) = {s | Contains G S s} := by
    ext s
    simp [Contains]
  rw [heq, iteration_contains_measure]
  have hsingle (v : V) :
      (iterationLaw G p ε Λ d k) {s : State G | s.2 v = true} =
        ENNReal.ofReal ((p : ℝ) ^ k) := by
    simpa [Contains] using iteration_contains_measure G p ε Λ d k {v}
  simp_rw [hsingle]
  simp [ENNReal.ofReal_pow, pow_nonneg p.property.1]

lemma contraction_fifth_power (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) :
    (1 - ε / 2) ^ 5 ≤ 1 - 2 * ε := by
  have h2 := mul_le_mul_of_nonneg_right hε1 hε0
  have h3 := mul_nonneg hε0 (sq_nonneg ε)
  have h4 := mul_le_mul_of_nonneg_right hε1 h3
  have h5 := mul_nonneg hε0 (sq_nonneg (ε ^ 2))
  nlinarith [sq_nonneg ε]

/-- Closed lower bounds for the actual degree scale and iid retention density. -/
theorem scales_bounded_below (ε Λ d : ℝ) (k : ℕ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hΛ : 1 ≤ Λ) (hd : 0 ≤ d)
    (hstop : 1 ≤ ratioScale ε Λ k) :
    d / Λ ^ 5 ≤ degreeScale ε d k ∧ degreeScale ε d k ≤ d ∧
      1 / Λ ^ 5 ≤ (1 - ε) ^ k := by
  have hΛ0 : 0 < Λ := by linarith
  have hr0 : 0 ≤ 1 - ε / 2 := by linarith
  have ha0 : 0 ≤ 1 - 5 * ε / 4 := by linarith
  have hr : 1 / Λ ≤ (1 - ε / 2) ^ k := by
    apply (div_le_iff₀ hΛ0).mpr
    simpa [ratioScale, mul_comm] using hstop
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / Λ) hr 5
  have hbase := contraction_fifth_power ε hε0 hε1
  have hdegpow : ((1 - ε / 2) ^ 5) ^ k ≤ (1 - 5 * ε / 4) ^ k :=
    pow_le_pow_left₀ (pow_nonneg hr0 _) (by linarith) k
  have hretainpow : ((1 - ε / 2) ^ 5) ^ k ≤ (1 - ε) ^ k :=
    pow_le_pow_left₀ (pow_nonneg hr0 _) (by linarith) k
  have hpowers : ((1 - ε / 2) ^ k) ^ 5 = ((1 - ε / 2) ^ 5) ^ k := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hpowers] at hpow
  have hlow : 1 / Λ ^ 5 ≤ (1 - 5 * ε / 4) ^ k := by
    simpa only [div_pow, one_pow, hpowers] using hpow.trans hdegpow
  refine ⟨?_, ?_, ?_⟩
  · unfold degreeScale
    have h := mul_le_mul_of_nonneg_right hlow hd
    simpa only [div_mul_eq_mul_div, one_mul] using h
  · unfold degreeScale
    exact mul_le_of_le_one_left hd (pow_le_one₀ ha0 (by linarith))
  · simpa only [div_pow, one_pow, hpowers] using hpow.trans hretainpow

/-- Existence of a finite first stopping index, with all prior steps valid for
the ratio hypothesis. The logarithmic degree hypothesis is handled separately. -/
theorem exists_stopping_index (ε Λ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 100)
    (hΛ : 1 ≤ Λ) :
    ∃ k : ℕ, 1 ≤ ratioScale ε Λ k ∧ ratioScale ε Λ k ≤ 1 + 10 * ε ∧
      ∀ i < k, 10 * ε ≤ ratioScale ε Λ i - 1 := by
  have hΛ0 : 0 < Λ := by linarith
  have hex : ∃ k : ℕ, ratioScale ε Λ k ≤ 1 + 10 * ε := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
      (show 0 < (1 + 10 * ε) / Λ by positivity)
      (show 1 - ε / 2 < 1 by linarith)
    refine ⟨k, ?_⟩
    unfold ratioScale
    have hh := (lt_div_iff₀ hΛ0).mp hk
    nlinarith
  let k := Nat.find hex
  have hupper : ratioScale ε Λ k ≤ 1 + 10 * ε := Nat.find_spec hex
  have hprior : ∀ i < k, 10 * ε ≤ ratioScale ε Λ i - 1 := by
    intro i hi
    have hh := Nat.find_min hex hi
    linarith
  refine ⟨k, ?_, hupper, hprior⟩
  cases hk : k with
  | zero => simpa [ratioScale, hk] using hΛ
  | succ j =>
    have hp := hprior j (by omega)
    have hs : ratioScale ε Λ k = (1 - ε / 2) * ratioScale ε Λ j := by
      rw [hk]
      unfold ratioScale
      rw [pow_succ]
      ring
    have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1 - ε / 2 by linarith)
    rw [hk] at hs
    rw [hs]
    nlinarith

/-- A final independent thinning changes only A and leaves the graph fixed. -/
def thinState (s : State G) (ω : V → Bool) : State G :=
  (s.1, fun v => s.2 v && ω v)

def thinKernel (q : unitInterval) (s : State G) : Measure (State G) :=
  (sampleMeasure V q).map (thinState G s)

instance thinKernel_probability (q : unitInterval) (s : State G) :
    IsProbabilityMeasure (thinKernel G q s) := by
  unfold thinKernel
  exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

def thinnedLaw (p q : unitInterval) (ε Λ d : ℝ) (k : ℕ) : Measure (State G) :=
  (iterationLaw G p ε Λ d k).bind (thinKernel G q)

instance thinnedLaw_probability (p q : unitInterval) (ε Λ d : ℝ) (k : ℕ) :
    IsProbabilityMeasure (thinnedLaw G p q ε Λ d k) := finite_bind_probability _ _

lemma thin_contains_probability (q : unitInterval) (s : State G) (S : Finset V) :
    (thinKernel G q s).real {s | Contains G S s} =
      if Contains G S s then (q : ℝ) ^ S.card else 0 := by
  have hmap : (thinKernel G q s).real {s | Contains G S s} =
      (sampleMeasure V q).real {ω | Contains G S (thinState G s ω)} := by
    rw [thinKernel, Measure.real, Measure.map_apply (measurable_of_finite _)
      MeasurableSet.of_discrete]
    rfl
  rw [hmap]
  by_cases hs : Contains G S s
  · rw [if_pos hs]
    have heq : {ω | Contains G S (thinState G s ω)} = {ω | S ⊆ sampleVertices ω} := by
      ext ω
      simp only [Contains, thinState, Bool.and_eq_true, Set.mem_ofPred_eq]
      simp only [Finset.subset_iff, sampleVertices, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · exact fun h v hv => (h v hv).2
      · exact fun h v hv => ⟨hs v hv, h hv⟩
    rw [heq, sample_contains_real_probability]
  · rw [if_neg hs]
    have heq : {ω | Contains G S (thinState G s ω)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hs (fun v hv => (Bool.and_eq_true_iff.mp (h v hv)).1)
    rw [heq, measureReal_empty]

theorem thinned_contains_probability (p q : unitInterval) (ε Λ d : ℝ)
    (k : ℕ) (S : Finset V) :
    (thinnedLaw G p q ε Λ d k).real {s | Contains G S s} =
      ((p : ℝ) ^ k * (q : ℝ)) ^ S.card := by
  rw [thinnedLaw, finite_bind_real]
  simp_rw [thin_contains_probability]
  have heq : (fun s : State G => if Contains G S s then (q : ℝ) ^ S.card else 0) =
      {s | Contains G S s}.indicator (fun _ => (q : ℝ) ^ S.card) := by
    funext s
    simp [Set.indicator_apply]
  rw [heq, integral_indicator_const _ MeasurableSet.of_discrete]
  simp only [smul_eq_mul, iteration_contains_probability, mul_pow]

theorem thinned_vertices_independent (p q : unitInterval) (ε Λ d : ℝ) (k : ℕ) :
    iIndepSet (fun v : V => {s : State G | s.2 v = true})
      (thinnedLaw G p q ε Λ d k) := by
  have hm (S : Finset V) : (thinnedLaw G p q ε Λ d k) {s | Contains G S s} =
      ENNReal.ofReal (((p : ℝ) ^ k * (q : ℝ)) ^ S.card) := by
    rw [← thinned_contains_probability G p q ε Λ d k S, Measure.real,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [iIndepSet_iff_meas_biInter (fun _ => MeasurableSet.of_discrete)]
  intro S
  have heq : (⋂ v ∈ S, {s : State G | s.2 v = true}) = {s | Contains G S s} := by
    ext s
    simp [Contains]
  rw [heq, hm]
  have hsingle (v : V) : (thinnedLaw G p q ε Λ d k) {s : State G | s.2 v = true} =
      ENNReal.ofReal ((p : ℝ) ^ k * (q : ℝ)) := by
    simpa [Contains] using hm {v}
  simp_rw [hsingle]
  simp [ENNReal.ofReal_pow (mul_nonneg (pow_nonneg p.property.1 _) q.property.1)]

def AdditiveGood (d C err : ℝ) (s : State G) : Prop :=
  (∀ v, s.2 v = true → v ∈ s.1.verts) ∧
    ∃ d₁ : ℝ, d / C ≤ d₁ ∧ d₁ ≤ d ∧ DegreeWindow G s.1 d₁ (d₁ + err)

theorem goodState_additive (ε Λ d C err : ℝ) (k : ℕ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hΛ : 1 ≤ Λ) (hd : 0 ≤ d)
    (hC : Λ ^ 5 ≤ C) (hstop0 : 1 ≤ ratioScale ε Λ k)
    (hstop1 : ratioScale ε Λ k ≤ 1 + 10 * ε) (herr : 10 * ε * d ≤ err)
    (s : State G) (hs : GoodState G ε Λ d k s) : AdditiveGood G d C err s := by
  have hΛ0 : 0 < Λ := by linarith
  have hC0 : 0 < C := lt_of_lt_of_le (pow_pos hΛ0 5) hC
  have hsc := scales_bounded_below ε Λ d k hε0 hε1 hΛ hd hstop0
  have hdi : 0 ≤ degreeScale ε d k :=
    (div_nonneg hd (pow_nonneg hΛ0.le 5)).trans hsc.1
  refine ⟨hs.1, degreeScale ε d k, ?_, hsc.2.1, ?_⟩
  · exact (div_le_div_of_nonneg_left hd (pow_pos hΛ0 5) hC).trans hsc.1
  · intro v hv
    refine ⟨(hs.2 v hv).1, ?_⟩
    have hu := (hs.2 v hv).2
    have hmul := mul_le_mul_of_nonneg_right hstop1 hdi
    have herror := mul_le_mul_of_nonneg_left hsc.2.1 (show 0 ≤ 10 * ε by positivity)
    linarith

lemma thin_preserves_additive (d C err : ℝ) (s : State G) (ω : V → Bool)
    (hs : AdditiveGood G d C err s) : AdditiveGood G d C err (thinState G s ω) := by
  refine ⟨?_, hs.2⟩
  intro v hv
  exact hs.1 v (Bool.and_eq_true_iff.mp hv).1

theorem thinned_additive_failure_bound (p q : unitInterval) (n ε Λ d C err : ℝ) (k : ℕ)
    (hn : 2 ≤ n) (hcard : (Fintype.card V : ℝ) ≤ n)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hΛ : 1 ≤ Λ) (hd : 0 ≤ d)
    (hp : (p : ℝ) = 1 - ε) (hC : Λ ^ 5 ≤ C)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Λ * d)
    (hgap : ∀ i < k, 10 * ε ≤ ratioScale ε Λ i - 1)
    (hlog : ∀ i < k, 10000 * log n ≤ ε * degreeScale ε d i)
    (hstop0 : 1 ≤ ratioScale ε Λ k) (hstop1 : ratioScale ε Λ k ≤ 1 + 10 * ε)
    (herr : 10 * ε * d ≤ err) :
    (thinnedLaw G p q ε Λ d k).real {s | ¬ AdditiveGood G d C err s} ≤ k / n ^ 2 := by
  have hi := iteration_failure_bound G p n ε Λ d k hn hcard hε0 hε1 hd hp hdeg hgap hlog
  have ha := adaptive_failure_bound (iterationLaw G p ε Λ d k) (thinKernel G q)
    (GoodState G ε Λ d k) (AdditiveGood G d C err) 0 (by norm_num) (fun s hs => ?_)
  · exact (ha.trans (by simpa using hi))
  · have hgood := goodState_additive G ε Λ d C err k hε0 hε1 hΛ hd hC hstop0 hstop1 herr s hs
    have hmap : (thinKernel G q s).real {s | ¬ AdditiveGood G d C err s} =
        (sampleMeasure V q).real {ω | ¬ AdditiveGood G d C err (thinState G s ω)} := by
      rw [thinKernel, Measure.real, Measure.map_apply (measurable_of_finite _)
        MeasurableSet.of_discrete]
      rfl
    rw [hmap]
    have heq : {ω | ¬ AdditiveGood G d C err (thinState G s ω)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact thin_preserves_additive G d C err s ω hgood
    rw [heq, measureReal_empty]

lemma ratio_at_order_le_one (N : ℕ) (ε Λ d : ℝ)
    (hN : 2 ≤ N) (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hΛ : 1 ≤ Λ)
    (hdN : d ≤ (N : ℝ)) (hlog : 10000 * Λ ^ 5 * log N ≤ ε * d) :
    ratioScale ε Λ N ≤ 1 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hΛ0 : 0 < Λ := by linarith
  have hlogN : (1 / 2 : ℝ) ≤ log N := by
    have hl := log_le_log (by norm_num : (0 : ℝ) < 2) hNr
    linarith [log_two_gt_d9]
  have hΛpow : Λ ≤ Λ ^ 5 := by
    simpa using pow_le_pow_right₀ hΛ (show 1 ≤ 5 by norm_num)
  have hlarge := mul_le_mul_of_nonneg_left hlogN
    (show 0 ≤ 10000 * Λ ^ 5 by positivity)
  have heN := mul_le_mul_of_nonneg_left hdN hε
  have hlogΛ := log_le_sub_one_of_pos hΛ0
  have he : log Λ - ε * N / 2 ≤ 0 := by nlinarith
  have hp := pow_le_pow_left₀ (show 0 ≤ 1 - ε / 2 by linarith)
    (one_sub_le_exp_neg (ε / 2)) N
  have heq : exp (-(ε / 2)) ^ N = exp (-ε * N / 2) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  unfold ratioScale
  calc
    Λ * (1 - ε / 2) ^ N ≤ Λ * exp (-ε * N / 2) :=
      mul_le_mul_of_nonneg_left (hp.trans_eq heq) hΛ0.le
    _ = exp (log Λ - ε * N / 2) := by
      rw [exp_sub, exp_log hΛ0, show -ε * N / 2 = -(ε * N / 2) by ring, exp_neg]
      ring
    _ ≤ 1 := by simpa using exp_le_exp.mpr he

theorem exists_stopping_index_bounded (N : ℕ) (ε Λ d : ℝ)
    (hN : 2 ≤ N) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100) (hΛ : 1 ≤ Λ)
    (hdN : d ≤ (N : ℝ)) (hlog : 10000 * Λ ^ 5 * log N ≤ ε * d) :
    ∃ k : ℕ, k ≤ N ∧ 1 ≤ ratioScale ε Λ k ∧ ratioScale ε Λ k ≤ 1 + 10 * ε ∧
      ∀ i < k, 10 * ε ≤ ratioScale ε Λ i - 1 := by
  obtain ⟨k, hk0, hk1, hprior⟩ := exists_stopping_index ε Λ hε hε1 hΛ
  refine ⟨k, ?_, hk0, hk1, hprior⟩
  by_contra hnk
  have hp := hprior N (by omega)
  have hb := ratio_at_order_le_one N ε Λ d hN hε.le hε1 hΛ hdN hlog
  linarith

lemma choose_final_thinning (p : unitInterval) (C : ℝ) (k : ℕ) (hC : 0 < C)
    (hret : 1 / C ≤ (p : ℝ) ^ k) :
    ∃ q : unitInterval, (p : ℝ) ^ k * (q : ℝ) = 1 / C := by
  have hpk : 0 < (p : ℝ) ^ k := lt_of_lt_of_le (by positivity) hret
  refine ⟨⟨(1 / C) / (p : ℝ) ^ k, ?_, ?_⟩, ?_⟩
  · positivity
  · exact (div_le_one hpk).mpr hret
  · dsimp
    field_simp

/-- Actual additive original-edge regularization with an iid retained subset of
the requested density. This is the large-degree branch with explicit constants;
the measure is constructed by finite adaptive iteration and independent thinning. -/
theorem exists_additive_regularization_law [Nonempty V] (N : ℕ) (Λ d C : ℝ)
    (hN : 2 ≤ N) (hcard : Fintype.card V ≤ N) (hΛ : 1 ≤ Λ) (hd : 0 < d)
    (hlarge : 1000000 * Λ ^ 5 * log N ≤ d) (hC : Λ ^ 5 ≤ C)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Λ * d) :
    ∃ ν : Measure (State G), IsProbabilityMeasure ν ∧
      iIndepSet (fun v : V => {s : State G | s.2 v = true}) ν ∧
      (∀ v, ν.real {s : State G | s.2 v = true} = 1 / C) ∧
      ν.real {s | ¬ AdditiveGood G d C (100000 * Λ ^ 5 * log N) s} ≤ 1 / N := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hC0 : 0 < C := lt_of_lt_of_le (pow_pos hΛ0 5) hC
  have hlogN : 0 < log N := log_pos (by linarith)
  let ε : ℝ := 10000 * Λ ^ 5 * log N / d
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 / 100 := by
    dsimp [ε]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hεd : ε * d = 10000 * Λ ^ 5 * log N := by
    dsimp [ε]
    field_simp
  let p : unitInterval := ⟨1 - ε, by constructor <;> linarith⟩
  have hp : (p : ℝ) = 1 - ε := rfl
  have hdN : d ≤ (N : ℝ) := by
    obtain ⟨v⟩ := ‹Nonempty V›
    have hcardv : G.degree v < Fintype.card V := G.degree_lt_card_verts v
    have hDN : G.degree v ≤ N := by omega
    have hDNreal : (G.degree v : ℝ) ≤ N := by exact_mod_cast hDN
    exact (hdeg v).1.trans hDNreal
  obtain ⟨k, hkN, hk0, hk1, hprior⟩ := exists_stopping_index_bounded N ε Λ d
    hN hε0 hε1 hΛ hdN hεd.symm.le
  have hret : 1 / C ≤ (p : ℝ) ^ k := by
    rw [hp]
    exact (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (pow_pos hΛ0 5) hC).trans
      (scales_bounded_below ε Λ d k hε0.le hε1 hΛ hd.le hk0).2.2
  obtain ⟨q, hq⟩ := choose_final_thinning p C k hC0 hret
  refine ⟨thinnedLaw G p q ε Λ d k, inferInstance,
    thinned_vertices_independent G p q ε Λ d k, ?_, ?_⟩
  · intro v
    simpa only [Contains, Finset.mem_singleton, forall_eq, Finset.card_singleton, pow_one, hq]
      using thinned_contains_probability G p q ε Λ d k {v}
  · have hlogs : ∀ i < k, 10000 * log (N : ℝ) ≤ ε * degreeScale ε d i := by
      intro i hi
      have hri : 1 ≤ ratioScale ε Λ i := by
        have hh := hprior i hi
        linarith
      have hdi := (scales_bounded_below ε Λ d i hε0.le hε1 hΛ hd.le hri).1
      have hmul := mul_le_mul_of_nonneg_left hdi hε0.le
      have heq : ε * (d / Λ ^ 5) = 10000 * log (N : ℝ) := by
        rw [← mul_div_assoc, hεd]
        field_simp
      rwa [heq] at hmul
    have hf := thinned_additive_failure_bound G p q N ε Λ d C
      (100000 * Λ ^ 5 * log N) k (by exact_mod_cast hN) (by exact_mod_cast hcard)
      hε0.le hε1 hΛ hd.le hp hC hdeg hprior hlogs hk0 hk1 (by nlinarith [hεd])
    apply hf.trans
    have hkReal : (k : ℝ) ≤ N := by exact_mod_cast hkN
    calc
      (k : ℝ) / (N : ℝ) ^ 2 ≤ N / (N : ℝ) ^ 2 := div_le_div_of_nonneg_right hkReal (sq_nonneg _)
      _ = 1 / N := by field_simp

/-- Symmetric near-regularity, including the small-degree empty-graph branch. -/
def NearlyRegularGood (d C err : ℝ) (s : State G) : Prop :=
  (∀ v, s.2 v = true → v ∈ s.1.verts) ∧
    ∃ d₁ : ℝ, d / C ≤ d₁ ∧ d₁ ≤ d ∧ DegreeWindow G s.1 (d₁ - err) (d₁ + err)

lemma additive_implies_nearly (d C err : ℝ) (herr : 0 ≤ err) (s : State G)
    (hs : AdditiveGood G d C err s) : NearlyRegularGood G d C err s := by
  obtain ⟨hA, d₁, hlo, hhi, hdeg⟩ := hs
  refine ⟨hA, d₁, hlo, hhi, ?_⟩
  intro v hv
  exact ⟨by linarith [(hdeg v hv).1], (hdeg v hv).2⟩

def emptySpanning : G.Subgraph where
  verts := Set.univ
  Adj := fun _ _ => False
  adj_sub := False.elim
  edge_vert := False.elim
  symm := ⟨fun _ _ => False.elim⟩

def emptyState (ω : V → Bool) : State G := (emptySpanning G, ω)

def emptyLaw (q : unitInterval) : Measure (State G) := (sampleMeasure V q).map (emptyState G)

instance emptyLaw_probability (q : unitInterval) : IsProbabilityMeasure (emptyLaw G q) := by
  unfold emptyLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

lemma emptyLaw_contains_probability (q : unitInterval) (S : Finset V) :
    (emptyLaw G q).real {s | Contains G S s} = (q : ℝ) ^ S.card := by
  have heq : emptyState G ⁻¹' {s | Contains G S s} = {ω | S ⊆ sampleVertices ω} := by
    ext ω
    simp [emptyState, Contains, sampleVertices, Finset.subset_iff]
  rw [emptyLaw, Measure.real, Measure.map_apply (measurable_of_finite _)
    MeasurableSet.of_discrete, heq]
  exact sample_contains_real_probability q S

theorem emptyLaw_independent (q : unitInterval) :
    iIndepSet (fun v : V => {s : State G | s.2 v = true}) (emptyLaw G q) := by
  have hm (S : Finset V) : (emptyLaw G q) {s | Contains G S s} =
      ENNReal.ofReal ((q : ℝ) ^ S.card) := by
    rw [← emptyLaw_contains_probability G q S, Measure.real,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [iIndepSet_iff_meas_biInter (fun _ => MeasurableSet.of_discrete)]
  intro S
  have heq : (⋂ v ∈ S, {s : State G | s.2 v = true}) = {s | Contains G S s} := by
    ext s
    simp [Contains]
  rw [heq, hm]
  have hsingle (v : V) : (emptyLaw G q) {s : State G | s.2 v = true} =
      ENNReal.ofReal (q : ℝ) := by simpa [Contains] using hm {v}
  simp_rw [hsingle]
  simp [ENNReal.ofReal_pow q.property.1]

lemma emptyState_nearly_good (d C err : ℝ) (hd : 0 ≤ d) (hC : 1 ≤ C)
    (herr : d / C ≤ err) (ω : V → Bool) :
    NearlyRegularGood G d C err (emptyState G ω) := by
  have hC0 : 0 < C := by linarith
  have hscale : d / C ≤ d := div_le_self hd hC
  have hscale0 : 0 ≤ d / C := div_nonneg hd hC0.le
  refine ⟨by simp [emptyState, emptySpanning], d / C, le_rfl, hscale, ?_⟩
  intro v hv
  have hzero : (emptyState G ω).1.spanningCoe.degree v = 0 := by
    unfold SimpleGraph.degree
    have he : (emptyState G ω).1.spanningCoe.neighborFinset v = ∅ := by
      ext u
      constructor
      · intro hu
        exact False.elim (((emptyState G ω).1.spanningCoe.mem_neighborFinset v u).mp hu)
      · simp
    rw [he, Finset.card_empty]
  rw [hzero]
  constructor <;> norm_num <;> linarith

lemma emptyLaw_failure_zero (q : unitInterval) (d C err : ℝ)
    (hall : ∀ ω, NearlyRegularGood G d C err (emptyState G ω)) :
    (emptyLaw G q).real {s | ¬ NearlyRegularGood G d C err s} = 0 := by
  rw [emptyLaw, Measure.real, Measure.map_apply (measurable_of_finite _)
    MeasurableSet.of_discrete]
  have he : emptyState G ⁻¹' {s | ¬ NearlyRegularGood G d C err s} = ∅ := by
    ext ω
    simp [hall ω]
  rw [he, measure_empty, ENNReal.toReal_zero]

/-- Complete additive regularization supplier with an explicit polynomial
constant, exact iid retained density, and a quantitative high-probability bound.
All states contain actual original-edge subgraphs; no final graph is assumed. -/
theorem exists_nearly_regular_law (N : ℕ) (Λ d : ℝ)
    (hN : 2 ≤ N) (hcard : Fintype.card V ≤ N) (hΛ : 1 ≤ Λ) (hd : 0 ≤ d)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Λ * d) :
    ∃ ν : Measure (State G), IsProbabilityMeasure ν ∧
      iIndepSet (fun v : V => {s : State G | s.2 v = true}) ν ∧
      (∀ v, ν.real {s : State G | s.2 v = true} = 1 / (1000000 * Λ ^ 5)) ∧
      ν.real {s | ¬ NearlyRegularGood G d (1000000 * Λ ^ 5)
        (100000 * Λ ^ 5 * log N) s} ≤ 1 / N := by
  have hΛ0 : 0 < Λ := by linarith
  have hΛ5 : 1 ≤ Λ ^ 5 := one_le_pow₀ hΛ
  have hC : 1 ≤ 1000000 * Λ ^ 5 := by nlinarith
  have hC0 : 0 < 1000000 * Λ ^ 5 := by positivity
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog0 : 0 ≤ log N := log_nonneg (by linarith)
  have herr0 : 0 ≤ 100000 * Λ ^ 5 * log N := by positivity
  let q : unitInterval := ⟨1 / (1000000 * Λ ^ 5),
    by exact ⟨by positivity, (div_le_one hC0).mpr hC⟩⟩
  have empty_suffices (hall : ∀ ω, NearlyRegularGood G d (1000000 * Λ ^ 5)
      (100000 * Λ ^ 5 * log N) (emptyState G ω)) :
      ∃ ν : Measure (State G), IsProbabilityMeasure ν ∧
        iIndepSet (fun v : V => {s : State G | s.2 v = true}) ν ∧
        (∀ v, ν.real {s : State G | s.2 v = true} = 1 / (1000000 * Λ ^ 5)) ∧
        ν.real {s | ¬ NearlyRegularGood G d (1000000 * Λ ^ 5)
          (100000 * Λ ^ 5 * log N) s} ≤ 1 / N := by
    refine ⟨emptyLaw G q, inferInstance, emptyLaw_independent G q, ?_, ?_⟩
    · intro v
      simpa [Contains, q] using emptyLaw_contains_probability G q {v}
    · rw [emptyLaw_failure_zero G q _ _ _ hall]
      positivity
  by_cases hne : Nonempty V
  · letI := hne
    by_cases hlarge : 1000000 * Λ ^ 5 * log N ≤ d
    · have hdpos : 0 < d := by
        have hl : 0 < log N := log_pos (by linarith)
        have ht : 0 < 1000000 * Λ ^ 5 * log N := by positivity
        exact ht.trans_le hlarge
      obtain ⟨ν, hν, hi, hm, hf⟩ := exists_additive_regularization_law G N Λ d
        (1000000 * Λ ^ 5) hN hcard hΛ hdpos hlarge (by nlinarith) hdeg
      letI := hν
      refine ⟨ν, hν, hi, hm, le_trans ?_ hf⟩
      apply measureReal_mono _ (measure_ne_top _ _)
      intro s hs ha
      exact hs (additive_implies_nearly G _ _ _ herr0 s ha)
    · apply empty_suffices
      intro ω
      apply emptyState_nearly_good G _ _ _ hd hC
      have hdl : d / (1000000 * Λ ^ 5) ≤ log N := by
        apply (div_le_iff₀ hC0).mpr
        nlinarith
      have he : log (N : ℝ) ≤ 100000 * Λ ^ 5 * log N := by
        have hmul := mul_le_mul_of_nonneg_right hΛ5 hlog0
        nlinarith
      exact hdl.trans he
  · haveI : IsEmpty V := not_nonempty_iff.mp hne
    apply empty_suffices
    intro ω
    refine ⟨?_, d / (1000000 * Λ ^ 5), le_rfl, div_le_self hd hC, ?_⟩
    · intro v
      exact isEmptyElim v
    · intro v
      exact isEmptyElim v

end Erdos585.Attempt6.RegularizationIteration
