import Openmath.Attempt6.PublicBernoulli

   
                                                                  
                                                                           
                                                                          
                                                         
  

namespace Erdos585.Attempt6

open MeasureTheory ProbabilityTheory Finset Real
open OAI.ErdosGallai.Sampling

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual number of original neighbors of v in the selected vertex set. -/
def reservoirNeighborCount (Q : Finset V) (v : V) : ℕ :=
  (G.neighborFinset v ∩ Q).card

/-- Exact lower tail for the original neighborhood, without a supplied good set. -/
theorem sampled_neighbor_lower_tail (p : unitInterval) (v : V) :
    (sampleMeasure V p).real
      {ω | (reservoirNeighborCount G (sampleVertices ω) v : ℝ) ≤
        (p : ℝ) * G.degree v / 2} ≤
      exp (-(p : ℝ) * G.degree v / 8) := by
  simpa [reservoirNeighborCount, SimpleGraph.card_neighborFinset_eq_degree] using
    sample_card_lower_tail p (G.neighborFinset v)

/-- Exact upper tail for the original neighborhood. -/
theorem sampled_neighbor_upper_tail (p : unitInterval) (v : V) :
    (sampleMeasure V p).real
      {ω | 2 * (p : ℝ) * G.degree v ≤
        (reservoirNeighborCount G (sampleVertices ω) v : ℝ)} ≤
      exp (-(p : ℝ) * G.degree v / 3) := by
  simpa [reservoirNeighborCount, SimpleGraph.card_neighborFinset_eq_degree] using
    sample_card_upper_tail p (G.neighborFinset v)

/-- Uniform failure bound using a lower and an upper bound on the original degree.
The upper-tail exponent uses the lower degree bound; the maximum degree controls
the upper threshold. -/
theorem sampled_neighbor_failure_bound (p : unitInterval) (δ Δ : ℝ) (v : V)
    (hδ : δ ≤ (G.degree v : ℝ)) (hΔ : (G.degree v : ℝ) ≤ Δ) :
    (sampleMeasure V p).real
      {ω | (reservoirNeighborCount G (sampleVertices ω) v : ℝ) < (p : ℝ) * δ / 2 ∨
        2 * (p : ℝ) * Δ < (reservoirNeighborCount G (sampleVertices ω) v : ℝ)} ≤
      exp (-(p : ℝ) * δ / 8) + exp (-(p : ℝ) * δ / 3) := by
  let μ := sampleMeasure V p
  let A : Set (V → Bool) :=
    {ω | (reservoirNeighborCount G (sampleVertices ω) v : ℝ) < (p : ℝ) * δ / 2}
  let B : Set (V → Bool) :=
    {ω | 2 * (p : ℝ) * Δ < (reservoirNeighborCount G (sampleVertices ω) v : ℝ)}
  have hp : 0 ≤ (p : ℝ) := p.property.1
  have hlow : μ.real A ≤ exp (-(p : ℝ) * δ / 8) := by
    have hsub : A ⊆
        {ω | (reservoirNeighborCount G (sampleVertices ω) v : ℝ) ≤
          (p : ℝ) * G.degree v / 2} := by
      intro ω hω
      change (reservoirNeighborCount G (sampleVertices ω) v : ℝ) < (p : ℝ) * δ / 2 at hω
      have hm := mul_le_mul_of_nonneg_left hδ hp
      change (reservoirNeighborCount G (sampleVertices ω) v : ℝ) ≤
        (p : ℝ) * G.degree v / 2
      linarith
    calc
      μ.real A ≤ μ.real _ := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ exp (-(p : ℝ) * G.degree v / 8) := sampled_neighbor_lower_tail G p v
      _ ≤ _ := exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hδ hp])
  have hupp : μ.real B ≤ exp (-(p : ℝ) * δ / 3) := by
    have hsub : B ⊆
        {ω | 2 * (p : ℝ) * G.degree v ≤
          (reservoirNeighborCount G (sampleVertices ω) v : ℝ)} := by
      intro ω hω
      change 2 * (p : ℝ) * Δ < (reservoirNeighborCount G (sampleVertices ω) v : ℝ) at hω
      have hm := mul_le_mul_of_nonneg_left hΔ hp
      change 2 * (p : ℝ) * G.degree v ≤
        (reservoirNeighborCount G (sampleVertices ω) v : ℝ)
      linarith
    calc
      μ.real B ≤ μ.real _ := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ exp (-(p : ℝ) * G.degree v / 3) := sampled_neighbor_upper_tail G p v
      _ ≤ _ := exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hδ hp])
  change μ.real (A ∪ B) ≤ _
  exact (measureReal_union_le A B).trans (add_le_add hlow hupp)

/-- A genuine vertex subset simultaneously controls neighbor counts at every
original vertex. The explicit union bound pays both tails. -/
theorem exists_reservoir_degree_bounds (p : unitInterval) (δ Δ : ℝ)
    (hδ : ∀ v, δ ≤ (G.degree v : ℝ))
    (hΔ : ∀ v, (G.degree v : ℝ) ≤ Δ)
    (hbudget : (Fintype.card V : ℝ) *
      (exp (-(p : ℝ) * δ / 8) + exp (-(p : ℝ) * δ / 3)) < 1) :
    ∃ Q : Finset V, ∀ v,
      (p : ℝ) * δ / 2 ≤ (reservoirNeighborCount G Q v : ℝ) ∧
      (reservoirNeighborCount G Q v : ℝ) ≤ 2 * (p : ℝ) * Δ := by
  let μ := sampleMeasure V p
  let E : V → Set (V → Bool) := fun v =>
    {ω | (reservoirNeighborCount G (sampleVertices ω) v : ℝ) < (p : ℝ) * δ / 2 ∨
      2 * (p : ℝ) * Δ < (reservoirNeighborCount G (sampleVertices ω) v : ℝ)}
  have hbound : ∑ v ∈ (Finset.univ : Finset V), μ.real (E v) < 1 := by
    calc
      _ ≤ ∑ _v ∈ (Finset.univ : Finset V),
          (exp (-(p : ℝ) * δ / 8) + exp (-(p : ℝ) * δ / 3)) := by
        apply Finset.sum_le_sum
        intro v _
        exact sampled_neighbor_failure_bound G p δ Δ v (hδ v) (hΔ v)
      _ = (Fintype.card V : ℝ) *
          (exp (-(p : ℝ) * δ / 8) + exp (-(p : ℝ) * δ / 3)) := by simp [mul_add]
      _ < 1 := hbudget
  obtain ⟨ω, hω⟩ := exists_avoiding_finite_events (μ := μ) Finset.univ E hbound
  refine ⟨sampleVertices ω, ?_⟩
  intro v
  have hgood := hω v (Finset.mem_univ v)
  change ¬(_ ∨ _) at hgood
  exact ⟨le_of_not_gt (fun h => hgood (Or.inl h)),
    le_of_not_gt (fun h => hgood (Or.inr h))⟩

/-- Explicit failure probability for simultaneous original-neighborhood control. -/
theorem sampled_all_neighbor_failure_bound (p : unitInterval) (δ Δ : ℝ)
    (hδ : ∀ v, δ ≤ (G.degree v : ℝ))
    (hΔ : ∀ v, (G.degree v : ℝ) ≤ Δ) :
    (sampleMeasure V p).real
      {ω | ∃ v, (reservoirNeighborCount G (sampleVertices ω) v : ℝ) < (p : ℝ) * δ / 2 ∨
        2 * (p : ℝ) * Δ < (reservoirNeighborCount G (sampleVertices ω) v : ℝ)} ≤
      (Fintype.card V : ℝ) *
        (exp (-(p : ℝ) * δ / 8) + exp (-(p : ℝ) * δ / 3)) := by
  let μ := sampleMeasure V p
  let E : V → Set (V → Bool) := fun v =>
    {ω | (reservoirNeighborCount G (sampleVertices ω) v : ℝ) < (p : ℝ) * δ / 2 ∨
      2 * (p : ℝ) * Δ < (reservoirNeighborCount G (sampleVertices ω) v : ℝ)}
  have heq :
      {ω | ∃ v, (reservoirNeighborCount G (sampleVertices ω) v : ℝ) < (p : ℝ) * δ / 2 ∨
        2 * (p : ℝ) * Δ < (reservoirNeighborCount G (sampleVertices ω) v : ℝ)} =
      ⋃ v ∈ (Finset.univ : Finset V), E v := by
    ext ω
    simp [E]
  rw [heq]
  calc
    μ.real (⋃ v ∈ (Finset.univ : Finset V), E v) ≤
        ∑ v ∈ (Finset.univ : Finset V), μ.real (E v) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ (Finset.univ : Finset V),
        (exp (-(p : ℝ) * δ / 8) + exp (-(p : ℝ) * δ / 3)) := by
      apply Finset.sum_le_sum
      intro v _
      exact sampled_neighbor_failure_bound G p δ Δ v (hδ v) (hΔ v)
    _ = _ := by simp [mul_add]

/-- Actual subset with both simultaneous degree concentration and a size bound.
The extra cardinality tail is explicitly paid, not inferred from degree control. -/
theorem exists_small_reservoir_degree_bounds (p : unitInterval) (δ Δ : ℝ)
    (hδ : ∀ v, δ ≤ (G.degree v : ℝ))
    (hΔ : ∀ v, (G.degree v : ℝ) ≤ Δ)
    (hbudget : (Fintype.card V : ℝ) *
        (exp (-(p : ℝ) * δ / 8) + exp (-(p : ℝ) * δ / 3)) +
      exp (-(p : ℝ) * Fintype.card V / 3) < 1) :
    ∃ Q : Finset V,
      (Q.card : ℝ) ≤ 2 * (p : ℝ) * Fintype.card V ∧
      ∀ v, (p : ℝ) * δ / 2 ≤ (reservoirNeighborCount G Q v : ℝ) ∧
        (reservoirNeighborCount G Q v : ℝ) ≤ 2 * (p : ℝ) * Δ := by
  let μ := sampleMeasure V p
  let A : Set (V → Bool) :=
    {ω | ∃ v, (reservoirNeighborCount G (sampleVertices ω) v : ℝ) < (p : ℝ) * δ / 2 ∨
      2 * (p : ℝ) * Δ < (reservoirNeighborCount G (sampleVertices ω) v : ℝ)}
  let B : Set (V → Bool) :=
    {ω | 2 * (p : ℝ) * Fintype.card V < ((sampleVertices ω).card : ℝ)}
  have hA : μ.real A ≤ (Fintype.card V : ℝ) *
      (exp (-(p : ℝ) * δ / 8) + exp (-(p : ℝ) * δ / 3)) :=
    sampled_all_neighbor_failure_bound G p δ Δ hδ hΔ
  have hB : μ.real B ≤ exp (-(p : ℝ) * Fintype.card V / 3) := by
    have ht := sample_card_upper_tail p (Finset.univ : Finset V)
    simp only [Finset.card_univ, Finset.univ_inter] at ht
    apply le_trans _ ht
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    change 2 * (p : ℝ) * Fintype.card V < ((sampleVertices ω).card : ℝ) at hω
    exact le_of_lt hω
  have hgood : μ.real (A ∪ B) < 1 :=
    lt_of_le_of_lt ((measureReal_union_le A B).trans (add_le_add hA hB)) hbudget
  let E : Unit → Set (V → Bool) := fun _ => A ∪ B
  have hfinite : ∑ i ∈ ({()} : Finset Unit), μ.real (E i) < 1 := by
    simpa [E] using hgood
  obtain ⟨ω, hω⟩ := exists_avoiding_finite_events (μ := μ) {()} E hfinite
  have hnot := hω () (by simp)
  change ¬(_ ∨ _) at hnot
  refine ⟨sampleVertices ω, ?_, ?_⟩
  · exact le_of_not_gt (fun h => hnot (Or.inr h))
  · intro v
    exact ⟨le_of_not_gt (fun h => hnot (Or.inl ⟨v, Or.inl h⟩)),
      le_of_not_gt (fun h => hnot (Or.inl ⟨v, Or.inr h⟩))⟩

end Erdos585.Attempt6
