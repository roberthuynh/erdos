import Openmath.Attempt6.RegularizationTransport
import Openmath.Attempt6.BernsteinBlocks
import Openmath.Attempt6.BalancedCompletion
import Openmath.Attempt6.ReservoirDegree

/-! Actual independent categorical vertex pools, their Bernoulli marginals,
finite Bernstein deviation bounds, and deterministic balanced completion. -/
noncomputable section
namespace Erdos585.Attempt6.CategoricalPools
open MeasureTheory ProbabilityTheory Finset Real
open OAI.ErdosGallai.Sampling
open AbsorberSelection.ProductLaw BernsteinBlocks
attribute [local instance] Classical.propDecidable

variable {V I B : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

abbrev Category (I : Type*) := Option (I × Bool)
instance categoryMeasurable : MeasurableSpace (Category I) := ⊤
instance categoryMeasurableSingleton : MeasurableSingletonClass (Category I) :=
  ⟨fun _ => MeasurableSet.of_discrete⟩

def categoryWeight (r t : I → ℝ) : Category I → ℝ
  | none => 1 - ∑ i, (r i + t i)
  | some (i, false) => r i
  | some (i, true) => t i

lemma categoryWeight_nonneg (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (ht : ∀ i, 0 ≤ t i) (hbudget : ∑ i, (r i + t i) ≤ 1) :
    ∀ c, 0 ≤ categoryWeight r t c := by
  rintro (_ | ⟨i, b⟩)
  · exact sub_nonneg.mpr hbudget
  · cases b
    · exact hr i
    · exact ht i

lemma categoryWeight_sum (r t : I → ℝ) : ∑ c, categoryWeight r t c = 1 := by
  simp [categoryWeight, Fintype.sum_option, Fintype.sum_prod_type,
    Finset.sum_add_distrib]
  ring

def finiteLaw [Fintype B] [MeasurableSpace B] (w : B → ℝ)
    (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b = 1) : Measure B :=
  (PMF.ofFintype (fun b => ENNReal.ofReal (w b)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => hw b), hs]
    simp)).toMeasure

instance finiteLaw_probability [Fintype B] [MeasurableSpace B]
    (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b = 1) :
    IsProbabilityMeasure (finiteLaw w hw hs) := by
  unfold finiteLaw
  infer_instance

lemma finiteLaw_singleton [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b = 1) (b : B) :
    (finiteLaw w hw hs).real {b} = w b := by
  simp [finiteLaw, Measure.real, PMF.toMeasure_apply_singleton, ENNReal.toReal_ofReal, hw]

def poolLaw (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i) (ht : ∀ i, 0 ≤ t i)
    (hbudget : ∑ i, (r i + t i) ≤ 1) : Measure (V → Category I) :=
  Measure.pi (fun _ : V => finiteLaw (categoryWeight r t)
    (categoryWeight_nonneg r t hr ht hbudget) (categoryWeight_sum r t))

instance poolLaw_probability (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (ht : ∀ i, 0 ≤ t i) (hbudget : ∑ i, (r i + t i) ≤ 1) :
    IsProbabilityMeasure (poolLaw (V := V) r t hr ht hbudget) := by
  unfold poolLaw
  infer_instance

def lowerPool (ω : V → Category I) (i : I) : Finset V :=
  Finset.univ.filter (fun v => ω v = some (i, false))
def bufferPool (ω : V → Category I) (i : I) : Finset V :=
  Finset.univ.filter (fun v => ω v = some (i, true))
def poolProjection (C : Finset (Category I)) (ω : V → Category I) : V → Bool :=
  fun v => decide (ω v ∈ C)

lemma pools_disjoint (ω : V → Category I) :
    Pairwise (fun i j => Disjoint (lowerPool ω i ∪ bufferPool ω i)
      (lowerPool ω j ∪ bufferPool ω j)) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro v hv hi
  simp only [lowerPool, bufferPool, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and] at hv hi
  rcases hv with hv | hv <;> rcases hi with hi | hi <;> simp_all

lemma lower_buffer_disjoint (ω : V → Category I) (i : I) :
    Disjoint (lowerPool ω i) (bufferPool ω i) := by
  rw [Finset.disjoint_left]
  intro v hv hi
  simp [lowerPool, bufferPool] at hv hi
  simp_all

lemma finite_event_sum {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (μ : Measure S) [IsProbabilityMeasure μ] (E : Set S) :
    μ.real E = ∑ s, if s ∈ E then μ.real {s} else 0 := by
  have h := sum_measureReal_singleton (μ := μ) (Finset.univ.filter (fun s => s ∈ E))
  have he : ((Finset.univ.filter (fun s => s ∈ E) : Finset S) : Set S) = E := by
    ext s
    simp
  rw [he, Finset.sum_filter] at h
  exact h.symm

lemma poolLaw_singleton (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (ht : ∀ i, 0 ≤ t i) (hbudget : ∑ i, (r i + t i) ≤ 1)
    (ω : V → Category I) :
    (poolLaw r t hr ht hbudget).real {ω} = mass (fun _ : V => categoryWeight r t) ω := by
  rw [poolLaw, Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro v _
  exact finiteLaw_singleton _ _ _ _

lemma poolLaw_event_sum (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (ht : ∀ i, 0 ≤ t i) (hbudget : ∑ i, (r i + t i) ≤ 1)
    (E : Set (V → Category I)) :
    (poolLaw r t hr ht hbudget).real E =
      ∑ ω, if ω ∈ E then mass (fun _ : V => categoryWeight r t) ω else 0 := by
  rw [finite_event_sum]
  simp_rw [poolLaw_singleton]

lemma category_probability (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (ht : ∀ i, 0 ≤ t i) (hbudget : ∑ i, (r i + t i) ≤ 1)
    (C : Finset (Category I)) :
    (finiteLaw (categoryWeight r t) (categoryWeight_nonneg r t hr ht hbudget)
      (categoryWeight_sum r t)).real C = ∑ c ∈ C, categoryWeight r t c := by
  rw [← sum_measureReal_singleton]
  simp_rw [finiteLaw_singleton]

/-- Projecting any category collection yields exactly the usual independent
Bernoulli vertex sampler at its total category probability. -/
theorem poolProjection_map (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (ht : ∀ i, 0 ≤ t i) (hbudget : ∑ i, (r i + t i) ≤ 1)
    (C : Finset (Category I)) (p : unitInterval)
    (hp : (p : ℝ) = ∑ c ∈ C, categoryWeight r t c) :
    (poolLaw (V := V) r t hr ht hbudget).map (poolProjection C) = sampleMeasure V p := by
  let μ := finiteLaw (categoryWeight r t) (categoryWeight_nonneg r t hr ht hbudget)
    (categoryWeight_sum r t)
  have hi : iIndepFun (fun v : V => fun ω : V → Category I => ω v)
      (poolLaw r t hr ht hbudget) :=
    iIndepFun_pi (X := fun _ : V => id) (fun _ => measurable_id.aemeasurable)
  have hj := hi.comp (fun _ : V => fun c : Category I => decide (c ∈ C))
    (fun _ => measurable_of_finite _)
  change iIndepFun (fun v : V => fun ω : V → Category I => decide (ω v ∈ C))
    (poolLaw r t hr ht hbudget) at hj
  change (poolLaw r t hr ht hbudget).map
    (fun ω v => decide (ω v ∈ C)) = _
  rw [hj.map_fun_eq_pi_map (fun _ => (measurable_of_finite _).aemeasurable)]
  unfold sampleMeasure
  congr 1
  funext v
  have hcoord := (measurePreserving_eval (fun _ : V => μ) v).map_eq
  have hcomp : (poolLaw (V := V) r t hr ht hbudget).map
      (fun ω => decide (ω v ∈ C)) = μ.map (fun c => decide (c ∈ C)) := by
    rw [← hcoord, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
    rfl
  rw [hcomp]
  haveI : IsProbabilityMeasure (μ.map (fun c => decide (c ∈ C))) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable
  apply RegularizationTransport.bool_measure_eq_bernoulli
  rw [Measure.real, Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  have he : {c : Category I | decide (c ∈ C) = true} = (C : Set (Category I)) := by
    ext c
    simp
  change μ.real {c | decide (c ∈ C) = true} = _
  rw [he, hp]
  exact category_probability r t hr ht hbudget C

def categoryCount (C : Finset (Category I)) (Q : Finset V)
    (ω : V → Category I) : ℕ := (Q.filter (fun v => ω v ∈ C)).card

def countIndicator (C : Finset (Category I)) (Q : Finset V) (v : V)
    (c : Category I) : ℝ := if v ∈ Q ∧ c ∈ C then 1 else 0

lemma categoryCount_eq_sum (C : Finset (Category I)) (Q : Finset V)
    (ω : V → Category I) :
    (categoryCount C Q ω : ℝ) = ∑ v, countIndicator C Q v (ω v) := by
  rw [categoryCount, Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  simp [countIndicator, ite_and]

lemma countIndicator_mean (r t : I → ℝ) (C : Finset (Category I))
    (Q : Finset V) (v : V) :
    mean (categoryWeight r t) (countIndicator C Q v) =
      if v ∈ Q then ∑ c ∈ C, categoryWeight r t c else 0 := by
  by_cases hv : v ∈ Q
  · simp [mean, countIndicator, hv, Finset.sum_filter]
  · simp [mean, countIndicator, hv]

lemma total_count_mean (r t : I → ℝ) (C : Finset (Category I)) (Q : Finset V) :
    (∑ v, mean (categoryWeight r t) (countIndicator C Q v)) =
      (∑ c ∈ C, categoryWeight r t c) * Q.card := by
  simp_rw [countIndicator_mean]
  simp [mul_comm]

/-- A genuine categorical count has a mean-sensitive Bernstein tail under
the actual product measure. Apply Q to a shore or to any ambient neighborhood. -/
theorem categoryCount_bernstein (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (ht : ∀ i, 0 ≤ t i) (hbudget : ∑ i, (r i + t i) ≤ 1)
    (C : Finset (Category I)) (Q : Finset V) (a : ℝ) (ha : 0 < a) :
    let M := (∑ c ∈ C, categoryWeight r t c) * Q.card
    (poolLaw r t hr ht hbudget).real
      {ω | 2 * sqrt (M * a) + 2 * a ≤ |(categoryCount C Q ω : ℝ) - M|} ≤
      2 * exp (-a) := by
  dsimp only
  rw [poolLaw_event_sum]
  have h := nonnegative_block_bernstein (fun _ : V => categoryWeight r t)
    (countIndicator C Q) (fun _ => categoryWeight_nonneg r t hr ht hbudget)
    (fun _ => categoryWeight_sum r t) 1 a (by norm_num) ha
    (fun v c => by unfold countIndicator; split_ifs <;> norm_num)
  dsimp only at h
  simp only [one_mul, mul_one, total_count_mean, ← categoryCount_eq_sum] at h
  exact h

/-- All requested centers, shores and category unions are handled by one
finite union bound. The input is only a list of count queries, not a good-event
probability assumption. -/
theorem all_counts_failure_bound {J : Type*} [Fintype J]
    (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i) (ht : ∀ i, 0 ≤ t i)
    (hbudget : ∑ i, (r i + t i) ≤ 1)
    (C : J → Finset (Category I)) (Q : J → Finset V)
    (a : ℝ) (ha : 0 < a) :
    (poolLaw r t hr ht hbudget).real {ω | ∃ j,
      2 * sqrt (((∑ c ∈ C j, categoryWeight r t c) * (Q j).card) * a) + 2 * a ≤
        |(categoryCount (C j) (Q j) ω : ℝ) -
          (∑ c ∈ C j, categoryWeight r t c) * (Q j).card|} ≤
      (Fintype.card J : ℝ) * (2 * exp (-a)) := by
  let E : J → Set (V → Category I) := fun j => {ω |
    2 * sqrt (((∑ c ∈ C j, categoryWeight r t c) * (Q j).card) * a) + 2 * a ≤
      |(categoryCount (C j) (Q j) ω : ℝ) -
        (∑ c ∈ C j, categoryWeight r t c) * (Q j).card|}
  have he : {ω | ∃ j, ω ∈ E j} = ⋃ j ∈ (Finset.univ : Finset J), E j := by
    ext ω
    simp
  change (poolLaw r t hr ht hbudget).real {ω | ∃ j, ω ∈ E j} ≤ _
  rw [he]
  calc
    _ ≤ ∑ j ∈ (Finset.univ : Finset J), (poolLaw r t hr ht hbudget).real (E j) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ (Finset.univ : Finset J), 2 * exp (-a) :=
      Finset.sum_le_sum (fun j _ => categoryCount_bernstein r t hr ht hbudget (C j) (Q j) a ha)
    _ = _ := by simp

def lowerCategories (i : I) : Finset (Category I) := {some (i, false)}
def upperCategories (i : I) : Finset (Category I) := {some (i, false), some (i, true)}

lemma lowerCategories_weight (r t : I → ℝ) (i : I) :
    (∑ c ∈ lowerCategories i, categoryWeight r t c) = r i := by
  simp [lowerCategories, categoryWeight]

lemma upperCategories_weight (r t : I → ℝ) (i : I) :
    (∑ c ∈ upperCategories i, categoryWeight r t c) = r i + t i := by
  simp [upperCategories, categoryWeight]

lemma lowerCategories_count (ω : V → Category I) (i : I) (Q : Finset V) :
    categoryCount (lowerCategories i) Q ω = (lowerPool ω i ∩ Q).card := by
  unfold categoryCount
  congr 1
  ext v
  simp [categoryCount, lowerCategories, lowerPool, and_comm]

lemma upperCategories_count (ω : V → Category I) (i : I) (Q : Finset V) :
    categoryCount (upperCategories i) Q ω = ((lowerPool ω i ∪ bufferPool ω i) ∩ Q).card := by
  unfold categoryCount
  congr 1
  ext v
  simp [categoryCount, upperCategories, lowerPool, bufferPool, and_comm]

lemma lowerProjection_vertices (ω : V → Category I) (i : I) :
    sampleVertices (poolProjection (lowerCategories i) ω) = lowerPool ω i := by
  ext v
  simp [sampleVertices, poolProjection, lowerCategories, lowerPool]

lemma upperProjection_vertices (ω : V → Category I) (i : I) :
    sampleVertices (poolProjection (upperCategories i) ω) = lowerPool ω i ∪ bufferPool ω i := by
  ext v
  simp [sampleVertices, poolProjection, upperCategories, lowerPool, bufferPool]

def radius (M a : ℝ) : ℝ := 2 * sqrt (M * a) + 2 * a

theorem exists_all_counts_good {J : Type*} [Fintype J]
    (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i) (ht : ∀ i, 0 ≤ t i)
    (hbudget : ∑ i, (r i + t i) ≤ 1)
    (C : J → Finset (Category I)) (Q : J → Finset V)
    (a : ℝ) (ha : 0 < a)
    (hsmall : (Fintype.card J : ℝ) * (2 * exp (-a)) < 1) :
    ∃ ω : V → Category I, ∀ j,
      |(categoryCount (C j) (Q j) ω : ℝ) -
        (∑ c ∈ C j, categoryWeight r t c) * (Q j).card| <
      radius ((∑ c ∈ C j, categoryWeight r t c) * (Q j).card) a := by
  let E : J → Set (V → Category I) := fun j => {ω |
    radius ((∑ c ∈ C j, categoryWeight r t c) * (Q j).card) a ≤
      |(categoryCount (C j) (Q j) ω : ℝ) -
        (∑ c ∈ C j, categoryWeight r t c) * (Q j).card|}
  have hb : ∑ j ∈ (Finset.univ : Finset J),
      (poolLaw r t hr ht hbudget).real (E j) < 1 := calc
    _ ≤ ∑ _j ∈ (Finset.univ : Finset J), 2 * exp (-a) :=
      Finset.sum_le_sum (fun j _ => categoryCount_bernstein r t hr ht hbudget (C j) (Q j) a ha)
    _ = (Fintype.card J : ℝ) * (2 * exp (-a)) := by simp
    _ < 1 := hsmall
  obtain ⟨ω, hω⟩ := exists_avoiding_finite_events
    (μ := poolLaw r t hr ht hbudget) Finset.univ E hb
  exact ⟨ω, fun j => lt_of_not_ge (hω j (Finset.mem_univ j))⟩

def selectedCategories (i : I) (upper : Bool) : Finset (Category I) :=
  if upper then upperCategories i else lowerCategories i
def selectedRate (r t : I → ℝ) (i : I) (upper : Bool) : ℝ :=
  if upper then r i + t i else r i
def selectedPool (ω : V → Category I) (i : I) (upper : Bool) : Finset V :=
  if upper then lowerPool ω i ∪ bufferPool ω i else lowerPool ω i
def shore (Q : Finset V) (right : Bool) : Finset V := if right then Qᶜ else Q

lemma selectedCategories_weight (r t : I → ℝ) (i : I) (b : Bool) :
    (∑ c ∈ selectedCategories i b, categoryWeight r t c) = selectedRate r t i b := by
  cases b <;> simp [selectedCategories, selectedRate, lowerCategories_weight,
    upperCategories_weight]

lemma selectedCategories_count (ω : V → Category I) (i : I) (b : Bool) (Q : Finset V) :
    categoryCount (selectedCategories i b) Q ω = (selectedPool ω i b ∩ Q).card := by
  cases b <;> simp [selectedCategories, selectedPool, lowerCategories_count,
    upperCategories_count]

/-- Actual simultaneous balanced pools with concentration on any finite family
of additional vertex sets. Choose those sets to be retained and original
neighborhoods to obtain all-center degree control in the same outcome. -/
theorem exists_balanced_pools_with_counts {J : Type*} [Fintype J]
    (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i) (ht : ∀ i, 0 ≤ t i)
    (hbudget : ∑ i, (r i + t i) ≤ 1)
    (Q : Finset V) (m : I → ℕ) (N : J → Finset V) (a : ℝ) (ha : 0 < a)
    (hsmall : (Fintype.card (I × Bool × (Bool ⊕ J)) : ℝ) * (2 * exp (-a)) < 1)
    (hmargin : ∀ i b,
      r i * (shore Q b).card + radius (r i * (shore Q b).card) a ≤ m i ∧
      (m i : ℝ) ≤ (r i + t i) * (shore Q b).card -
        radius ((r i + t i) * (shore Q b).card) a) :
    ∃ (ω : V → Category I) (S : I → Finset V),
      (∀ i, lowerPool ω i ⊆ S i ∧ S i ⊆ lowerPool ω i ∪ bufferPool ω i ∧
        (S i ∩ Q).card = m i ∧ (S i ∩ Qᶜ).card = m i ∧ (S i).card = 2 * m i) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      ∀ i b j,
        |((selectedPool ω i b ∩ N j).card : ℝ) - selectedRate r t i b * (N j).card| <
          radius (selectedRate r t i b * (N j).card) a := by
  let C : I × Bool × (Bool ⊕ J) → Finset (Category I) :=
    fun x => selectedCategories x.1 x.2.1
  let A : I × Bool × (Bool ⊕ J) → Finset V :=
    fun x => Sum.elim (shore Q) N x.2.2
  obtain ⟨ω, hω⟩ := exists_all_counts_good r t hr ht hbudget C A a ha hsmall
  have hcounts (i : I) (b : Bool) :
      (lowerPool ω i ∩ shore Q b).card ≤ m i ∧
      m i ≤ ((lowerPool ω i ∪ bufferPool ω i) ∩ shore Q b).card := by
    have hl : |((lowerPool ω i ∩ shore Q b).card : ℝ) - r i * (shore Q b).card| <
        radius (r i * (shore Q b).card) a := by
      simpa [C, A, selectedCategories_count, selectedCategories_weight,
        selectedPool, selectedRate] using hω (i, false, Sum.inl b)
    have hu : |(((lowerPool ω i ∪ bufferPool ω i) ∩ shore Q b).card : ℝ) -
        (r i + t i) * (shore Q b).card| < radius ((r i + t i) * (shore Q b).card) a := by
      simpa [C, A, selectedCategories_count, selectedCategories_weight,
        selectedPool, selectedRate] using hω (i, true, Sum.inl b)
    have hln : ((lowerPool ω i ∩ shore Q b).card : ℝ) ≤ m i := by
      linarith [(abs_lt.mp hl).2, (hmargin i b).1]
    have hun : (m i : ℝ) ≤ ((lowerPool ω i ∪ bufferPool ω i) ∩ shore Q b).card := by
      linarith [(abs_lt.mp hu).1, (hmargin i b).2]
    exact ⟨by exact_mod_cast hln, by exact_mod_cast hun⟩
  obtain ⟨S, hS, hdis⟩ := exists_pairwise_disjoint_balanced_completion
    (lowerPool ω) (bufferPool ω) Q m (pools_disjoint ω) (fun i =>
      ⟨by simpa [shore] using hcounts i false, by simpa [shore] using hcounts i true⟩)
  refine ⟨ω, S, hS, hdis, ?_⟩
  intro i b j
  simpa [C, A, selectedCategories_count, selectedCategories_weight] using
    hω (i, b, Sum.inr j)

/-- Any event about a lower pool transfers exactly to the standard Bernoulli
sampler; this includes the published connecting-property failure event. -/
theorem lowerPool_event_probability (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (ht : ∀ i, 0 ≤ t i) (hbudget : ∑ i, (r i + t i) ≤ 1)
    (i : I) (p : unitInterval) (hp : (p : ℝ) = r i) (P : Finset V → Prop) :
    (poolLaw r t hr ht hbudget).real {ω | P (lowerPool ω i)} =
      (sampleMeasure V p).real {A | P (sampleVertices A)} := by
  have hm := poolProjection_map (V := V) r t hr ht hbudget (lowerCategories i) p
    (by simpa [lowerCategories_weight] using hp)
  rw [← hm]
  simp only [Measure.real]
  rw [Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  apply congrArg ENNReal.toReal
  congr 1
  ext ω
  simp [lowerProjection_vertices]

lemma graphDegreeInto_eq_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : graphDegreeInto G S v = (S ∩ G.neighborFinset v).card := by
  unfold graphDegreeInto
  congr 1
  ext u
  simp

/-- Explicit all-center, all-pool deviation bound in any original graph.
Each lower or upper categorical pool has its exact binomial mean. -/
theorem all_pool_degree_failure_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i) (ht : ∀ i, 0 ≤ t i)
    (hbudget : ∑ i, (r i + t i) ≤ 1) (a : ℝ) (ha : 0 < a) :
    (poolLaw r t hr ht hbudget).real {ω | ∃ i b v,
      radius (selectedRate r t i b * G.degree v) a ≤
        |(graphDegreeInto G (selectedPool ω i b) v : ℝ) - selectedRate r t i b * G.degree v|} ≤
      (Fintype.card (I × Bool × V) : ℝ) * (2 * exp (-a)) := by
  have h := all_counts_failure_bound r t hr ht hbudget
    (fun x : I × Bool × V => selectedCategories x.1 x.2.1)
    (fun x : I × Bool × V => G.neighborFinset x.2.2) a ha
  simp only [selectedCategories_weight, selectedCategories_count,
    SimpleGraph.card_neighborFinset_eq_degree, ← graphDegreeInto_eq_inter,
    Prod.exists] at h
  exact h

/-- Completion preserves every queried count inside the lower/upper envelope.
This pays arbitrary balancing without any extra degree error. -/
lemma completion_count_bounds (ω : V → Category I) (i : I) (S A : Finset V)
    (hlo : lowerPool ω i ⊆ S) (hhi : S ⊆ lowerPool ω i ∪ bufferPool ω i)
    (r t a : ℝ)
    (hl : |((lowerPool ω i ∩ A).card : ℝ) - r * A.card| < radius (r * A.card) a)
    (hu : |(((lowerPool ω i ∪ bufferPool ω i) ∩ A).card : ℝ) - (r + t) * A.card| <
      radius ((r + t) * A.card) a) :
    r * A.card - radius (r * A.card) a ≤ (S ∩ A).card ∧
      ((S ∩ A).card : ℝ) ≤ (r + t) * A.card + radius ((r + t) * A.card) a := by
  have hln : ((lowerPool ω i ∩ A).card : ℝ) ≤ (S ∩ A).card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter hlo (by rfl))
  have hun : ((S ∩ A).card : ℝ) ≤ ((lowerPool ω i ∪ bufferPool ω i) ∩ A).card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter hhi (by rfl))
  constructor
  · linarith [(abs_lt.mp hl).1]
  · linarith [(abs_lt.mp hu).2]

def sourceLowerRate (n m z w : ℝ) : ℝ := (2 * m - 4 * z * m - w) / n
def sourceBufferRate (n m z w : ℝ) : ℝ := (10 * z * m + 2 * w) / n

lemma source_total_rate (n m z w : ℝ) :
    sourceLowerRate n m z w + sourceBufferRate n m z w = (2 * m + 6 * z * m + w) / n := by
  unfold sourceLowerRate sourceBufferRate
  ring

/-- Exact source lower shore mean, including the imbalance correction. -/
theorem source_lower_shore_mean (n m z w q : ℝ) (hn : 0 < n)
    (hm : 0 ≤ m) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hnum : 4 * z * m + w ≤ 2 * m) (hq : q ≤ n * (1 / 2 + z)) :
    sourceLowerRate n m z w * q ≤ m - w / 2 := by
  have hr : 0 ≤ sourceLowerRate n m z w := by
    unfold sourceLowerRate
    exact div_nonneg (by linarith) hn.le
  have h := mul_le_mul_of_nonneg_left hq hr
  have he : sourceLowerRate n m z w * (n * (1 / 2 + z)) =
      (2 * m - 4 * z * m - w) * (1 / 2 + z) := by
    unfold sourceLowerRate
    field_simp
  rw [he] at h
  have hzz : 0 ≤ z ^ 2 * m := mul_nonneg (sq_nonneg z) hm
  nlinarith [mul_nonneg hz hw]

/-- Exact source upper shore mean; the displayed hypothesis is the precise
small-imbalance condition used in CONCENTRATION Section1. -/
theorem source_upper_shore_mean (n m z w q : ℝ) (hn : 0 < n)
    (hm : 0 ≤ m) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hwsmall : w ≤ m * (1 - 6 * z)) (hq : n * (1 / 2 - z) ≤ q) :
    m + w / 2 ≤ (sourceLowerRate n m z w + sourceBufferRate n m z w) * q := by
  rw [source_total_rate]
  have hr : 0 ≤ (2 * m + 6 * z * m + w) / n := by positivity
  have h := mul_le_mul_of_nonneg_left hq hr
  have he : (2 * m + 6 * z * m + w) / n * (n * (1 / 2 - z)) =
      (2 * m + 6 * z * m + w) * (1 / 2 - z) := by field_simp
  rw [he] at h
  have hc := mul_le_mul_of_nonneg_left hwsmall hz
  nlinarith

/-- The proposed100sqrt(mL) balancing margin pays the actual checked
Bernstein radius at a=10L whenever the relevant mean is at most2m and L≤m. -/
theorem source_balancing_radius (M m L : ℝ) (hM : 0 ≤ M) (hmean : M ≤ 2 * m)
    (hL : 0 ≤ L) (hLm : L ≤ m) :
    radius M (10 * L) ≤ (100 * sqrt (m * L)) / 2 := by
  have hm : 0 ≤ m := hL.trans hLm
  have hs0 : 0 ≤ sqrt (m * L) := sqrt_nonneg _
  have hs2 : sqrt (m * L) ^ 2 = m * L := sq_sqrt (mul_nonneg hm hL)
  have hLs : L ≤ sqrt (m * L) := by
    have hh := mul_le_mul_of_nonneg_right hLm hL
    nlinarith
  have ht0 : 0 ≤ sqrt (M * (10 * L)) := sqrt_nonneg _
  have ht2 : sqrt (M * (10 * L)) ^ 2 = M * (10 * L) :=
    sq_sqrt (by positivity)
  have hts : sqrt (M * (10 * L)) ≤ 5 * sqrt (m * L) := by
    have hh := mul_le_mul_of_nonneg_right hmean (show 0 ≤ 10 * L by positivity)
    nlinarith
  unfold radius
  nlinarith

/-- Concrete finite conditions ensure the source category probabilities are
valid jointly, rather than merely individually. -/
theorem source_rates_valid (n z : ℝ) (m w : I → ℝ) (hn : 0 < n)
    (hz : 0 ≤ z) (hzsmall : z ≤ 1 / 20)
    (hm : ∀ i, 0 ≤ m i) (hw : ∀ i, 0 ≤ w i)
    (hwsmall : ∀ i, w i ≤ m i / 10) (hsize : ∑ i, 3 * m i ≤ n) :
    (∀ i, 0 ≤ sourceLowerRate n (m i) z (w i)) ∧
    (∀ i, 0 ≤ sourceBufferRate n (m i) z (w i)) ∧
    (∑ i, (sourceLowerRate n (m i) z (w i) + sourceBufferRate n (m i) z (w i))) ≤ 1 := by
  have hzm (i : I) : z * m i ≤ m i / 20 := by
    have h := mul_le_mul_of_nonneg_right hzsmall (hm i)
    nlinarith
  refine ⟨fun i => div_nonneg (by nlinarith [hzm i, hwsmall i, hm i]) hn.le,
    fun i => div_nonneg (by have hmi := hm i; have hwi := hw i; positivity) hn.le, ?_⟩
  simp_rw [source_total_rate]
  calc
    _ ≤ ∑ i, (3 * m i) / n := Finset.sum_le_sum (fun i _ =>
      div_le_div_of_nonneg_right (by nlinarith [hzm i, hwsmall i, hm i]) hn.le)
    _ = (∑ i, 3 * m i) / n := (Finset.sum_div _ _ _).symm
    _ ≤ 1 := (div_le_one hn).mpr hsize

theorem source_sqrt_margin_small (m L : ℝ) (hm : 0 ≤ m) (hL : 0 ≤ L)
    (hlarge : 1000000 * L ≤ m) : 100 * sqrt (m * L) ≤ m / 10 := by
  have hs := sq_sqrt (mul_nonneg hm hL)
  have hs0 := sqrt_nonneg (m * L)
  have h := mul_le_mul_of_nonneg_left hlarge hm
  nlinarith

/-- The source upper and lower shore means are at most2m under explicit
smallness conditions; this is the variance proxy needed by the balancing tail. -/
theorem source_shore_means_le (n m z w q : ℝ) (hn : 0 < n)
    (hm : 0 ≤ m) (hz : 0 ≤ z) (hzsmall : z ≤ 1 / 20)
    (hw : 0 ≤ w) (hwsmall : w ≤ m / 10) (hq0 : 0 ≤ q)
    (hq : q ≤ n * (1 / 2 + z)) :
    sourceLowerRate n m z w * q ≤ 2 * m ∧
    (sourceLowerRate n m z w + sourceBufferRate n m z w) * q ≤ 2 * m := by
  have hzm : z * m ≤ m / 20 := by
    have h := mul_le_mul_of_nonneg_right hzsmall hm
    nlinarith
  have hnum : 4 * z * m + w ≤ 2 * m := by nlinarith
  have hlo := source_lower_shore_mean n m z w q hn hm hz hw hnum hq
  refine ⟨by linarith, ?_⟩
  rw [source_total_rate]
  have hrate : 0 ≤ (2 * m + 6 * z * m + w) / n := by positivity
  have hq2 : q ≤ n * (2 / 3) := by nlinarith
  have h := mul_le_mul_of_nonneg_left hq2 hrate
  have he : (2 * m + 6 * z * m + w) / n * (n * (2 / 3)) =
      (2 * m + 6 * z * m + w) * (2 / 3) := by field_simp
  rw [he] at h
  nlinarith

/-- The exact source shore formulas and square-root margin discharge the
deterministic balancing inequalities required by the categorical constructor. -/
theorem source_shore_balancing_margins (n m z L q : ℝ) (hn : 0 < n)
    (hm : 0 ≤ m) (hz : 0 ≤ z) (hzsmall : z ≤ 1 / 20) (hL : 0 ≤ L)
    (hlarge : 1000000 * L ≤ m) (hq0 : 0 ≤ q)
    (hql : n * (1 / 2 - z) ≤ q) (hqu : q ≤ n * (1 / 2 + z)) :
    let w := 100 * sqrt (m * L)
    let r := sourceLowerRate n m z w
    let t := sourceBufferRate n m z w
    r * q + radius (r * q) (10 * L) ≤ m ∧
      m ≤ (r + t) * q - radius ((r + t) * q) (10 * L) := by
  dsimp only
  let w := 100 * sqrt (m * L)
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hwsmall : w ≤ m / 10 := source_sqrt_margin_small m L hm hL hlarge
  have hzm : z * m ≤ m / 20 := by
    have h := mul_le_mul_of_nonneg_right hzsmall hm
    nlinarith
  have hnum : 4 * z * m + w ≤ 2 * m := by nlinarith
  have hsmall : w ≤ m * (1 - 6 * z) := by nlinarith
  have hl := source_lower_shore_mean n m z w q hn hm hz hw hnum hqu
  have hu := source_upper_shore_mean n m z w q hn hm hz hw hsmall hql
  have hmeans := source_shore_means_le n m z w q hn hm hz hzsmall hw hwsmall hq0 hqu
  have hr0 : 0 ≤ sourceLowerRate n m z w := div_nonneg (by linarith) hn.le
  have ht0 : 0 ≤ sourceBufferRate n m z w := div_nonneg (by positivity) hn.le
  have hLm : L ≤ m := by linarith
  have hrl := source_balancing_radius _ m L (mul_nonneg hr0 hq0) hmeans.1 hL hLm
  have hru := source_balancing_radius _ m L (mul_nonneg (add_nonneg hr0 ht0) hq0)
    hmeans.2 hL hLm
  change _ + _ ≤ m ∧ m ≤ _ - _
  dsimp [w] at hl hu hrl hru ⊢
  constructor <;> linarith

/-- Source Section1 categorical pools with the proposed square-root margin.
Every probability and balancing obligation is derived from concrete finite
size, imbalance and tail-budget inequalities. Additional queries may be every
retained and original neighborhood simultaneously. -/
theorem exists_source_balanced_pools {J : Type*} [Fintype J]
    (Q : Finset V) (m : I → ℕ) (N : J → Finset V) (z L : ℝ)
    (hn : 0 < (Fintype.card V : ℝ)) (hz : 0 ≤ z) (hzsmall : z ≤ 1 / 20)
    (hL : 0 < L) (hlarge : ∀ i, 1000000 * L ≤ m i)
    (hsize : ∑ i, (3 * m i : ℝ) ≤ Fintype.card V)
    (hshore : ∀ b, (Fintype.card V : ℝ) * (1 / 2 - z) ≤ (shore Q b).card ∧
      ((shore Q b).card : ℝ) ≤ (Fintype.card V : ℝ) * (1 / 2 + z))
    (hsmall : (Fintype.card (I × Bool × (Bool ⊕ J)) : ℝ) * (2 * exp (-(10 * L))) < 1) :
    let r := fun i => sourceLowerRate (Fintype.card V) (m i) z (100 * sqrt (m i * L))
    let t := fun i => sourceBufferRate (Fintype.card V) (m i) z (100 * sqrt (m i * L))
    ∃ (ω : V → Category I) (S : I → Finset V),
      (∀ i, lowerPool ω i ⊆ S i ∧ S i ⊆ lowerPool ω i ∪ bufferPool ω i ∧
        (S i ∩ Q).card = m i ∧ (S i ∩ Qᶜ).card = m i ∧ (S i).card = 2 * m i) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      ∀ i b j,
        |((selectedPool ω i b ∩ N j).card : ℝ) - selectedRate r t i b * (N j).card| <
          radius (selectedRate r t i b * (N j).card) (10 * L) := by
  dsimp only
  have hv := source_rates_valid (Fintype.card V) z (fun i => (m i : ℝ))
    (fun i => 100 * sqrt (m i * L)) hn hz hzsmall (fun i => Nat.cast_nonneg _)
    (fun i => by positivity)
    (fun i => source_sqrt_margin_small (m i) L (Nat.cast_nonneg _) hL.le (hlarge i)) hsize
  apply exists_balanced_pools_with_counts _ _ hv.1 hv.2.1 hv.2.2 Q m N
    (10 * L) (by positivity) hsmall
  intro i b
  exact source_shore_balancing_margins (Fintype.card V) (m i) z L (shore Q b).card
    hn (Nat.cast_nonneg _) hz hzsmall hL.le (hlarge i) (Nat.cast_nonneg _)
    (hshore b).1 (hshore b).2

def lowerProbability (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (ht : ∀ i, 0 ≤ t i) (hbudget : ∑ i, (r i + t i) ≤ 1) (i : I) : unitInterval :=
  ⟨r i, hr i, by
    have hsingle : r i + t i ≤ ∑ j, (r j + t j) :=
      Finset.single_le_sum (fun j _ => add_nonneg (hr j) (ht j)) (Finset.mem_univ i)
    linarith [ht i]⟩

/-- Concentration and Bernoulli-supplied lower-pool properties hold in one
categorical outcome. This prevents combining separately chosen good samples.
No independence between pool properties or between good events is assumed. -/
theorem exists_counts_and_lower_properties {J : Type*} [Fintype J]
    (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i) (ht : ∀ i, 0 ≤ t i)
    (hbudget : ∑ i, (r i + t i) ≤ 1)
    (C : J → Finset (Category I)) (Q : J → Finset V)
    (a : ℝ) (ha : 0 < a) (P : I → Finset V → Prop) (δ : I → ℝ)
    (hP : ∀ i, (sampleMeasure V (lowerProbability r t hr ht hbudget i)).real
      {A | ¬ P i (sampleVertices A)} ≤ δ i)
    (hsmall : (Fintype.card J : ℝ) * (2 * exp (-a)) + ∑ i, δ i < 1) :
    ∃ ω : V → Category I,
      (∀ j, |(categoryCount (C j) (Q j) ω : ℝ) -
        (∑ c ∈ C j, categoryWeight r t c) * (Q j).card| <
        radius ((∑ c ∈ C j, categoryWeight r t c) * (Q j).card) a) ∧
      ∀ i, P i (lowerPool ω i) := by
  let E : J ⊕ I → Set (V → Category I) := Sum.elim
    (fun j => {ω | radius ((∑ c ∈ C j, categoryWeight r t c) * (Q j).card) a ≤
      |(categoryCount (C j) (Q j) ω : ℝ) - (∑ c ∈ C j, categoryWeight r t c) * (Q j).card|})
    (fun i => {ω | ¬ P i (lowerPool ω i)})
  have hj (j : J) : (poolLaw r t hr ht hbudget).real (E (Sum.inl j)) ≤ 2 * exp (-a) :=
    categoryCount_bernstein r t hr ht hbudget (C j) (Q j) a ha
  have hi (i : I) : (poolLaw r t hr ht hbudget).real (E (Sum.inr i)) ≤ δ i := by
    change (poolLaw r t hr ht hbudget).real {ω | ¬ P i (lowerPool ω i)} ≤ _
    rw [lowerPool_event_probability r t hr ht hbudget i
      (lowerProbability r t hr ht hbudget i) rfl (fun A => ¬ P i A)]
    exact hP i
  have hb : ∑ x ∈ (Finset.univ : Finset (J ⊕ I)),
      (poolLaw r t hr ht hbudget).real (E x) < 1 := by
    rw [Fintype.sum_sum_type]
    calc
      _ ≤ (∑ _j : J, 2 * exp (-a)) + ∑ i, δ i :=
        add_le_add (Finset.sum_le_sum (fun j _ => hj j))
          (Finset.sum_le_sum (fun i _ => hi i))
      _ = (Fintype.card J : ℝ) * (2 * exp (-a)) + ∑ i, δ i := by simp
      _ < 1 := hsmall
  obtain ⟨ω, hω⟩ := exists_avoiding_finite_events
    (μ := poolLaw r t hr ht hbudget) Finset.univ E hb
  refine ⟨ω, fun j => lt_of_not_ge (hω (Sum.inl j) (Finset.mem_univ _)), ?_⟩
  intro i
  exact not_not.mp (hω (Sum.inr i) (Finset.mem_univ _))

theorem pool_coordinates_independent (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (ht : ∀ i, 0 ≤ t i) (hbudget : ∑ i, (r i + t i) ≤ 1) :
    iIndepFun (fun v : V => fun ω : V → Category I => ω v)
      (poolLaw r t hr ht hbudget) :=
  iIndepFun_pi (X := fun _ : V => id) (fun _ => measurable_id.aemeasurable)

theorem pool_coordinate_marginal (r t : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (ht : ∀ i, 0 ≤ t i) (hbudget : ∑ i, (r i + t i) ≤ 1) (v : V) :
    (poolLaw r t hr ht hbudget).map (fun ω => ω v) =
      finiteLaw (categoryWeight r t) (categoryWeight_nonneg r t hr ht hbudget)
        (categoryWeight_sum r t) := by
  exact (measurePreserving_eval (fun _ : V => finiteLaw (categoryWeight r t)
    (categoryWeight_nonneg r t hr ht hbudget) (categoryWeight_sum r t)) v).map_eq

end Erdos585.Attempt6.CategoricalPools
