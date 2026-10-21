import Openmath.Attempt6.RandomRouting

/-! Original-graph source pool coupling: retained iid subset, independent
thinning, finite conditional averaging and monotone routing transfer. -/
noncomputable section
namespace Erdos585.Attempt6.SourcePools
open MeasureTheory ProbabilityTheory Finset Real
open OAI.ErdosGallai.Sampling
open RegularizationIteration RegularizationTransport CategoricalPools RandomRouting
attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

def mulProbability (p q : unitInterval) : unitInterval :=
  ⟨(p : ℝ) * (q : ℝ), mul_nonneg p.property.1 q.property.1, by
    nlinarith [p.property.1, p.property.2, q.property.1, q.property.2]⟩

def thin (A B : V → Bool) : V → Bool := fun v => A v && B v

lemma bool_and_law (p q : unitInterval) :
    ((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
      (fun x : Bool × Bool => x.1 && x.2) = bernoulliMeasure true false (mulProbability p q) := by
  haveI : IsProbabilityMeasure
      (((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
        (fun x : Bool × Bool => x.1 && x.2)) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable
  apply bool_measure_eq_bernoulli
  rw [Measure.real, Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  have he : {x : Bool × Bool | (x.1 && x.2) = true} =
      ({true} : Set Bool) ×ˢ ({true} : Set Bool) := by
    ext x
    rcases x with ⟨a, b⟩
    cases a <;> cases b <;> simp
  change (((bernoulliMeasure true false p).prod (bernoulliMeasure true false q))
    {x : Bool × Bool | (x.1 && x.2) = true}).toReal = _
  rw [he, Measure.prod_prod, ENNReal.toReal_mul]
  simp [bernoulliMeasure_real_apply, mulProbability]

/-- Actual independent Bernoulli thinning has the exact product density. -/
theorem thin_map (p q : unitInterval) :
    ((sampleMeasure V p).prod (sampleMeasure V q)).map
      (fun x => thin x.1 x.2) = sampleMeasure V (mulProbability p q) := by
  let μ : Measure (V → Bool × Bool) := Measure.pi
    (fun _ : V => (bernoulliMeasure true false p).prod (bernoulliMeasure true false q))
  have hi : iIndepFun (fun v : V => fun ω : V → Bool × Bool => ω v) μ :=
    iIndepFun_pi (X := fun _ : V => id) (fun _ => measurable_id.aemeasurable)
  have hj := hi.comp (fun _ : V => fun x : Bool × Bool => x.1 && x.2)
    (fun _ => measurable_of_finite _)
  change iIndepFun (fun v : V => fun ω : V → Bool × Bool => (ω v).1 && (ω v).2) μ at hj
  have hm : μ.map (fun ω v => (ω v).1 && (ω v).2) = sampleMeasure V (mulProbability p q) := by
    rw [hj.map_fun_eq_pi_map (fun _ => (measurable_of_finite _).aemeasurable)]
    unfold sampleMeasure
    congr 1
    funext v
    have he := (measurePreserving_eval
      (fun _ : V => (bernoulliMeasure true false p).prod (bernoulliMeasure true false q)) v).map_eq
    rw [← bool_and_law p q, ← he,
      Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
    rfl
  have hpair := (measurePreserving_arrowProdEquivProdArrow Bool Bool V
    (fun _ => bernoulliMeasure true false p) (fun _ => bernoulliMeasure true false q)).map_eq
  change μ.map (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool V) =
    (sampleMeasure V p).prod (sampleMeasure V q) at hpair
  rw [← hpair, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  exact hm

theorem thin_event_probability (p q : unitInterval) (P : (V → Bool) → Prop) :
    ((sampleMeasure V p).prod (sampleMeasure V q)).real {x | P (thin x.1 x.2)} =
      (sampleMeasure V (mulProbability p q)).real {A | P A} := by
  rw [← thin_map p q]
  simp only [Measure.real]
  rw [Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  rfl

/-- Routing is monotone in the reservoir: new outside terminal lists and loads
satisfy the smaller reservoir contract, and all paths retain their original edges. -/
theorem strongRoutingAt_mono (G : SimpleGraph V) {R S : Finset V} (hRS : R ⊆ S)
    (L D : ℝ) (hR : StrongRoutingAt G R L D) : StrongRoutingAt G S L D := by
  intro n terminal hout hdist hload
  obtain ⟨T, p, hp, hT, he⟩ := hR n terminal (fun i hi => hout i (hRS hi)) hdist
    (fun v hv => hload v (hRS hv))
  refine ⟨T, p, ?_, hT, he⟩
  intro i
  exact ⟨(hp i).1, (hp i).2.1.trans hRS, (hp i).2.2⟩

/-- Select one actual regularized graph and retained subset so that every
independently thinned retained subset has small conditional routing failure.
The hypotheses are unconditional laws on the original graph. -/
theorem exists_retained_with_thinning_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ) (Λ d L : ℝ) (hN : 2 ≤ N) (hcard : Fintype.card V ≤ N)
    (hΛ : 1 ≤ Λ) (hd : 0 ≤ d)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Λ * d)
    (q : I → unitInterval) (D δ η : I → ℝ) (hη : ∀ i, 0 < η i)
    (hroute : ∀ i,
      (sampleMeasure V (mulProbability (retentionProbability Λ hΛ) (q i))).real
        {B | ¬ StrongRoutingAt G (sampleVertices B) L (D i)} ≤ δ i)
    (hbudget : 1 / (N : ℝ) + ∑ i, δ i / η i < 1) :
    ∃ (H : G.Subgraph) (A : V → Bool),
      NearlyRegularGood G d (1000000 * Λ ^ 5) (100000 * Λ ^ 5 * log N) (H, A) ∧
      ∀ i, (sampleMeasure V (q i)).real
        {B | ¬ StrongRoutingAt G (sampleVertices (thin A B)) L (D i)} ≤ η i := by
  obtain ⟨ν, hν, hmap, hbad⟩ := exists_nearly_regular_bernoulli_coupling G N Λ d
    hN hcard hΛ hd hdeg
  letI := hν
  let f : I → State G → ℝ := fun i s => (sampleMeasure V (q i)).real
    {B | ¬ StrongRoutingAt G (sampleVertices (thin s.2 B)) L (D i)}
  have havg (i : I) : ∫ s, f i s ∂ν ≤ δ i := by
    have he : (∫ s, f i s ∂ν) =
        ∫ A : V → Bool, (sampleMeasure V (q i)).real
          {B | ¬ StrongRoutingAt G (sampleVertices (thin A B)) L (D i)}
            ∂sampleMeasure V (retentionProbability Λ hΛ) := by
      rw [← hmap]
      exact (integral_map (μ := ν)
        (measurable_of_finite (Prod.snd : State G → V → Bool)).aemeasurable
        (measurable_of_finite (fun A : V → Bool => (sampleMeasure V (q i)).real
          {B | ¬ StrongRoutingAt G (sampleVertices (thin A B)) L (D i)})).aestronglyMeasurable).symm
    have hF := finite_product_failure (sampleMeasure V (retentionProbability Λ hΛ))
      (sampleMeasure V (q i)) {x | ¬ StrongRoutingAt G
        (sampleVertices (thin x.1 x.2)) L (D i)}
    simp only [Set.mem_setOf_eq] at hF
    rw [he, ← hF, thin_event_probability (retentionProbability Λ hΛ) (q i)
      (fun B => ¬ StrongRoutingAt G (sampleVertices B) L (D i))]
    exact hroute i
  obtain ⟨s, hs, hf⟩ := exists_good_with_small_failures ν
    (NearlyRegularGood G d (1000000 * Λ ^ 5) (100000 * Λ ^ 5 * log N))
    f δ η (1 / N) (fun _ _ => measureReal_nonneg) hη havg hbad hbudget
  exact ⟨s.1, s.2, hs, hf⟩

lemma thin_sampleVertices (A B : V → Bool) :
    sampleVertices (thin A B) = sampleVertices A ∩ sampleVertices B := by
  ext v
  simp [sampleVertices, thin]

/-- Exact monotone coupling between two densities, with arbitrary fixed
supports. A categorical lower pool is contained in its upper pool pointwise. -/
theorem masked_failure_mono (U W : Finset V) (hUW : U ⊆ W)
    (p q : unitInterval) (hpq : (p : ℝ) ≤ q)
    (P : Finset V → Prop) (hP : Monotone P) :
    (sampleMeasure V q).real {B | ¬ P (W ∩ sampleVertices B)} ≤
      (sampleMeasure V p).real {B | ¬ P (U ∩ sampleVertices B)} := by
  let r : Unit → ℝ := fun _ => p
  let t : Unit → ℝ := fun _ => (q : ℝ) - p
  have hr : ∀ i, 0 ≤ r i := fun _ => p.property.1
  have ht : ∀ i, 0 ≤ t i := fun _ => sub_nonneg.mpr hpq
  have hb : ∑ i, (r i + t i) ≤ 1 := by simpa [r, t] using q.property.2
  let μ := poolLaw (V := V) r t hr ht hb
  have hl : μ.real {ω | ¬ P (U ∩ lowerPool ω ())} =
      (sampleMeasure V p).real {B | ¬ P (U ∩ sampleVertices B)} :=
    lowerPool_event_probability r t hr ht hb () p rfl (fun S => ¬ P (U ∩ S))
  have hm := poolProjection_map (V := V) r t hr ht hb (upperCategories ()) q
    (by simp [upperCategories_weight, r, t])
  have hu : μ.real {ω | ¬ P (W ∩ (lowerPool ω () ∪ bufferPool ω ()))} =
      (sampleMeasure V q).real {B | ¬ P (W ∩ sampleVertices B)} := by
    rw [← hm]
    simp only [Measure.real]
    rw [Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
    apply congrArg ENNReal.toReal
    congr 1
    ext ω
    simp [upperProjection_vertices]
  rw [← hu, ← hl]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hbad hgood
  exact hbad (hP (Finset.inter_subset_inter hUW Finset.subset_union_left) hgood)

/-- One selected original subgraph works for every larger sampling density
for every pool type. No robust expansion of the retained graph is asserted. -/
theorem exists_retained_with_larger_density_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ) (Λ d L : ℝ) (hN : 2 ≤ N) (hcard : Fintype.card V ≤ N)
    (hΛ : 1 ≤ Λ) (hd : 0 ≤ d)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Λ * d)
    (q : I → unitInterval) (D δ η : I → ℝ) (hη : ∀ i, 0 < η i)
    (hroute : ∀ i,
      (sampleMeasure V (mulProbability (retentionProbability Λ hΛ) (q i))).real
        {B | ¬ StrongRoutingAt G (sampleVertices B) L (D i)} ≤ δ i)
    (hbudget : 1 / (N : ℝ) + ∑ i, δ i / η i < 1) :
    ∃ (H : G.Subgraph) (A : V → Bool),
      NearlyRegularGood G d (1000000 * Λ ^ 5) (100000 * Λ ^ 5 * log N) (H, A) ∧
      ∀ i (p : unitInterval), (q i : ℝ) ≤ p →
        (sampleMeasure V p).real {B | ¬ StrongRoutingAt G
          (H.verts.toFinset ∩ sampleVertices B) L (D i)} ≤ η i := by
  obtain ⟨H, A, hgood, hcond⟩ := exists_retained_with_thinning_bounds G N Λ d L
    hN hcard hΛ hd hdeg q D δ η hη hroute hbudget
  refine ⟨H, A, hgood, ?_⟩
  intro i p hip
  have hsub : sampleVertices A ⊆ H.verts.toFinset := by
    intro v hv
    exact Set.mem_toFinset.mpr (hgood.1 v (by simpa [sampleVertices] using hv))
  have hm := masked_failure_mono (sampleVertices A) H.verts.toFinset hsub
    (q i) p hip (fun R => StrongRoutingAt G R L (D i))
    (fun _ _ h => strongRoutingAt_mono G h L (D i))
  apply hm.trans
  simpa only [thin_sampleVertices] using hcond i

theorem restriction_map {W : Type*} [Fintype W] (f : W ↪ V) (p : unitInterval) :
    (sampleMeasure V p).map (fun A w => A (f w)) = sampleMeasure W p := by
  have hi : iIndepFun (fun v : V => fun A : V → Bool => A v) (sampleMeasure V p) :=
    iIndepFun_pi (X := fun _ : V => id) (fun _ => measurable_id.aemeasurable)
  have hj := hi.precomp f.injective
  rw [hj.map_fun_eq_pi_map (fun _ => (measurable_of_finite _).aemeasurable)]
  unfold sampleMeasure
  congr 1
  funext w
  exact (measurePreserving_eval (fun _ : V => bernoulliMeasure true false p) (f w)).map_eq

def retainedEmbedding (G : SimpleGraph V) (H : G.Subgraph) : H.verts ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

lemma retained_sample_map (G : SimpleGraph V) (H : G.Subgraph) (A : V → Bool) :
    (sampleVertices (fun v : H.verts => A v)).map (retainedEmbedding G H) =
      H.verts.toFinset ∩ sampleVertices A := by
  ext v
  simp only [Finset.mem_map, sampleVertices, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_inter, Set.mem_toFinset]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hv, hA⟩
    exact ⟨⟨v, hv⟩, hA, rfl⟩

/-- Sampling on the actual retained support has exactly the same law as
restricting an ambient iid sample. This identifies the consumer probability. -/
theorem retained_event_probability (G : SimpleGraph V) (H : G.Subgraph)
    (p : unitInterval) (P : Finset V → Prop) :
    (sampleMeasure H.verts p).real
      {B | P ((sampleVertices B).map (retainedEmbedding G H))} =
    (sampleMeasure V p).real {A | P (H.verts.toFinset ∩ sampleVertices A)} := by
  rw [← restriction_map (retainedEmbedding G H) p]
  simp only [Measure.real]
  rw [Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  apply congrArg ENNReal.toReal
  congr 1
  ext A
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  change P ((sampleVertices (fun v : H.verts => A v)).map (retainedEmbedding G H)) ↔ _
  rw [retained_sample_map]

/-- Degree control of the actual graph on the retained vertex type is inherited
from the original-subgraph degree window without adding isolated ambient vertices. -/
theorem retained_degree_window (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : G.Subgraph) (d M : ℝ) (h : DegreeWindow G H d M) :
    ∀ v : H.verts, d ≤ (H.coe.degree v : ℝ) ∧ (H.coe.degree v : ℝ) ≤ M := by
  intro v
  simpa only [SimpleGraph.Subgraph.coe_degree, SimpleGraph.Subgraph.degree_spanningCoe]
    using h v v.property

/-- Actual original-graph regularization and strong-routing supplier for any
finite pool family. All random routing estimates are instantiated from the
checked robust-expander theorem at the independently thinned seed density. -/
theorem exists_retained_source_routing (G : SimpleGraph V) [DecidableRel G.Adj]
    (d L s : ℝ) (hd : 0 < d) (hL : (10 : ℝ) ^ 30 ≤ L)
    (hN : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ 18 * d)
    (hsdegree : d / L ^ 2 ≤ s) (hG : RobustCore.RobustExpanderAt G L (1 / 32) s)
    (q : I → unitInterval) (η : I → ℝ) (hη : ∀ i, 0 < η i)
    (hq : ∀ i, 0 < (q i : ℝ))
    (hseeddegree : ∀ i, 2560 * L ≤
      (mulProbability (retentionProbability 18 (by norm_num)) (q i) : ℝ) * d)
    (hseedrobust : ∀ i,
      (((qProbability (mulProbability (retentionProbability 18 (by norm_num)) (q i)) :
        unitInterval) : ℝ)⁻¹) ^ 4 * L ^ 30 ≤ s)
    (hbudget : 1 / (Fintype.card V : ℝ) +
      ∑ i, (2 / (Fintype.card V : ℝ)) / η i < 1) :
    ∃ (H : G.Subgraph) (A : V → Bool),
      NearlyRegularGood G d (1000000 * (18 : ℝ) ^ 5)
        (100000 * (18 : ℝ) ^ 5 * log (Fintype.card V)) (H, A) ∧
      ∀ i (p : unitInterval), (q i : ℝ) ≤ p →
        (sampleMeasure H.verts p).real {B | ¬ StrongRoutingAt G
          ((sampleVertices B).map (retainedEmbedding G H)) L
          ((mulProbability (retentionProbability 18 (by norm_num)) (q i) : ℝ) ^ 8 * d / L ^ 75)} ≤ η i := by
  let ρ := retentionProbability 18 (by norm_num)
  have hρ : 0 < (ρ : ℝ) := by norm_num [ρ, retentionProbability]
  have hr (i : I) := bernoulli_source_strongRouting_failure G (mulProbability ρ (q i))
    (show 0 < (mulProbability ρ (q i) : ℝ) from mul_pos hρ (hq i))
    d (18 * d) L s hd le_rfl hL hN hlog (fun v => (hdeg v).1)
    (fun v => (hdeg v).2) (hseeddegree i) hsdegree (hseedrobust i) hG
  obtain ⟨H, A, hgood, hroute⟩ := exists_retained_with_larger_density_bounds G
    (Fintype.card V) 18 d L hN le_rfl (by norm_num) hd.le hdeg q
    (fun i => (mulProbability ρ (q i) : ℝ) ^ 8 * d / L ^ 75)
    (fun _ => 2 / (Fintype.card V : ℝ)) η hη hr hbudget
  refine ⟨H, A, hgood, ?_⟩
  intro i p hip
  rw [retained_event_probability G H p (fun R => ¬ StrongRoutingAt G R L
    ((mulProbability ρ (q i) : ℝ) ^ 8 * d / L ^ 75))]
  exact hroute i p hip

def ambientNeighbors (G : SimpleGraph V) (H : G.Subgraph) (v : V) : Finset H.verts :=
  Finset.univ.filter (fun w => G.Adj v w)

lemma ambient_degree_count (G : SimpleGraph V) (H : G.Subgraph)
    (S : Finset H.verts) (v : V) :
    graphDegreeInto G (S.map (retainedEmbedding G H)) v = (S ∩ ambientNeighbors G H v).card := by
  unfold graphDegreeInto
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  ext w
  constructor
  · intro hw
    obtain ⟨hwS, hadj⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_inter.mpr ⟨hwS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩⟩
  · intro hw
    obtain ⟨hwS, hwN⟩ := Finset.mem_inter.mp hw
    exact Finset.mem_filter.mpr ⟨hwS, (Finset.mem_filter.mp hwN).2⟩

/-- Actual balanced original-graph source pools on one retained support.
All assumptions after the routing law are explicit finite probability budgets
or inequalities between numerical means and radii, never successful samples.
The retained error is exactly Ksqrt(q_iL), and ambient bounds hold at every
original center, including centers outside the retained support. -/
theorem retained_balanced_source_pools [DecidableEq I]
    (G : SimpleGraph V) (H : G.Subgraph) (Q : Finset H.verts) (m : I → ℕ)
    (r t q D M η : I → ℝ) (L K a : ℝ)
    (hr : ∀ i, 0 ≤ r i) (ht : ∀ i, 0 ≤ t i)
    (hcat : ∑ i, (r i + t i) ≤ 1) (ha : 0 < a)
    (hroute : ∀ i, (sampleMeasure H.verts (lowerProbability r t hr ht hcat i)).real
      {B | ¬ StrongRoutingAt G ((sampleVertices B).map (retainedEmbedding G H)) L (D i)} ≤ η i)
    (hbudget : (Fintype.card (I × Bool × (Bool ⊕ (H.verts ⊕ V))) : ℝ) *
      (2 * exp (-a)) + ∑ i, η i < 1)
    (hshore : ∀ i b,
      r i * (shore Q b).card + radius (r i * (shore Q b).card) a ≤ m i ∧
      (m i : ℝ) ≤ (r i + t i) * (shore Q b).card - radius ((r i + t i) * (shore Q b).card) a)
    (hretained : ∀ i (v : H.verts),
      q i - K * sqrt (q i * L) ≤ r i * H.coe.degree v - radius (r i * H.coe.degree v) a ∧
      (r i + t i) * H.coe.degree v + radius ((r i + t i) * H.coe.degree v) a ≤
        q i + K * sqrt (q i * L))
    (hambient : ∀ i v,
      (r i + t i) * (ambientNeighbors G H v).card +
        radius ((r i + t i) * (ambientNeighbors G H v).card) a ≤ M i) :
    ∃ S : I → Finset H.verts,
      (∀ i, (S i ∩ Q).card = m i ∧ (S i ∩ Qᶜ).card = m i ∧ (S i).card = 2 * m i) ∧
      Pairwise (fun i j => Disjoint ((S i).map (retainedEmbedding G H))
        ((S j).map (retainedEmbedding G H))) ∧
      (∀ i v, |(graphDegreeInto H.coe (S i) v : ℝ) - q i| ≤ K * sqrt (q i * L)) ∧
      (∀ i v, (graphDegreeInto G ((S i).map (retainedEmbedding G H)) v : ℝ) ≤ M i) ∧
      ∀ i, StrongRoutingAt G ((S i).map (retainedEmbedding G H)) L (D i) := by
  let J := I × Bool × (Bool ⊕ (H.verts ⊕ V))
  let N : H.verts ⊕ V → Finset H.verts :=
    Sum.elim (fun v => H.coe.neighborFinset v) (ambientNeighbors G H)
  let C : J → Finset (Category I) := fun x => selectedCategories x.1 x.2.1
  let A : J → Finset H.verts := fun x => Sum.elim (shore Q) N x.2.2
  let P : I → Finset H.verts → Prop := fun i S =>
    StrongRoutingAt G (S.map (retainedEmbedding G H)) L (D i)
  obtain ⟨ω, hcounts, hP⟩ := exists_counts_and_lower_properties r t hr ht hcat C A a ha P η
    hroute hbudget
  have hc (i : I) (b : Bool) (B : Bool ⊕ (H.verts ⊕ V)) :
      |((selectedPool ω i b ∩ Sum.elim (shore Q) N B).card : ℝ) -
        selectedRate r t i b * (Sum.elim (shore Q) N B).card| <
        radius (selectedRate r t i b * (Sum.elim (shore Q) N B).card) a := by
    simpa [C, A, selectedCategories_count, selectedCategories_weight] using hcounts (i, b, B)
  have hs (i : I) (b : Bool) : (lowerPool ω i ∩ shore Q b).card ≤ m i ∧
      m i ≤ ((lowerPool ω i ∪ bufferPool ω i) ∩ shore Q b).card := by
    have hl := hc i false (Sum.inl b)
    have hu := hc i true (Sum.inl b)
    simp only [Sum.elim_inl, selectedPool, selectedRate, Bool.false_eq_true, if_false, if_true] at hl hu
    have hln : ((lowerPool ω i ∩ shore Q b).card : ℝ) ≤ m i := by
      linarith [(abs_lt.mp hl).2, (hshore i b).1]
    have hun : (m i : ℝ) ≤ ((lowerPool ω i ∪ bufferPool ω i) ∩ shore Q b).card := by
      linarith [(abs_lt.mp hu).1, (hshore i b).2]
    exact ⟨by exact_mod_cast hln, by exact_mod_cast hun⟩
  obtain ⟨S, hS, hdis⟩ := exists_pairwise_disjoint_balanced_completion
    (lowerPool ω) (bufferPool ω) Q m (pools_disjoint ω) (fun i =>
      ⟨by simpa [shore] using hs i false, by simpa [shore] using hs i true⟩)
  have henvelope (i : I) (j : H.verts ⊕ V) :
      r i * (N j).card - radius (r i * (N j).card) a ≤ (S i ∩ N j).card ∧
      ((S i ∩ N j).card : ℝ) ≤ (r i + t i) * (N j).card + radius ((r i + t i) * (N j).card) a :=
    completion_count_bounds ω i (S i) (N j) (hS i).1 (hS i).2.1 (r i) (t i) a
      (by simpa [selectedPool, selectedRate] using hc i false (Sum.inr j))
      (by simpa [selectedPool, selectedRate] using hc i true (Sum.inr j))
  refine ⟨S, fun i => (hS i).2.2, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [Finset.disjoint_left]
    intro v hi hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨y, hy, he⟩ := Finset.mem_map.mp hj
    have hyx := (retainedEmbedding G H).injective he
    subst y
    exact Finset.disjoint_left.mp (hdis hij) hx hy
  · intro i v
    have he := henvelope i (Sum.inl v)
    have hcount : graphDegreeInto H.coe (S i) v = (S i ∩ N (Sum.inl v)).card := by
      unfold graphDegreeInto
      congr 1
      ext w
      simp [N]
    rw [← hcount] at he
    simp only [N, Sum.elim_inl, SimpleGraph.card_neighborFinset_eq_degree] at he
    have hlow := (hretained i v).1.trans he.1
    have hupper := he.2.trans (hretained i v).2
    exact abs_le.mpr ⟨by linarith only [hlow], by linarith only [hupper]⟩
  · intro i v
    rw [ambient_degree_count]
    exact (henvelope i (Sum.inr v)).2.trans (hambient i v)
  · intro i
    exact strongRoutingAt_mono G (Finset.map_subset_map.mpr (hS i).1) L (D i) (hP i)

lemma radius_le_thirty_sqrt (M q L : ℝ) (hM : 0 ≤ M) (hMq : M ≤ 2 * q)
    (hL : 0 ≤ L) (hLq : L ≤ q) : radius M (10 * L) ≤ 30 * sqrt (q * L) := by
  have hq := hL.trans hLq
  have hs := sq_sqrt (mul_nonneg hq hL)
  have hs0 := sqrt_nonneg (q * L)
  have ht := sq_sqrt (show 0 ≤ M * (10 * L) by positivity)
  have ht0 := sqrt_nonneg (M * (10 * L))
  have hLs : L ≤ sqrt (q * L) := by
    nlinarith [mul_le_mul_of_nonneg_right hLq hL]
  have hroot : sqrt (M * (10 * L)) ≤ 5 * sqrt (q * L) := by
    nlinarith [mul_le_mul_of_nonneg_right hMq (show 0 ≤ 10 * L by positivity)]
  unfold radius
  nlinarith

/-- Exact degree mean calculations for the source rates, including both the
regularization error and the balancing margin. -/
theorem source_degree_means (n d m z w k : ℝ) (hn : 0 < n) (hd : 0 ≤ d)
    (hm : 0 ≤ m) (hz : 0 ≤ z) (hzsmall : z ≤ 1 / 20)
    (hw : 0 ≤ w) (hwsmall : w ≤ m / 10)
    (hk : d * (1 - z) ≤ k ∧ k ≤ d * (1 + z)) :
    2 * d * m / n - 6 * d * z * m / n - d * w / n ≤ sourceLowerRate n m z w * k ∧
    (sourceLowerRate n m z w + sourceBufferRate n m z w) * k ≤
      2 * d * m / n + 10 * d * z * m / n + 2 * d * w / n ∧
    0 ≤ sourceLowerRate n m z w * k ∧
    0 ≤ (sourceLowerRate n m z w + sourceBufferRate n m z w) * k ∧
    sourceLowerRate n m z w * k ≤ 2 * (2 * d * m / n) ∧
    (sourceLowerRate n m z w + sourceBufferRate n m z w) * k ≤ 2 * (2 * d * m / n) := by
  have hzm : z * m ≤ m / 20 := by nlinarith [mul_le_mul_of_nonneg_right hzsmall hm]
  have hzd : z * d ≤ d / 20 := by nlinarith [mul_le_mul_of_nonneg_right hzsmall hd]
  have hk0 : 0 ≤ k := by nlinarith [hk.1]
  have hrn : 0 ≤ 2 * m - 4 * z * m - w := by nlinarith
  have hun : 0 ≤ 2 * m + 6 * z * m + w := by positivity
  have hlo := mul_le_mul_of_nonneg_left hk.1 hrn
  have hhi := mul_le_mul_of_nonneg_left hk.2 hun
  have hpositive : 0 ≤ d * (4 * z ^ 2 * m + z * w) := by positivity
  have hpositive2 : 0 ≤ d * (z * m * (2 - 6 * z) + w * (1 - z)) := by
    have h2 : 0 ≤ 2 - 6 * z := by linarith
    have h1 : 0 ≤ 1 - z := by linarith
    positivity
  have hloNum : 2 * d * m - 6 * d * z * m - d * w ≤ (2 * m - 4 * z * m - w) * k := by
    nlinarith
  have hhiNum : (2 * m + 6 * z * m + w) * k ≤ 2 * d * m + 10 * d * z * m + 2 * d * w := by
    nlinarith
  have hUnum : 2 * m + 6 * z * m + w ≤ 3 * m := by nlinarith
  have hkbound : k ≤ 4 * d / 3 := by nlinarith [hk.2]
  have hmeanNum : (2 * m + 6 * z * m + w) * k ≤ 4 * d * m := by
    have hh := mul_le_mul hUnum hkbound hk0 (show 0 ≤ 3 * m by positivity)
    nlinarith
  have hlowNum : (2 * m - 4 * z * m - w) * k ≤ (2 * m + 6 * z * m + w) * k := by
    apply mul_le_mul_of_nonneg_right _ hk0
    nlinarith [mul_nonneg hz hm]
  have hlowmean := div_le_div_of_nonneg_right (hlowNum.trans hmeanNum) hn.le
  have huppermean := div_le_div_of_nonneg_right hmeanNum hn.le
  have hloDiv := div_le_div_of_nonneg_right hloNum hn.le
  have hhiDiv := div_le_div_of_nonneg_right hhiNum hn.le
  rw [source_total_rate]
  unfold sourceLowerRate
  constructor
  · ring_nf at hloDiv ⊢
    exact hloDiv
  constructor
  · ring_nf at hhiDiv ⊢
    exact hhiDiv
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · ring_nf at hlowmean ⊢
    exact hlowmean
  · ring_nf at huppermean ⊢
    exact huppermean

lemma dense_balancing_charge (n d m L : ℝ) (hn : 0 < n) (hd : 0 ≤ d)
    (hdn : d ≤ 2 * n) (hm : 0 ≤ m) (hL : 0 ≤ L) :
    d * (100 * sqrt (m * L)) / n ≤ 100 * sqrt ((2 * d * m / n) * L) := by
  let b := d / n
  have hb : 0 ≤ b := div_nonneg hd hn.le
  have hb2 : b ≤ 2 := (div_le_iff₀ hn).mpr (by nlinarith)
  have he : 2 * d * m / n = 2 * b * m := by dsimp [b]; ring
  rw [he]
  have hs := sq_sqrt (mul_nonneg hm hL)
  have ht := sq_sqrt (show 0 ≤ 2 * b * m * L by positivity)
  have hs0 := sqrt_nonneg (m * L)
  have ht0 := sqrt_nonneg (2 * b * m * L)
  have hcharge : 0 ≤ b * (2 - b) * (m * L) := by positivity
  have hroot : b * sqrt (m * L) ≤ sqrt (2 * b * m * L) := by
    have hsq : (b * sqrt (m * L)) ^ 2 ≤ (sqrt (2 * b * m * L)) ^ 2 := by
      rw [mul_pow, hs, ht]
      nlinarith only [hcharge]
    have hbroot : 0 ≤ b * sqrt (m * L) := mul_nonneg hb hs0
    nlinarith
  calc
    d * (100 * sqrt (m * L)) / n = 100 * (b * sqrt (m * L)) := by dsimp [b]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hroot (by norm_num)

/-- Full source retained-degree calibration. The constant10C+240 pays the
regularization error, dense-graph balancing error and actual Bernstein radius. -/
theorem source_degree_envelope (n d m C L k : ℝ) (hn : 0 < n) (hd : 0 < d)
    (hm : 0 ≤ m) (hC : 0 ≤ C) (hL : 0 ≤ L) (hdn : d ≤ 2 * n) (hmn : m ≤ n)
    (hlarge : 1000000 * L ≤ m) (hzsmall : C * L / d ≤ 1 / 20)
    (hqL : L ≤ 2 * d * m / n) (hk : d - C * L ≤ k ∧ k ≤ d + C * L) :
    let q := 2 * d * m / n
    let r := sourceLowerRate n m (C * L / d) (100 * sqrt (m * L))
    let t := sourceBufferRate n m (C * L / d) (100 * sqrt (m * L))
    q - (10 * C + 240) * sqrt (q * L) ≤ r * k - radius (r * k) (10 * L) ∧
      (r + t) * k + radius ((r + t) * k) (10 * L) ≤ q + (10 * C + 240) * sqrt (q * L) := by
  dsimp only
  let z := C * L / d
  let w := 100 * sqrt (m * L)
  let q := 2 * d * m / n
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hwsmall : w ≤ m / 10 := source_sqrt_margin_small m L hm hL hlarge
  have hdz : d * z = C * L := by dsimp [z]; field_simp
  have hkz : d * (1 - z) ≤ k ∧ k ≤ d * (1 + z) := by
    constructor <;> nlinarith [hk.1, hk.2]
  have hb := source_degree_means n d m z w k hn hd.le hm hz hzsmall hw hwsmall hkz
  have hradius := radius_le_thirty_sqrt _ q L hb.2.2.1 hb.2.2.2.2.1 hL hqL
  have huradius := radius_le_thirty_sqrt _ q L hb.2.2.2.1 hb.2.2.2.2.2 hL hqL
  have hwcharge : d * w / n ≤ 100 * sqrt (q * L) := dense_balancing_charge n d m L hn hd.le hdn hm hL
  have hroot0 := sqrt_nonneg (q * L)
  have hq0 : 0 ≤ q := hL.trans hqL
  have hLroot : L ≤ sqrt (q * L) := by
    have hs := sq_sqrt (mul_nonneg hq0 hL)
    nlinarith [mul_le_mul_of_nonneg_right hqL hL]
  have hfrac : m / n ≤ 1 := (div_le_one hn).mpr hmn
  have hreg : d * z * m / n ≤ C * sqrt (q * L) := calc
    d * z * m / n = C * L * (m / n) := by rw [hdz]; ring
    _ ≤ C * L := by
      have hh := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hC hL)
      simpa using hh
    _ ≤ _ := mul_le_mul_of_nonneg_left hLroot hC
  have hreg6 : 6 * d * z * m / n ≤ 6 * C * sqrt (q * L) := by
    have hh := mul_le_mul_of_nonneg_left hreg (show (0 : ℝ) ≤ 6 by norm_num)
    ring_nf at hh ⊢
    exact hh
  have hreg10 : 10 * d * z * m / n ≤ 10 * C * sqrt (q * L) := by
    have hh := mul_le_mul_of_nonneg_left hreg (show (0 : ℝ) ≤ 10 by norm_num)
    ring_nf at hh ⊢
    exact hh
  have hwcharge2 : 2 * d * w / n ≤ 200 * sqrt (q * L) := by
    have hh := mul_le_mul_of_nonneg_left hwcharge (show (0 : ℝ) ≤ 2 by norm_num)
    ring_nf at hh ⊢
    exact hh
  change q - _ ≤ _ ∧ _ ≤ q + _
  constructor
  · nlinarith [hb.1, mul_nonneg hC hroot0]
  · nlinarith [hb.2.1]

/-- Only finite scalar obligations remain in this record. In particular it
contains no probabilistic success assumption, graph output or routing witness. -/
structure PoolScalarBounds [DecidableEq I] (G : SimpleGraph V) (H : G.Subgraph)
    (Q : Finset H.verts) (m : I → ℕ) (r t q M η : I → ℝ) (L K a : ℝ) : Prop where
  lower_nonneg : ∀ i, 0 ≤ r i
  buffer_nonneg : ∀ i, 0 ≤ t i
  category_budget : ∑ i, (r i + t i) ≤ 1
  parameter_pos : 0 < a
  tail_budget : (Fintype.card (I × Bool × (Bool ⊕ (H.verts ⊕ V))) : ℝ) *
    (2 * exp (-a)) + ∑ i, η i < 1
  shore_margins : ∀ i b,
    r i * (shore Q b).card + radius (r i * (shore Q b).card) a ≤ m i ∧
    (m i : ℝ) ≤ (r i + t i) * (shore Q b).card - radius ((r i + t i) * (shore Q b).card) a
  retained_margins : ∀ i (v : H.verts),
    q i - K * sqrt (q i * L) ≤ r i * H.coe.degree v - radius (r i * H.coe.degree v) a ∧
    (r i + t i) * H.coe.degree v + radius ((r i + t i) * H.coe.degree v) a ≤
      q i + K * sqrt (q i * L)
  ambient_margins : ∀ i v,
    (r i + t i) * (ambientNeighbors G H v).card +
      radius ((r i + t i) * (ambientNeighbors G H v).card) a ≤ M i

def HasSourcePools (G : SimpleGraph V) (H : G.Subgraph) (Q : Finset H.verts)
    (m : I → ℕ) (q D M : I → ℝ) (L K : ℝ) : Prop :=
  ∃ S : I → Finset H.verts,
    (∀ i, (S i ∩ Q).card = m i ∧ (S i ∩ Qᶜ).card = m i ∧ (S i).card = 2 * m i) ∧
    Pairwise (fun i j => Disjoint ((S i).map (retainedEmbedding G H))
      ((S j).map (retainedEmbedding G H))) ∧
    (∀ i v, |(graphDegreeInto H.coe (S i) v : ℝ) - q i| ≤ K * sqrt (q i * L)) ∧
    (∀ i v, (graphDegreeInto G ((S i).map (retainedEmbedding G H)) v : ℝ) ≤ M i) ∧
    ∀ i, StrongRoutingAt G ((S i).map (retainedEmbedding G H)) L (D i)

theorem source_pools_of_scalars [DecidableEq I]
    (G : SimpleGraph V) (H : G.Subgraph) (Q : Finset H.verts) (m : I → ℕ)
    (r t q D M η : I → ℝ) (L K a : ℝ)
    (h : PoolScalarBounds G H Q m r t q M η L K a)
    (hroute : ∀ i, (sampleMeasure H.verts
      (lowerProbability r t h.lower_nonneg h.buffer_nonneg h.category_budget i)).real
        {B | ¬ StrongRoutingAt G ((sampleVertices B).map (retainedEmbedding G H)) L (D i)} ≤ η i) :
    HasSourcePools G H Q m q D M L K :=
  retained_balanced_source_pools G H Q m r t q D M η L K a
    h.lower_nonneg h.buffer_nonneg h.category_budget h.parameter_pos hroute
    h.tail_budget h.shore_margins h.retained_margins h.ambient_margins

def seedDensity (p : unitInterval) : unitInterval :=
  mulProbability (retentionProbability 18 (by norm_num)) p
def seedCapacity (d L : ℝ) (p : unitInterval) : ℝ := (seedDensity p : ℝ) ^ 8 * d / L ^ 75

/-- The original graph supplies ONE actual retained nearly-regular subgraph
that supports every five-pool construction satisfying the explicit scalar
conditions. The independent seed densities are fixed before selecting H;
the final pool rates may depend on H and may be larger than those densities. -/
theorem exists_five_original_source_pool_supplier
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d L s : ℝ) (hd : 0 < d) (hL : (10 : ℝ) ^ 30 ≤ L)
    (hN : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ 18 * d)
    (hsdegree : d / L ^ 2 ≤ s) (hG : RobustCore.RobustExpanderAt G L (1 / 32) s)
    (pmin : Fin 5 → unitInterval) (η : Fin 5 → ℝ) (hη : ∀ i, 0 < η i)
    (hpmin : ∀ i, 0 < (pmin i : ℝ))
    (hseeddegree : ∀ i, 2560 * L ≤ (seedDensity (pmin i) : ℝ) * d)
    (hseedrobust : ∀ i, (((qProbability (seedDensity (pmin i)) : unitInterval) : ℝ)⁻¹) ^ 4 * L ^ 30 ≤ s)
    (hbudget : 1 / (Fintype.card V : ℝ) +
      ∑ i, (2 / (Fintype.card V : ℝ)) / η i < 1) :
    ∃ (H : G.Subgraph) (A : V → Bool),
      NearlyRegularGood G d (1000000 * (18 : ℝ) ^ 5)
        (100000 * (18 : ℝ) ^ 5 * log (Fintype.card V)) (H, A) ∧
      ∀ (Q : Finset H.verts) (m : Fin 5 → ℕ) (r t q M : Fin 5 → ℝ) (K a : ℝ),
        (∀ i, (pmin i : ℝ) ≤ r i) →
        PoolScalarBounds G H Q m r t q M η L K a →
        HasSourcePools G H Q m q (fun i => seedCapacity d L (pmin i)) M L K := by
  obtain ⟨H, A, hgood, hroute⟩ := exists_retained_source_routing G d L s hd hL hN hlog
    hdeg hsdegree hG pmin η hη hpmin hseeddegree hseedrobust hbudget
  refine ⟨H, A, hgood, ?_⟩
  intro Q m r t q M K a hmin hscalars
  apply source_pools_of_scalars G H Q m r t q _ M η L K a hscalars
  intro i
  exact hroute i (lowerProbability r t hscalars.lower_nonneg hscalars.buffer_nonneg
    hscalars.category_budget i) (hmin i)

lemma ambientNeighbors_card_le_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : G.Subgraph) (v : V) : (ambientNeighbors G H v).card ≤ G.degree v := by
  calc
    (ambientNeighbors G H v).card =
        graphDegreeInto G ((Finset.univ : Finset H.verts).map (retainedEmbedding G H)) v := by
      rw [ambient_degree_count]
      simp
    _ ≤ Nat.card (G.neighborSet v) := graphDegreeInto_le_neighborCard G _ v
    _ = G.degree v := by rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]

lemma radius_mono (x y a : ℝ) (hxy : x ≤ y) (ha : 0 ≤ a) : radius x a ≤ radius y a := by
  unfold radius
  have hs := sqrt_le_sqrt (mul_le_mul_of_nonneg_right hxy ha)
  have hh := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 2 by norm_num)
  exact add_le_add hh le_rfl

set_option maxHeartbeats 800000 in
/-- Source rates discharge all retained/ambient mean-radius obligations.
The remaining hypotheses are finite size and shore inequalities plus the
explicit union budget. Ambient control uses the ORIGINAL degree upper bound. -/
theorem source_scalar_bounds [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : G.Subgraph)
    (Q : Finset H.verts) (m : I → ℕ) (η : I → ℝ) (d C L Δ : ℝ)
    (hn : 0 < (Fintype.card H.verts : ℝ)) (hd : 0 < d) (hC : 0 ≤ C) (hL : 0 < L)
    (hdn : d ≤ 2 * (Fintype.card H.verts : ℝ))
    (hzsmall : C * L / d ≤ 1 / 20)
    (hlarge : ∀ i, 1000000 * L ≤ m i)
    (hsize : ∑ i, (3 * m i : ℝ) ≤ Fintype.card H.verts)
    (hqL : ∀ i, L ≤ 2 * d * m i / Fintype.card H.verts)
    (hnear : ∀ v : H.verts, d - C * L ≤ (H.coe.degree v : ℝ) ∧ (H.coe.degree v : ℝ) ≤ d + C * L)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ)
    (hshore : ∀ b, (Fintype.card H.verts : ℝ) * (1 / 2 - C * L / d) ≤ (shore Q b).card ∧
      ((shore Q b).card : ℝ) ≤ (Fintype.card H.verts : ℝ) * (1 / 2 + C * L / d))
    (htail : (Fintype.card (I × Bool × (Bool ⊕ (H.verts ⊕ V))) : ℝ) *
      (2 * exp (-(10 * L))) + ∑ i, η i < 1) :
    let n : ℝ := Fintype.card H.verts
    let r := fun i => sourceLowerRate n (m i) (C * L / d) (100 * sqrt (m i * L))
    let t := fun i => sourceBufferRate n (m i) (C * L / d) (100 * sqrt (m i * L))
    let q := fun i => 2 * d * m i / n
    let M := fun i => 3 * m i * Δ / n + radius (3 * m i * Δ / n) (10 * L)
    PoolScalarBounds G H Q m r t q M η L (10 * C + 240) (10 * L) := by
  dsimp only
  let n : ℝ := Fintype.card H.verts
  let z := C * L / d
  let w := fun i => 100 * sqrt ((m i : ℝ) * L)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hw (i : I) : 0 ≤ w i := by dsimp [w]; positivity
  have hws (i : I) : w i ≤ m i / 10 :=
    source_sqrt_margin_small (m i) L (Nat.cast_nonneg _) hL.le (hlarge i)
  have hv := source_rates_valid n z (fun i => (m i : ℝ)) w hn hz hzsmall
    (fun _ => Nat.cast_nonneg _) hw hws hsize
  have hmn (i : I) : (m i : ℝ) ≤ n := by
    have hh : (3 * m i : ℝ) ≤ ∑ j, (3 * m j : ℝ) :=
      Finset.single_le_sum (f := fun j : I => (3 * (m j : ℝ)))
        (fun _ _ => by positivity) (Finset.mem_univ i)
    have hm0 : (0 : ℝ) ≤ m i := Nat.cast_nonneg _
    change (m i : ℝ) ≤ (Fintype.card H.verts : ℝ)
    linarith
  refine ⟨hv.1, hv.2.1, hv.2.2, by positivity, htail, ?_, ?_, ?_⟩
  · intro i b
    exact source_shore_balancing_margins n (m i) z L (shore Q b).card hn
      (Nat.cast_nonneg _) hz hzsmall hL.le (hlarge i) (Nat.cast_nonneg _)
      (hshore b).1 (hshore b).2
  · intro i v
    have hh := source_degree_envelope n d (m i) C L (H.coe.degree v) hn hd
      (Nat.cast_nonneg _) hC hL.le hdn (hmn i) (hlarge i) hzsmall (hqL i) (hnear v)
    simpa only [n, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hh
  · intro i v
    have hrate : sourceLowerRate n (m i) z (w i) + sourceBufferRate n (m i) z (w i) ≤
        3 * m i / n := by
      rw [source_total_rate]
      apply div_le_div_of_nonneg_right _ hn.le
      have hzm := mul_le_mul_of_nonneg_right hzsmall (show (0 : ℝ) ≤ m i by positivity)
      have hm0 : (0 : ℝ) ≤ m i := Nat.cast_nonneg _
      nlinarith [hws i]
    have hcard : ((ambientNeighbors G H v).card : ℝ) ≤ Δ :=
      (show ((ambientNeighbors G H v).card : ℝ) ≤ G.degree v by
        exact_mod_cast ambientNeighbors_card_le_degree G H v).trans (hdeg v)
    have hmean : (sourceLowerRate n (m i) z (w i) + sourceBufferRate n (m i) z (w i)) *
        (ambientNeighbors G H v).card ≤ 3 * m i * Δ / n := by
      have hh := mul_le_mul hrate hcard (Nat.cast_nonneg _)
        (show 0 ≤ (3 * m i : ℝ) / n by positivity)
      ring_nf at hh ⊢
      exact hh
    exact add_le_add hmean (radius_mono _ _ _ hmean (by positivity))

/-- The source lower rate dominates a density fixed using the original order.
This permits choosing the seed before learning the random retained graph. -/
theorem source_lower_ge_original_density (N n m z L : ℝ)
    (hn : 0 < n) (hnN : n ≤ N) (hm : 0 ≤ m) (hL : 0 ≤ L)
    (hz : z ≤ 1 / 20) (hlarge : 1000000 * L ≤ m) :
    m / N ≤ sourceLowerRate n m z (100 * sqrt (m * L)) := by
  have hw := source_sqrt_margin_small m L hm hL hlarge
  have hzm := mul_le_mul_of_nonneg_right hz hm
  have hnum : m ≤ 2 * m - 4 * z * m - 100 * sqrt (m * L) := by nlinarith
  calc
    m / N ≤ m / n := div_le_div_of_nonneg_left hm hn hnN
    _ ≤ _ := div_le_div_of_nonneg_right hnum hn.le

/-- The exact retained-subset marginal pays a linear retained-order bound.
The graph and its subset need not be independent. -/
theorem retained_order_bad_bound (G : SimpleGraph V)
    (ν : Measure (State G)) [IsProbabilityMeasure ν] (p : unitInterval)
    (hmap : ν.map Prod.snd = sampleMeasure V p)
    (Good : State G → Prop)
    (hretain : ∀ s, Good s → ∀ v, s.2 v = true → v ∈ s.1.verts) :
    ν.real {s | Good s ∧ (Fintype.card s.1.verts : ℝ) < (p : ℝ) * Fintype.card V / 2} ≤
      exp (-(p : ℝ) * Fintype.card V / 8) := by
  have ht := sample_card_lower_tail p (Finset.univ : Finset V)
  simp only [Finset.univ_inter, Finset.card_univ] at ht
  rw [← hmap, Measure.real, Measure.map_apply (measurable_of_finite _)
    MeasurableSet.of_discrete] at ht
  apply le_trans _ ht
  apply measureReal_mono _ (measure_ne_top _ _)
  intro s hs
  have hsub : sampleVertices s.2 ⊆ s.1.verts.toFinset := by
    intro v hv
    exact Set.mem_toFinset.mpr (hretain s hs.1 v (by simpa [sampleVertices] using hv))
  have hc : ((sampleVertices s.2).card : ℝ) ≤ Fintype.card s.1.verts := by
    exact_mod_cast (show (sampleVertices s.2).card ≤ Fintype.card s.1.verts from
      (Finset.card_le_card hsub).trans_eq (Set.toFinset_card _))
  exact le_trans hc hs.2.le

/-- Finite conditional averaging with a retained-order guarantee paid from
the actual Bernoulli lower tail, rather than assumed as a successful event. -/
theorem exists_good_large_with_small_failures (G : SimpleGraph V)
    (ν : Measure (State G)) [IsProbabilityMeasure ν] (p : unitInterval)
    (hmap : ν.map Prod.snd = sampleMeasure V p)
    (Good : State G → Prop)
    (hretain : ∀ s, Good s → ∀ v, s.2 v = true → v ∈ s.1.verts)
    (f : I → State G → ℝ) (δ η : I → ℝ) (b : ℝ)
    (hf : ∀ i s, 0 ≤ f i s) (hη : ∀ i, 0 < η i)
    (havg : ∀ i, ∫ s, f i s ∂ν ≤ δ i)
    (hbad : ν.real {s | ¬ Good s} ≤ b)
    (hbudget : b + exp (-(p : ℝ) * Fintype.card V / 8) + ∑ i, δ i / η i < 1) :
    ∃ s, Good s ∧ (p : ℝ) * Fintype.card V / 2 ≤ (Fintype.card s.1.verts : ℝ) ∧
      ∀ i, f i s ≤ η i := by
  let GoodLarge := fun s : State G => Good s ∧
    (p : ℝ) * Fintype.card V / 2 ≤ (Fintype.card s.1.verts : ℝ)
  have hb : ν.real {s | ¬ GoodLarge s} ≤ b + exp (-(p : ℝ) * Fintype.card V / 8) := by
    have he : {s | ¬ GoodLarge s} = {s | ¬ Good s} ∪
        {s | Good s ∧ (Fintype.card s.1.verts : ℝ) < (p : ℝ) * Fintype.card V / 2} := by
      ext s
      simp only [GoodLarge, Set.mem_setOf_eq, Set.mem_union]
      by_cases h : Good s <;> simp [h, not_le]
    rw [he]
    exact (measureReal_union_le _ _).trans
      (add_le_add hbad (retained_order_bad_bound G ν p hmap Good hretain))
  obtain ⟨s, hs, hfs⟩ := exists_good_with_small_failures ν GoodLarge f δ η _ hf hη havg hb hbudget
  exact ⟨s, hs.1, hs.2, hfs⟩

/-- Order-aware version of the original-graph conditional supplier. -/
theorem exists_large_retained_with_larger_density_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ) (Λ d L : ℝ) (hN : 2 ≤ N) (hcard : Fintype.card V ≤ N)
    (hΛ : 1 ≤ Λ) (hd : 0 ≤ d)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ Λ * d)
    (q : I → unitInterval) (D δ η : I → ℝ) (hη : ∀ i, 0 < η i)
    (hroute : ∀ i,
      (sampleMeasure V (mulProbability (retentionProbability Λ hΛ) (q i))).real
        {B | ¬ StrongRoutingAt G (sampleVertices B) L (D i)} ≤ δ i)
    (hbudget : 1 / (N : ℝ) + exp (-(retentionProbability Λ hΛ : ℝ) * Fintype.card V / 8) +
      ∑ i, δ i / η i < 1) :
    ∃ (H : G.Subgraph) (A : V → Bool),
      NearlyRegularGood G d (1000000 * Λ ^ 5) (100000 * Λ ^ 5 * log N) (H, A) ∧
      (retentionProbability Λ hΛ : ℝ) * Fintype.card V / 2 ≤ (Fintype.card H.verts : ℝ) ∧
      ∀ i (p : unitInterval), (q i : ℝ) ≤ p →
        (sampleMeasure H.verts p).real {B | ¬ StrongRoutingAt G
          ((sampleVertices B).map (retainedEmbedding G H)) L (D i)} ≤ η i := by
  obtain ⟨ν, hν, hmap, hbad⟩ := exists_nearly_regular_bernoulli_coupling G N Λ d
    hN hcard hΛ hd hdeg
  letI := hν
  let f : I → State G → ℝ := fun i s => (sampleMeasure V (q i)).real
    {B | ¬ StrongRoutingAt G (sampleVertices (thin s.2 B)) L (D i)}
  have havg (i : I) : ∫ s, f i s ∂ν ≤ δ i := by
    have he : (∫ s, f i s ∂ν) =
        ∫ A : V → Bool, (sampleMeasure V (q i)).real
          {B | ¬ StrongRoutingAt G (sampleVertices (thin A B)) L (D i)}
            ∂sampleMeasure V (retentionProbability Λ hΛ) := by
      rw [← hmap]
      exact (integral_map (μ := ν)
        (measurable_of_finite (Prod.snd : State G → V → Bool)).aemeasurable
        (measurable_of_finite (fun A : V → Bool => (sampleMeasure V (q i)).real
          {B | ¬ StrongRoutingAt G (sampleVertices (thin A B)) L (D i)})).aestronglyMeasurable).symm
    have hF := finite_product_failure (sampleMeasure V (retentionProbability Λ hΛ))
      (sampleMeasure V (q i)) {x | ¬ StrongRoutingAt G
        (sampleVertices (thin x.1 x.2)) L (D i)}
    simp only [Set.mem_setOf_eq] at hF
    rw [he, ← hF, thin_event_probability (retentionProbability Λ hΛ) (q i)
      (fun B => ¬ StrongRoutingAt G (sampleVertices B) L (D i))]
    exact hroute i
  obtain ⟨s, hs, horder, hf⟩ := exists_good_large_with_small_failures G ν
    (retentionProbability Λ hΛ) hmap
    (NearlyRegularGood G d (1000000 * Λ ^ 5) (100000 * Λ ^ 5 * log N))
    (fun _ h => h.1) f δ η (1 / N) (fun _ _ => measureReal_nonneg) hη havg hbad hbudget
  refine ⟨s.1, s.2, hs, horder, ?_⟩
  intro i p hip
  rw [retained_event_probability G s.1 p (fun R => ¬ StrongRoutingAt G R L (D i))]
  have hsub : sampleVertices s.2 ⊆ s.1.verts.toFinset := by
    intro v hv
    exact Set.mem_toFinset.mpr (hs.1 v (by simpa [sampleVertices] using hv))
  have hm := masked_failure_mono (sampleVertices s.2) s.1.verts.toFinset hsub
    (q i) p hip (fun R => StrongRoutingAt G R L (D i))
    (fun _ _ h => strongRoutingAt_mono G h L (D i))
  apply hm.trans
  simpa only [f, thin_sampleVertices] using hf i

/-- Full five-pool supplier including the linear retained-order guarantee. -/
theorem exists_large_five_original_source_pool_supplier
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d L s : ℝ) (hd : 0 < d) (hL : (10 : ℝ) ^ 30 ≤ L)
    (hN : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ 18 * d)
    (hsdegree : d / L ^ 2 ≤ s) (hG : RobustCore.RobustExpanderAt G L (1 / 32) s)
    (pmin : Fin 5 → unitInterval) (η : Fin 5 → ℝ) (hη : ∀ i, 0 < η i)
    (hpmin : ∀ i, 0 < (pmin i : ℝ))
    (hseeddegree : ∀ i, 2560 * L ≤ (seedDensity (pmin i) : ℝ) * d)
    (hseedrobust : ∀ i, (((qProbability (seedDensity (pmin i)) : unitInterval) : ℝ)⁻¹) ^ 4 * L ^ 30 ≤ s)
    (hbudget : 1 / (Fintype.card V : ℝ) +
      exp (-(retentionProbability 18 (by norm_num) : ℝ) * Fintype.card V / 8) +
      ∑ i, (2 / (Fintype.card V : ℝ)) / η i < 1) :
    ∃ (H : G.Subgraph) (A : V → Bool),
      NearlyRegularGood G d (1000000 * (18 : ℝ) ^ 5)
        (100000 * (18 : ℝ) ^ 5 * log (Fintype.card V)) (H, A) ∧
      (retentionProbability 18 (by norm_num) : ℝ) * Fintype.card V / 2 ≤
        (Fintype.card H.verts : ℝ) ∧
      ∀ (Q : Finset H.verts) (m : Fin 5 → ℕ) (r t q M : Fin 5 → ℝ) (K a : ℝ),
        (∀ i, (pmin i : ℝ) ≤ r i) →
        PoolScalarBounds G H Q m r t q M η L K a →
        HasSourcePools G H Q m q (fun i => seedCapacity d L (pmin i)) M L K := by
  have hρ : 0 < (retentionProbability 18 (by norm_num) : ℝ) := by
    norm_num [retentionProbability]
  have hr (i : Fin 5) := bernoulli_source_strongRouting_failure G (seedDensity (pmin i))
    (show 0 < (seedDensity (pmin i) : ℝ) from mul_pos hρ (hpmin i))
    d (18 * d) L s hd le_rfl hL hN hlog (fun v => (hdeg v).1)
    (fun v => (hdeg v).2) (hseeddegree i) hsdegree (hseedrobust i) hG
  obtain ⟨H, A, hgood, horder, hroute⟩ := exists_large_retained_with_larger_density_bounds G
    (Fintype.card V) 18 d L hN le_rfl (by norm_num) hd.le hdeg pmin
    (fun i => seedCapacity d L (pmin i)) (fun _ => 2 / (Fintype.card V : ℝ)) η
    hη hr hbudget
  refine ⟨H, A, hgood, horder, ?_⟩
  intro Q m r t q M K a hmin hscalars
  apply source_pools_of_scalars G H Q m r t q _ M η L K a hscalars
  intro i
  exact hroute i (lowerProbability r t hscalars.lower_nonneg hscalars.buffer_nonneg
    hscalars.category_budget i) (hmin i)

end Erdos585.Attempt6.SourcePools
