import Openmath.Attempt6.CategoricalPools
import Openmath.Attempt6.StrongConnecting
import Openmath.Attempt6.UniformReachability
import Openmath.Attempt6.ReachabilityBoost

                                                                           
                                                                              
noncomputable section
namespace Erdos585.Attempt6.RandomRouting

open SimpleGraph MeasureTheory ProbabilityTheory Real Finset
open Reachability
open OAI.ErdosGallai.Sampling
open CategoricalPools
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every finite original terminal request has actual simple original-edge
paths with exact nonempty disjoint interiors and disjoint actual edge lists. -/
def StrongRoutingAt (G : SimpleGraph V) (R : Finset V) (L D : ℝ) : Prop :=
  ∀ (r : ℕ) (terminal : Fin r × Bool → V),
    (∀ i, terminal i ∉ R) →
    (∀ i, terminal (i, false) ≠ terminal (i, true)) →
    (∀ v ∈ R, (((Finset.univ : Finset (Fin r × Bool)).filter
      (fun i => G.Adj (terminal i) v)).card : ℝ) ≤ D) →
    ∃ S : Fin r → Finset V,
      ∃ p : (i : Fin r) → G.Walk (terminal (i, false)) (terminal (i, true)),
        (∀ i, (S i).Nonempty ∧ S i ⊆ R ∧
          terminal (i, false) ∉ S i ∧ terminal (i, true) ∉ S i ∧
          (p i).IsPath ∧ (p i).length ≤ Nat.floor (L ^ 6) ∧
          (p i).support.toFinset =
            insert (terminal (i, false)) (insert (terminal (i, true)) (S i))) ∧
        Pairwise (fun i j => Disjoint (S i) (S j)) ∧
        Pairwise (fun i j => (p i).edges.Disjoint (p j).edges)

/-- Actual local conditions imply the full universal finite-request contract. -/
theorem strongRoutingAt_of_pools (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q W : Finset V) (hdis : Disjoint Q W) (hsize : W.card ≤ Q.card) (hQ : 3 ≤ Q.card)
    (ell n : ℕ) (M L lambda delta D : ℝ)
    (hlambda : 0 < lambda) (hL : 16 ≤ L) (hdelta : 0 < delta) (hD : 0 ≤ D)
    (horder : Fintype.card V ≤ n)
    (hreach : ReservoirReachableAt G Q ell lambda)
    (hM : ∀ v ∈ Q, (graphDegreeInto G (Q ∪ W) v : ℝ) ≤ M)
    (hell : (ell : ℝ) ≤ L ^ 4) (hlog : logTwo (n : ℝ) ≤ L)
    (hleft : ∀ v, delta ≤ (graphDegreeInto G W v : ℝ))
    (hload : D ≤ lambda * delta / (16 * M * L ^ 12)) :
    StrongRoutingAt G (Q ∪ W) L D := by
  letI : DecidableRel G.Adj := fun x y => Classical.propDecidable (G.Adj x y)
  intro r terminal houtside hdistinct hright
  exact StrongConnecting.local_routing_power_six G terminal Q W hdis hsize hQ
    ell n M L lambda delta D hlambda hL hdelta hD horder hreach (fun v hv => by simpa [graphDegreeInto] using hM v hv) hell hlog
    (fun i => by simpa [graphDegreeInto] using hleft (terminal i))
    (fun v hv => by simpa using hright v (Finset.mem_union_right Q hv)) hload houtside hdistinct

def lowerRate (p : unitInterval) : Unit → ℝ := fun _ => 3 * (p : ℝ) / 4
def bufferRate (p : unitInterval) : Unit → ℝ := fun _ => (p : ℝ) / 4

lemma lowerRate_nonneg (p : unitInterval) : ∀ i, 0 ≤ lowerRate p i := by
  intro i; dsimp [lowerRate]; have hp := p.property.1; positivity
lemma bufferRate_nonneg (p : unitInterval) : ∀ i, 0 ≤ bufferRate p i := by
  intro i; dsimp [bufferRate]; have hp := p.property.1; positivity
lemma routing_rate_budget (p : unitInterval) :
    (∑ i : Unit, (lowerRate p i + bufferRate p i)) ≤ 1 := by
  simp only [Fintype.sum_unique, lowerRate, bufferRate]
  linarith [p.property.2]

def routingLaw (p : unitInterval) : Measure (V → Category Unit) :=
  poolLaw (lowerRate p) (bufferRate p) (lowerRate_nonneg p)
    (bufferRate_nonneg p) (routing_rate_budget p)

instance routingLaw_probability (p : unitInterval) : IsProbabilityMeasure (routingLaw (V := V) p) := by
  unfold routingLaw
  infer_instance

def qProbability (p : unitInterval) : unitInterval :=
  ⟨3 * (p : ℝ) / 4, by have hp := p.property.1; positivity, by linarith [p.property.2]⟩

abbrev Qpool (omega : V → Category Unit) := lowerPool omega ()
abbrev Wpool (omega : V → Category Unit) := bufferPool omega ()
def Rpool (omega : V → Category Unit) := Qpool omega ∪ Wpool omega

/-- The union R is exactly an independent Bernoulli-p vertex sample. -/
theorem routing_union_map (p : unitInterval) :
    (routingLaw (V := V) p).map (poolProjection (upperCategories ())) = sampleMeasure V p := by
  apply poolProjection_map (lowerRate p) (bufferRate p) (lowerRate_nonneg p)
    (bufferRate_nonneg p) (routing_rate_budget p)
  simp only [upperCategories_weight, lowerRate, bufferRate]
  ring

theorem union_event_probability (p : unitInterval) (P : Finset V → Prop) :
    (routingLaw p).real {omega | P (Rpool omega)} =
      (sampleMeasure V p).real {A | P (sampleVertices A)} := by
  rw [← routing_union_map p]
  simp only [Measure.real]
  rw [Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  apply congrArg ENNReal.toReal
  congr 1
  ext omega
  simp only [Set.mem_preimage, Set.mem_setOf_eq, upperProjection_vertices, Rpool]

theorem lower_event_probability (p : unitInterval) (P : Finset V → Prop) :
    (routingLaw p).real {omega | P (Qpool omega)} =
      (sampleMeasure V (qProbability p)).real {A | P (sampleVertices A)} := by
  exact lowerPool_event_probability (lowerRate p) (bufferRate p)
    (lowerRate_nonneg p) (bufferRate_nonneg p) (routing_rate_budget p)
    () (qProbability p) rfl P

/-- Explicit scalar condition paying the genuine categorical Bernstein radius. -/
theorem radius_le_half (M a : ℝ) (ha : 0 ≤ a) (hM : 0 ≤ M) (hlarge : 64 * a ≤ M) :
    CategoricalPools.radius M a ≤ M / 2 := by
  have hsq := Real.sq_sqrt (mul_nonneg hM ha)
  have hs0 := Real.sqrt_nonneg (M * a)
  have hm := mul_le_mul_of_nonneg_left hlarge hM
  have hs : Real.sqrt (M * a) ≤ M / 8 := by nlinarith
  unfold CategoricalPools.radius
  linarith

abbrev Query (V : Type*) := Bool ⊕ (Bool × V)
def bufferCategories : Finset (Category Unit) := {some ((), true)}
def queryCategories : Query V → Finset (Category Unit)
  | Sum.inl false => lowerCategories ()
  | Sum.inl true => bufferCategories
  | Sum.inr (false, _) => bufferCategories
  | Sum.inr (true, _) => upperCategories ()
def queryVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Query V → Finset V
  | Sum.inl _ => Finset.univ
  | Sum.inr (_, v) => G.neighborFinset v

lemma bufferCategories_weight (p : unitInterval) :
    (∑ c ∈ bufferCategories, categoryWeight (lowerRate p) (bufferRate p) c) = (p : ℝ) / 4 := by
  simp [bufferCategories, categoryWeight, bufferRate]

lemma bufferCategories_count (omega : V → Category Unit) (A : Finset V) :
    categoryCount bufferCategories A omega = (Wpool omega ∩ A).card := by
  unfold categoryCount bufferCategories Wpool bufferPool
  congr 1
  ext v
  simp [and_comm]

def CountsGood (G : SimpleGraph V) [DecidableRel G.Adj] (p : unitInterval) (a : ℝ)
    (omega : V → Category Unit) : Prop :=
  ∀ j : Query V,
    |(categoryCount (queryCategories j) (queryVertices G j) omega : ℝ) -
      (∑ c ∈ queryCategories j, categoryWeight (lowerRate p) (bufferRate p) c) *
        (queryVertices G j).card| <
      CategoricalPools.radius
        ((∑ c ∈ queryCategories j, categoryWeight (lowerRate p) (bufferRate p) c) *
          (queryVertices G j).card) a

/-- The actual joint product law pays every size and original-degree query;
no degree-good-event probability is assumed. -/
theorem counts_failure_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (a : ℝ) (ha : 0 < a) :
    (routingLaw p).real {omega | ¬CountsGood G p a omega} ≤
      (Fintype.card (Query V) : ℝ) * (2 * exp (-a)) := by
  have ht := all_counts_failure_bound (lowerRate p) (bufferRate p) (lowerRate_nonneg p)
    (bufferRate_nonneg p) (routing_rate_budget p) queryCategories (queryVertices G) a ha
  apply (measureReal_mono ?_ (measure_ne_top _ _)).trans ht
  intro omega hbad
  change ¬∀ j : Query V, _ at hbad
  push_neg at hbad
  exact hbad

/-- The paid categorical count event supplies every local routing condition,
including actual pool cardinalities and all original center degrees. -/
theorem pools_good_of_counts (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (hp : 0 < (p : ℝ)) (a d Delta : ℝ)
    (ha : 1 ≤ a) (hd : 0 < d)
    (hlower : ∀ v, d ≤ (G.degree v : ℝ))
    (hupper : ∀ v, (G.degree v : ℝ) ≤ Delta)
    (hsize : 256 * a ≤ (p : ℝ) * Fintype.card V)
    (hdegree : 256 * a ≤ (p : ℝ) * d)
    (omega : V → Category Unit) (hgood : CountsGood G p a omega) :
    Disjoint (Qpool omega) (Wpool omega) ∧ (Wpool omega).card ≤ (Qpool omega).card ∧
      3 ≤ (Qpool omega).card ∧
      (∀ v, (p : ℝ) * d / 8 ≤ (graphDegreeInto G (Wpool omega) v : ℝ)) ∧
      (∀ v, (graphDegreeInto G (Rpool omega) v : ℝ) ≤ 2 * (p : ℝ) * Delta) := by
  have ha0 : 0 ≤ a := by linarith
  have hq : |((Qpool omega).card : ℝ) - (3 * (p : ℝ) / 4) * Fintype.card V| <
      CategoricalPools.radius ((3 * (p : ℝ) / 4) * Fintype.card V) a := by
    simpa [queryCategories, queryVertices, lowerCategories_count,
      lowerCategories_weight, lowerRate] using hgood (Sum.inl false)
  have hw : |((Wpool omega).card : ℝ) - ((p : ℝ) / 4) * Fintype.card V| <
      CategoricalPools.radius (((p : ℝ) / 4) * Fintype.card V) a := by
    simpa [queryCategories, queryVertices, bufferCategories_count,
      bufferCategories_weight] using hgood (Sum.inl true)
  have hrq := radius_le_half ((3 * (p : ℝ) / 4) * Fintype.card V) a ha0
    (by positivity) (by nlinarith)
  have hrw := radius_le_half (((p : ℝ) / 4) * Fintype.card V) a ha0
    (by positivity) (by nlinarith)
  have hqlo : 3 * (p : ℝ) * Fintype.card V / 8 < (Qpool omega).card := by
    linarith [(abs_lt.mp hq).1]
  have hwhi : ((Wpool omega).card : ℝ) < 3 * (p : ℝ) * Fintype.card V / 8 := by
    linarith [(abs_lt.mp hw).2]
  refine ⟨lower_buffer_disjoint omega (), ?_, ?_, ?_, ?_⟩
  · have hh := le_of_lt (hwhi.trans hqlo)
    exact_mod_cast hh
  · have hh : (3 : ℝ) ≤ (Qpool omega).card := by linarith
    exact_mod_cast hh
  · intro v
    have hwv : |(graphDegreeInto G (Wpool omega) v : ℝ) - ((p : ℝ) / 4) * G.degree v| <
        CategoricalPools.radius (((p : ℝ) / 4) * G.degree v) a := by
      simpa only [queryCategories, queryVertices, bufferCategories_count,
        bufferCategories_weight, SimpleGraph.card_neighborFinset_eq_degree,
        ← graphDegreeInto_eq_inter] using hgood (Sum.inr (false, v))
    have hpd := mul_le_mul_of_nonneg_left (hlower v) hp.le
    have hr := radius_le_half (((p : ℝ) / 4) * G.degree v) a ha0
      (by positivity) (by nlinarith)
    linarith [(abs_lt.mp hwv).1]
  · intro v
    have hrv : |(graphDegreeInto G (Rpool omega) v : ℝ) - (p : ℝ) * G.degree v| <
        CategoricalPools.radius ((p : ℝ) * G.degree v) a := by
      have hh := hgood (Sum.inr (true, v))
      simpa [queryCategories, queryVertices, upperCategories_count,
        upperCategories_weight, lowerRate, bufferRate,
        ← graphDegreeInto_eq_inter, Rpool,
        show 3 * (p : ℝ) / 4 + (p : ℝ) / 4 = (p : ℝ) by ring] using hh
    have hpd := mul_le_mul_of_nonneg_left (hlower v) hp.le
    have hpu := mul_le_mul_of_nonneg_left (hupper v) hp.le
    have hr := radius_le_half ((p : ℝ) * G.degree v) a ha0
      (by positivity) (by nlinarith)
    have hm : (0 : ℝ) ≤ (p : ℝ) * G.degree v := by positivity
    linarith [(abs_lt.mp hrv).2]

                                                                                
                                                                          
                                                                           
theorem bernoulli_strongRouting_failure_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (hp : 0 < (p : ℝ)) (a d Delta L lambda D rho : ℝ)
    (ha : 1 ≤ a) (hd : 0 < d) (hlambda : 0 < lambda) (hD : 0 ≤ D)
    (hL : 16 ≤ L) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hlower : ∀ v, d ≤ (G.degree v : ℝ))
    (hupper : ∀ v, (G.degree v : ℝ) ≤ Delta)
    (hsize : 256 * a ≤ (p : ℝ) * Fintype.card V)
    (hdegree : 256 * a ≤ (p : ℝ) * d)
    (hload : D ≤ lambda * ((p : ℝ) * d / 8) /
      (16 * (2 * (p : ℝ) * Delta) * L ^ 12))
    (hreach : (sampleMeasure V (qProbability p)).real
      {A | ¬ReservoirReachableAt G (sampleVertices A) (Nat.floor (L ^ 4)) lambda} ≤ rho) :
    (sampleMeasure V p).real {A | ¬StrongRoutingAt G (sampleVertices A) L D} ≤
      rho + (Fintype.card (Query V) : ℝ) * (2 * exp (-a)) := by
  rw [← union_event_probability p (fun R => ¬StrongRoutingAt G R L D)]
  let Ereach : Set (V → Category Unit) := {omega |
    ¬ReservoirReachableAt G (Qpool omega) (Nat.floor (L ^ 4)) lambda}
  let Ecounts : Set (V → Category Unit) := {omega | ¬CountsGood G p a omega}
  have hr : (routingLaw p).real Ereach ≤ rho := by
    dsimp only [Ereach]
    rw [lower_event_probability p (fun Q =>
      ¬ReservoirReachableAt G Q (Nat.floor (L ^ 4)) lambda)]
    exact hreach
  have hc : (routingLaw p).real Ecounts ≤
      (Fintype.card (Query V) : ℝ) * (2 * exp (-a)) :=
    counts_failure_bound G p a (by linarith)
  have hsub : {omega | ¬StrongRoutingAt G (Rpool omega) L D} ⊆ Ereach ∪ Ecounts := by
    intro omega hbad
    by_cases hre : ReservoirReachableAt G (Qpool omega) (Nat.floor (L ^ 4)) lambda
    · by_cases hco : CountsGood G p a omega
      · obtain ⟨hdis, hWQ, hQ, hleft, hupperR⟩ :=
          pools_good_of_counts G p hp a d Delta ha hd hlower hupper hsize hdegree omega hco
        have hroute := strongRoutingAt_of_pools G (Qpool omega) (Wpool omega) hdis hWQ hQ
          (Nat.floor (L ^ 4)) (Fintype.card V) (2 * (p : ℝ) * Delta) L lambda
          ((p : ℝ) * d / 8) D hlambda hL (by positivity) hD (by rfl) hre
          (fun v _ => hupperR v) (Nat.floor_le (by positivity)) hlog hleft hload
        exact False.elim (hbad hroute)
      · exact Or.inr hco
    · exact Or.inl hre
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le Ereach Ecounts).trans (add_le_add hr hc))

                                                                           
                                                                           
                                     
theorem uniform_reachability_failure_weak
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : unitInterval) (L epsilon s : ℝ)
    (hq : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1)
    (hL : (10 : ℝ) ^ 30 ≤ L) (heps : (1 / 128 : ℝ) ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hN : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hs : 20 * ((q : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ s)
    (hG : RobustCore.RobustExpanderAt G L epsilon s) :
    (sampleMeasure V q).real {A |
      ¬ReservoirReachableAt G (sampleVertices A) (Nat.floor (L ^ 4))
        ((q : ℝ) ^ 4 / (1536 * L ^ 27))} ≤ 1 / (Fintype.card V : ℝ) ^ 2 := by
  letI : DecidableRel G.Adj := fun x y => Classical.propDecidable (G.Adj x y)
  have hL16 : 16 ≤ L := by norm_num at hL; linarith
  apply (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (UniformReachability.uniform_arbitrary_reservoir_large_scale G q L epsilon s
      hq hq1 hL heps heps1 hN hlog hs hG)
  intro A hbad
  unfold ReservoirReachableAt at hbad
  push_neg at hbad
  obtain ⟨U, hU, F, hFG, hF, hball⟩ := hbad
  have hbudget : (F.card : ℝ) ≤ (q : ℝ) ^ 4 * U.card / (1536 * L ^ 27) := by
    convert hF using 1 <;> ring
  have hmono : ((reservoirBall (G.deleteEdges F) U (sampleVertices A)
      (ReservoirGrowth.growthSteps L + 1)).card : ℝ) ≤
        (reservoirBall (G.deleteEdges F) U (sampleVertices A) (Nat.floor (L ^ 4))).card := by
    exact_mod_cast Finset.card_le_card
      (reservoirBall_mono_radius (G.deleteEdges F) U (sampleVertices A)
        (UniformReachability.growth_radius_le_floor L hL16))
  exact ⟨U, F, hU, hFG, hbudget, hmono.trans hball⟩

/-- Fully instantiated actual random strong routing using the currently
verified weak reachability budget, without any good-event or probability-law
premise. The source-scale boosted lambda is a separate stronger supplier. -/
theorem bernoulli_strongRouting_weak
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (hp : 0 < (p : ℝ)) (a d Delta L epsilon s D : ℝ)
    (ha : 1 ≤ a) (hd : 0 < d) (hD : 0 ≤ D)
    (hL : (10 : ℝ) ^ 30 ≤ L) (heps : (1 / 128 : ℝ) ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hN : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hlower : ∀ v, d ≤ (G.degree v : ℝ))
    (hupper : ∀ v, (G.degree v : ℝ) ≤ Delta)
    (hsize : 256 * a ≤ (p : ℝ) * Fintype.card V)
    (hdegree : 256 * a ≤ (p : ℝ) * d)
    (hs : 20 * (((qProbability p : unitInterval) : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ s)
    (hG : RobustCore.RobustExpanderAt G L epsilon s)
    (hload : D ≤ (((qProbability p : unitInterval) : ℝ) ^ 4 / (1536 * L ^ 27)) *
      ((p : ℝ) * d / 8) / (16 * (2 * (p : ℝ) * Delta) * L ^ 12)) :
    (sampleMeasure V p).real {A | ¬StrongRoutingAt G (sampleVertices A) L D} ≤
      1 / (Fintype.card V : ℝ) ^ 2 +
        (Fintype.card (Query V) : ℝ) * (2 * exp (-a)) := by
  have hq : (0 : ℝ) < (qProbability p : unitInterval) := by
    dsimp [qProbability]
    positivity
  have hq1 : ((qProbability p : unitInterval) : ℝ) < 1 := by
    dsimp [qProbability]
    linarith [p.property.2]
  have hL16 : 16 ≤ L := by norm_num at hL; linarith
  apply bernoulli_strongRouting_failure_bound G p hp a d Delta L
    (((qProbability p : unitInterval) : ℝ) ^ 4 / (1536 * L ^ 27))
    D (1 / (Fintype.card V : ℝ) ^ 2) ha hd (by positivity) hD hL16 hlog
    hlower hupper hsize hdegree hload
  exact uniform_reachability_failure_weak G (qProbability p) L epsilon s hq hq1
    hL heps heps1 hN hlog hs hG

/-- The finite count-query family has exactly two size and two-per-vertex
degree queries. -/
theorem query_card : Fintype.card (Query V) = 2 + 2 * Fintype.card V := by
  simp [Query, Fintype.card_sum, Fintype.card_prod]

/-- Once the edge-partition boost supplies lambda=q^8*s/L^60, the stronger
density-eight load p^8*d/L^75 is affordable. Fixed numerical constants are
paid by L>=1179648, far below the ambient source threshold. -/
theorem source_eight_density_load_budget (p : unitInterval) (hp : 0 < (p : ℝ))
    (d Delta s L : ℝ) (hd : 0 < d) (hDelta : 0 < Delta)
    (hL : 1179648 ≤ L) (hhi : Delta ≤ 18 * d) (hs : d / L ^ 2 ≤ s) :
    (p : ℝ) ^ 8 * d / L ^ 75 ≤
      (((qProbability p : unitInterval) : ℝ) ^ 8 * s / L ^ 60) *
        ((p : ℝ) * d / 8) / (16 * (2 * (p : ℝ) * Delta) * L ^ 12) := by
  let q : ℝ := (qProbability p : unitInterval)
  let lam : ℝ := q ^ 8 * s / L ^ 60
  have hLp : 0 < L := by linarith
  have hq : 0 ≤ q := by dsimp [q, qProbability]; positivity
  have hpq : (p : ℝ) ≤ 2 * q := by dsimp [q, qProbability]; linarith
  have hpow : (p : ℝ) ^ 8 ≤ 256 * q ^ 8 := by
    have hh := pow_le_pow_left₀ hp.le hpq 8
    norm_num [mul_pow] at hh ⊢
    exact hh
  have hcross : 4608 * (p : ℝ) ^ 8 ≤ q ^ 8 * L := by
    have hh := mul_le_mul_of_nonneg_right hL (pow_nonneg hq 8)
    nlinarith
  have hfirst : (p : ℝ) ^ 8 * d / L ^ 75 ≤ q ^ 8 * d / (4608 * L ^ 74) := by
    have hh := mul_le_mul_of_nonneg_right hcross
      (show 0 ≤ d / (4608 * L ^ 75) by positivity)
    calc
      _ = 4608 * (p : ℝ) ^ 8 * (d / (4608 * L ^ 75)) := by field_simp <;> ring
      _ ≤ q ^ 8 * L * (d / (4608 * L ^ 75)) := hh
      _ = _ := by field_simp <;> ring
  have hlam : q ^ 8 * d / L ^ 62 ≤ lam := by
    have hh := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ q ^ 8 / L ^ 60 by positivity)
    calc
      _ = q ^ 8 / L ^ 60 * (d / L ^ 2) := by field_simp <;> ring
      _ ≤ q ^ 8 / L ^ 60 * s := hh
      _ = lam := by dsimp [lam]; ring
  have hlam0 : 0 ≤ lam := (by positivity : 0 ≤ q ^ 8 * d / L ^ 62).trans hlam
  have hsecond : q ^ 8 * d / (4608 * L ^ 74) ≤ lam / (4608 * L ^ 12) := by
    have hh := div_le_div_of_nonneg_right hlam
      (show 0 ≤ 4608 * L ^ 12 by positivity)
    calc
      _ = (q ^ 8 * d / L ^ 62) / (4608 * L ^ 12) := by field_simp <;> ring
      _ ≤ _ := hh
  have hden : 256 * Delta * L ^ 12 ≤ 4608 * d * L ^ 12 := by
    have hh := mul_le_mul_of_nonneg_right hhi (show 0 ≤ 256 * L ^ 12 by positivity)
    nlinarith only [hh]
  have hthird : lam / (4608 * L ^ 12) ≤ lam * d / (256 * Delta * L ^ 12) := by
    have hh := div_le_div_of_nonneg_left (mul_nonneg hlam0 hd.le)
      (show 0 < 256 * Delta * L ^ 12 by positivity) hden
    calc
      _ = lam * d / (4608 * d * L ^ 12) := by field_simp <;> ring
      _ ≤ _ := hh
  have heq : lam * ((p : ℝ) * d / 8) /
      (16 * (2 * (p : ℝ) * Delta) * L ^ 12) =
        lam * d / (256 * Delta * L ^ 12) := by
    field_simp [ne_of_gt hp, ne_of_gt hDelta, ne_of_gt hLp]
    <;> ring
  change _ ≤ lam * ((p : ℝ) * d / 8) / _
  rw [heq]
  exact hfirst.trans (hsecond.trans hthird)

/-- The exact categorical query tail is at most one inverse order when
a=10L and L dominates the ambient binary logarithm. -/
theorem count_tail_le_inverse_order (N : ℕ) (hN : 2 ≤ N) (L : ℝ)
    (hlog : logTwo (N : ℝ) ≤ L) :
    ((2 + 2 * N : ℕ) : ℝ) * (2 * exp (-(10 * L))) ≤ 1 / (N : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hln := UniformReachability.log_order_le_ambient N hN L hlog
  have heq : exp (-(10 * log (N : ℝ))) = 1 / (N : ℝ) ^ 10 := by
    rw [exp_neg, show 10 * log (N : ℝ) = ((10 : ℕ) : ℝ) * log (N : ℝ) by norm_num,
      exp_nat_mul, exp_log hNp]
    simp
  have hexp : exp (-(10 * L)) ≤ 1 / (N : ℝ) ^ 10 := by
    rw [← heq]
    exact exp_le_exp.mpr (by linarith)
  have hpow : (256 : ℝ) ≤ (N : ℝ) ^ 8 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN2 8
    norm_num at hh ⊢
    exact hh
  have hlarge : 256 * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 10 := by
    calc
      _ ≤ (N : ℝ) ^ 8 * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ((2 + 2 * N : ℕ) : ℝ) * (2 * (1 / (N : ℝ) ^ 10)) := by gcongr
    _ = (4 + 4 * (N : ℝ)) / (N : ℝ) ^ 10 := by push_cast; ring
    _ ≤ 1 / (N : ℝ) := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ 10) hNp).mpr
      nlinarith

/-- A genuine minimum degree also bounds the original order, so the same
scalar degree threshold pays the required pool-size concentration threshold. -/
theorem order_threshold_of_degree_threshold (G : SimpleGraph V) [DecidableRel G.Adj]
    (hN : 2 ≤ Fintype.card V) (p : unitInterval) (a d : ℝ)
    (hlower : ∀ v, d ≤ (G.degree v : ℝ)) (hdegree : 256 * a ≤ (p : ℝ) * d) :
    256 * a ≤ (p : ℝ) * Fintype.card V := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  have hh : G.degree v ≤ Fintype.card V := by
    simpa only [G.card_neighborFinset_eq_degree] using Finset.card_le_univ (G.neighborFinset v)
  have hhR : (G.degree v : ℝ) ≤ Fintype.card V := by exact_mod_cast hh
  exact hdegree.trans (mul_le_mul_of_nonneg_left ((hlower v).trans hhR) p.property.1)

/-- Fully instantiated density-eight strong random routing in the actual
original graph. The categorical union is exactly Bernoulli-p, and the actual
edge-partition boost supplies reachability without a free-family or tail input. -/
theorem bernoulli_source_strongRouting_failure
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (hp : 0 < (p : ℝ)) (d Delta L s : ℝ)
    (hd : 0 < d) (hDelta : Delta ≤ 18 * d)
    (hL : (10 : ℝ) ^ 30 ≤ L) (hN : 2 ≤ Fintype.card V)
    (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hlower : ∀ v, d ≤ (G.degree v : ℝ))
    (hupper : ∀ v, (G.degree v : ℝ) ≤ Delta)
    (hdegree : 2560 * L ≤ (p : ℝ) * d)
    (hsdegree : d / L ^ 2 ≤ s)
    (hsrobust : (((qProbability p : unitInterval) : ℝ)⁻¹) ^ 4 * L ^ 30 ≤ s)
    (hG : RobustCore.RobustExpanderAt G L (1 / 32) s) :
    (sampleMeasure V p).real
      {A | ¬StrongRoutingAt G (sampleVertices A) L ((p : ℝ) ^ 8 * d / L ^ 75)} ≤
        2 / (Fintype.card V : ℝ) := by
  have hLp : 0 < L := by norm_num at hL; linarith
  have hL16 : 16 ≤ L := by norm_num at hL; linarith
  have hLfixed : 1179648 ≤ L := by norm_num at hL; linarith
  have hq : (0 : ℝ) < (qProbability p : unitInterval) := by
    dsimp [qProbability]
    positivity
  have hq1 : ((qProbability p : unitInterval) : ℝ) < 1 := by
    dsimp [qProbability]
    linarith [p.property.2]
  have hsp : 0 < s := (div_pos hd (pow_pos hLp 2)).trans_le hsdegree
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  have hDeltaPos : 0 < Delta := hd.trans_le ((hlower v).trans (hupper v))
  have hdeg : 256 * (10 * L) ≤ (p : ℝ) * d := by linarith
  have hsize := order_threshold_of_degree_threshold G hN p (10 * L) d hlower hdeg
  have hload := source_eight_density_load_budget p hp d Delta s L hd hDeltaPos
    hLfixed hDelta hsdegree
  have ht := bernoulli_strongRouting_failure_bound G p hp (10 * L) d Delta L
    (((qProbability p : unitInterval) : ℝ) ^ 8 * s / L ^ 60)
    ((p : ℝ) ^ 8 * d / L ^ 75) (1 / (Fintype.card V : ℝ))
    (by linarith) hd (by positivity) (by positivity) hL16 hlog hlower hupper
    hsize hdeg hload
    (ReachabilityBoost.original_graph_reservoir_failure G (qProbability p) L s hq hq1
      hL hN hlog hsrobust hG)
  rw [query_card] at ht
  have htail := count_tail_le_inverse_order (Fintype.card V) hN L hlog
  calc
    _ ≤ _ := ht
    _ ≤ 1 / (Fintype.card V : ℝ) + 1 / (Fintype.card V : ℝ) := add_le_add (le_refl _) htail
    _ = _ := by ring

/-- Equivalent good-event form of the exact Bernoulli strong-routing law. -/
theorem bernoulli_source_strongRouting_good_probability
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (hp : 0 < (p : ℝ)) (d Delta L s : ℝ)
    (hd : 0 < d) (hDelta : Delta ≤ 18 * d)
    (hL : (10 : ℝ) ^ 30 ≤ L) (hN : 2 ≤ Fintype.card V)
    (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hlower : ∀ v, d ≤ (G.degree v : ℝ))
    (hupper : ∀ v, (G.degree v : ℝ) ≤ Delta)
    (hdegree : 2560 * L ≤ (p : ℝ) * d)
    (hsdegree : d / L ^ 2 ≤ s)
    (hsrobust : (((qProbability p : unitInterval) : ℝ)⁻¹) ^ 4 * L ^ 30 ≤ s)
    (hG : RobustCore.RobustExpanderAt G L (1 / 32) s) :
    1 - 2 / (Fintype.card V : ℝ) ≤
      (sampleMeasure V p).real
        {A | StrongRoutingAt G (sampleVertices A) L ((p : ℝ) ^ 8 * d / L ^ 75)} := by
  have hb := bernoulli_source_strongRouting_failure G p hp d Delta L s hd hDelta
    hL hN hlog hlower hupper hdegree hsdegree hsrobust hG
  let E : Set (V → Bool) :=
    {A | StrongRoutingAt G (sampleVertices A) L ((p : ℝ) ^ 8 * d / L ^ 75)}
  change (sampleMeasure V p).real Eᶜ ≤ _ at hb
  rw [measureReal_compl MeasurableSet.of_discrete, probReal_univ] at hb
  change _ ≤ (sampleMeasure V p).real E
  linarith

/-- Enlarging a routing reservoir preserves the full actual path contract,
including exact nonempty interiors and original edge disjointness. This is
the monotone property consumed by deterministic balanced completion. -/
theorem strongRoutingAt_mono (G : SimpleGraph V) (L D : ℝ)
    {R S : Finset V} (hRS : R ⊆ S) (hR : StrongRoutingAt G R L D) :
    StrongRoutingAt G S L D := by
  intro r terminal houtside hdistinct hload
  obtain ⟨T, p, hp, hdis, hedges⟩ := hR r terminal
    (fun i hi => houtside i (hRS hi)) hdistinct
    (fun v hv => hload v (hRS hv))
  refine ⟨T, p, ?_, hdis, hedges⟩
  intro i
  obtain ⟨hne, hsub, hx, hy, hsimple, hlength, hsupport⟩ := hp i
  exact ⟨hne, hsub.trans hRS, hx, hy, hsimple, hlength, hsupport⟩

end Erdos585.Attempt6.RandomRouting
