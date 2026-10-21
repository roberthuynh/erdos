import Openmath.Attempt6.PublicBernoulli

/-!
Original-edge coin construction for the CJMM 2025 Lemma 4.1 step.
Each low vertex uses one vertex coin; each high endpoint uses an incidence coin.
With coin survival probability p, a high-high edge survives with probability p²,
a low-high edge uses one independent edge coin, and low vertices survive with p.
The main theorem proves the one-step regularity improvement with failure at
most 1/n² under the published logarithmic condition, for n at least two.
Iteration and the final additive regularization theorem remain separate.
-/

namespace Erdos585.Attempt6.RegularizationStep

open MeasureTheory ProbabilityTheory Finset Real
open OAI.ErdosGallai.Sampling

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Coin (V : Type*) := Sum V (V × V)

def endpointCoin (L : Finset V) (u v : V) : Coin V :=
  if u ∈ L then Sum.inl u else Sum.inr (u, v)

def retained (L : Finset V) (ω : Coin V → Bool) : Set V :=
  {v | v ∉ L ∨ ω (Sum.inl v) = true}

/-- Every original sampled vertex is retained, including all sampled high vertices. -/
theorem sample_subset_retained (L : Finset V) (ω : Coin V → Bool) :
    {v | ω (Sum.inl v) = true} ⊆ retained L ω := by
  intro v hv
  exact Or.inr hv

/-- An actual original-edge subgraph. Both endpoint tests are used symmetrically. -/
def sampledSubgraph (G : SimpleGraph V) (L : Finset V) (ω : Coin V → Bool) :
    G.Subgraph where
  verts := retained L ω
  Adj u v := G.Adj u v ∧ ω (endpointCoin L u v) = true ∧
    ω (endpointCoin L v u) = true
  adj_sub h := h.1
  edge_vert := by
    intro u v h
    by_cases hu : u ∈ L
    · exact Or.inr (by simpa [endpointCoin, hu] using h.2.1)
    · exact Or.inl hu
  symm := ⟨fun u v h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩

/-- Coins that determine one neighbor's contribution after retaining v. -/
def neighborBlock (L : Finset V) (v u : V) : Finset (Coin V) :=
  if v ∈ L then {endpointCoin L u v}
  else {endpointCoin L v u, endpointCoin L u v}

lemma endpointCoin_ne_reverse (L : Finset V) {u v : V} (h : u ≠ v) :
    endpointCoin L u v ≠ endpointCoin L v u := by
  simp only [endpointCoin]
  split <;> split <;> simp_all

lemma neighborBlock_card (L : Finset V) {v u : V} (h : u ≠ v) :
    (neighborBlock L v u).card = if v ∈ L then 1 else 2 := by
  by_cases hv : v ∈ L
  · simp [neighborBlock, hv]
  · simp [neighborBlock, hv, endpointCoin_ne_reverse L h.symm]

lemma neighborBlocks_disjoint (L : Finset V) {v u w : V}
    (hu : u ≠ v) (hw : w ≠ v) (huw : u ≠ w) :
    Disjoint (neighborBlock L v u) (neighborBlock L v w) := by
  simp only [neighborBlock, endpointCoin]
  split <;> split <;> split <;> simp_all [Finset.disjoint_left]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

instance sampled_decidable (L : Finset V) (ω : Coin V → Bool) :
    DecidableRel (sampledSubgraph G L ω).spanningCoe.Adj :=
  fun u v => inferInstanceAs (Decidable
    (G.Adj u v ∧ ω (endpointCoin L u v) = true ∧ ω (endpointCoin L v u) = true))

lemma adjacency_iff_block (L : Finset V) (ω : Coin V → Bool) {v u : V}
    (hv : v ∈ retained L ω) :
    (sampledSubgraph G L ω).Adj v u ↔
      G.Adj v u ∧ neighborBlock L v u ⊆ sampleVertices ω := by
  by_cases hl : v ∈ L
  · have hv' : ω (Sum.inl v) = true := hv.resolve_left (not_not.mpr hl)
    simp [sampledSubgraph, neighborBlock, hl, endpointCoin, hv', sampleVertices]
  · simp [sampledSubgraph, neighborBlock, hl, sampleVertices, Finset.insert_subset_iff]

/-- Exact degree identity, on the original graph's neighbor type. -/
theorem degree_eq_block_sum (L : Finset V) (ω : Coin V → Bool) {v : V}
    (hv : v ∈ retained L ω) :
    ((sampledSubgraph G L ω).spanningCoe.degree v : ℝ) =
      ∑ u : ↥(G.neighborFinset v), blockIndicator (neighborBlock L v u) ω := by
  classical
  rw [SimpleGraph.degree_eq_sum_if_adj]
  rw [Finset.sum_coe_sort (G.neighborFinset v) (fun u => blockIndicator (neighborBlock L v u) ω),
    SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  simp only [SimpleGraph.Subgraph.spanningCoe_adj, adjacency_iff_block G L ω hv]
  simp only [blockIndicator, Set.indicator_apply, Set.mem_ofPred_eq]
  by_cases h : G.Adj v u <;> simp [h]

lemma neighbor_blocks_pairwise (L : Finset V) (v : V) :
    Pairwise fun u w : ↥(G.neighborFinset v) =>
      Disjoint (neighborBlock L v u) (neighborBlock L v w) := by
  intro u w huw
  exact neighborBlocks_disjoint L
    (G.ne_of_adj (G.mem_neighborFinset _ _ |>.mp u.property)).symm
    (G.ne_of_adj (G.mem_neighborFinset _ _ |>.mp w.property)).symm
    (fun h => huw (Subtype.ext h))

lemma neighbor_blocks_card (L : Finset V) (v : V) (u : ↥(G.neighborFinset v)) :
    (neighborBlock L v u).card = if v ∈ L then 1 else 2 :=
  neighborBlock_card L (G.ne_of_adj (G.mem_neighborFinset _ _ |>.mp u.property)).symm

/-- The degree surrogate is a sum of mutually independent 0/1 variables with
mean p for low v and p² for high v. On retained vertices it equals actual degree. -/
theorem neighbor_indicators_independent (L : Finset V) (p : unitInterval) (v : V) :
    iIndepFun (fun u : ↥(G.neighborFinset v) => blockIndicator (neighborBlock L v u))
      (sampleMeasure (Coin V) p) :=
  (sample_blocks_independent p _ (neighbor_blocks_pairwise G L v)).iIndepFun_indicator

theorem neighbor_indicator_integral (L : Finset V) (p : unitInterval) (v : V)
    (u : ↥(G.neighborFinset v)) :
    (∫ ω, blockIndicator (neighborBlock L v u) ω ∂sampleMeasure (Coin V) p) =
      (p : ℝ) ^ (if v ∈ L then 1 else 2) := by
  rw [blockIndicator_integral, neighbor_blocks_card G L v u]

/-- Unconditional probability of a bad retained vertex. No conditional event is
assumed to have positive probability. -/
theorem retained_degree_lower_tail (L : Finset V) (p : unitInterval) (v : V) :
    (sampleMeasure (Coin V) p).real
      {ω | v ∈ retained L ω ∧
        ((sampledSubgraph G L ω).spanningCoe.degree v : ℝ) ≤
          (p : ℝ) ^ (if v ∈ L then 1 else 2) * G.degree v / 2} ≤
      exp (-(p : ℝ) ^ (if v ∈ L then 1 else 2) * G.degree v / 8) := by
  have ht := sample_blocks_lower_tail p
    (fun u : ↥(G.neighborFinset v) => neighborBlock L v u)
    (neighbor_blocks_pairwise G L v) (if v ∈ L then 1 else 2)
    (neighbor_blocks_card G L v) Finset.univ
  simp only [Finset.card_univ, Fintype.card_coe,
    SimpleGraph.card_neighborFinset_eq_degree] at ht
  apply le_trans _ ht
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq]
  rw [← degree_eq_block_sum G L ω hω.1]
  exact hω.2

theorem retained_degree_upper_tail (L : Finset V) (p : unitInterval) (v : V) :
    (sampleMeasure (Coin V) p).real
      {ω | v ∈ retained L ω ∧
        2 * (p : ℝ) ^ (if v ∈ L then 1 else 2) * G.degree v ≤
          ((sampledSubgraph G L ω).spanningCoe.degree v : ℝ)} ≤
      exp (-(p : ℝ) ^ (if v ∈ L then 1 else 2) * G.degree v / 3) := by
  have ht := bernoulli_sum_upper_tail (Finset.univ : Finset ↥(G.neighborFinset v))
    (fun _ => measurable_of_finite _) (neighbor_indicators_independent G L p v)
    (fun u => blockIndicator_values (neighborBlock L v u))
    ((p : ℝ) ^ (if v ∈ L then 1 else 2)) (pow_nonneg p.property.1 _)
    (neighbor_indicator_integral G L p v)
  simp only [Finset.card_univ, Fintype.card_coe,
    SimpleGraph.card_neighborFinset_eq_degree] at ht
  apply le_trans _ ht
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq]
  rw [← degree_eq_block_sum G L ω hω.1]
  exact hω.2

/-- The coupled subset A has the exact independent vertex-inclusion moments. -/
theorem coupled_vertex_contains_probability (p : unitInterval) (S : Finset V) :
    (sampleMeasure (Coin V) p).real {ω | ∀ v ∈ S, ω (Sum.inl v) = true} =
      (p : ℝ) ^ S.card := by
  have heq : {ω : Coin V → Bool | ∀ v ∈ S, ω (Sum.inl v) = true} =
      {ω | S.image Sum.inl ⊆ sampleVertices ω} := by
    ext ω
    simp [Finset.image_subset_iff, sampleVertices]
  rw [heq, sample_contains_real_probability,
    Finset.card_image_of_injective _ Sum.inl_injective]

/-- Each original edge has the correct survival marginal p². -/
theorem original_edge_survival_probability (L : Finset V) (p : unitInterval)
    {u v : V} (huv : G.Adj u v) :
    (sampleMeasure (Coin V) p).real {ω | (sampledSubgraph G L ω).Adj u v} =
      (p : ℝ) ^ 2 := by
  have heq : {ω | (sampledSubgraph G L ω).Adj u v} =
      {ω | {endpointCoin L u v, endpointCoin L v u} ⊆ sampleVertices ω} := by
    ext ω
    simp [sampledSubgraph, huv, Finset.insert_subset_iff, sampleVertices]
  rw [heq, sample_contains_real_probability]
  simp [endpointCoin_ne_reverse L (G.ne_of_adj huv)]

noncomputable def deletionIndicator (L : Finset V) (v u : V) (ω : Coin V → Bool) : ℝ :=
  1 - blockIndicator (neighborBlock L v u) ω

lemma deletion_independent (L : Finset V) (p : unitInterval) (v : V) :
    iIndepFun (fun u : ↥(G.neighborFinset v) => deletionIndicator L v u)
      (sampleMeasure (Coin V) p) := by
  exact (neighbor_indicators_independent G L p v).comp
    (fun _ x => (1 : ℝ) - x) (fun _ => measurable_const.sub measurable_id)

lemma deletion_values (L : Finset V) (v u : V) (ω : Coin V → Bool) :
    deletionIndicator L v u ω = 0 ∨ deletionIndicator L v u ω = 1 := by
  rcases blockIndicator_values (neighborBlock L v u) ω with h | h <;>
    simp [deletionIndicator, h]

lemma deletion_integral (L : Finset V) (p : unitInterval) (v : V)
    (u : ↥(G.neighborFinset v)) :
    (∫ ω, deletionIndicator L v u ω ∂sampleMeasure (Coin V) p) =
      1 - (p : ℝ) ^ (if v ∈ L then 1 else 2) := by
  simp only [deletionIndicator]
  rw [integral_sub (integrable_const _) Integrable.of_finite,
    integral_const, neighbor_indicator_integral G L p v u]
  simp

lemma deletion_sum (L : Finset V) (ω : Coin V → Bool) {v : V}
    (hv : v ∈ retained L ω) :
    (∑ u : ↥(G.neighborFinset v), deletionIndicator L v u ω) =
      (G.degree v : ℝ) - (sampledSubgraph G L ω).spanningCoe.degree v := by
  simp only [deletionIndicator, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree,
    nsmul_eq_mul, mul_one, degree_eq_block_sum G L ω hv]

/-- Arbitrary-threshold Chernoff bound for the actual degree deficit.
Unlike a factor-two bound, this retains the small deletion mean 1-p or 1-p². -/
theorem retained_degree_below_chernoff (L : Finset V) (p : unitInterval) (v : V)
    (a t : ℝ) (ht : 0 ≤ t) :
    (sampleMeasure (Coin V) p).real
      {ω | v ∈ retained L ω ∧ ((sampledSubgraph G L ω).spanningCoe.degree v : ℝ) ≤ a} ≤
      exp (-t * ((G.degree v : ℝ) - a) + (G.degree v : ℝ) *
        (1 - (p : ℝ) ^ (if v ∈ L then 1 else 2)) * (exp t - 1)) := by
  let μ := sampleMeasure (Coin V) p
  let X := fun u : ↥(G.neighborFinset v) => deletionIndicator L v u
  have hb := measure_ge_le_exp_mul_mgf (μ := μ) (X := ∑ u, X u)
    ((G.degree v : ℝ) - a) ht (Integrable.of_finite)
  have hm := mgf_indicator_sum_bound (μ := μ) Finset.univ
    (fun u => measurable_of_finite (X u)) (deletion_independent G L p v)
    (fun u => deletion_values L v u)
    (1 - (p : ℝ) ^ (if v ∈ L then 1 else 2)) t (deletion_integral G L p v)
  simp only [Finset.card_univ, Fintype.card_coe,
    SimpleGraph.card_neighborFinset_eq_degree] at hm
  calc
    _ ≤ μ.real {ω | (G.degree v : ℝ) - a ≤ (∑ u, X u) ω} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      simp only [Set.mem_ofPred_eq, Finset.sum_apply]
      change (G.degree v : ℝ) - a ≤ ∑ u : ↥(G.neighborFinset v), deletionIndicator L v u ω
      rw [deletion_sum G L ω hω.1]
      linarith [hω.2]
    _ ≤ exp (-t * ((G.degree v : ℝ) - a)) * mgf (∑ u, X u) μ t := hb
    _ ≤ exp (-t * ((G.degree v : ℝ) - a)) *
        exp ((G.degree v : ℝ) * (1 - (p : ℝ) ^ (if v ∈ L then 1 else 2)) *
          (exp t - 1)) := mul_le_mul_of_nonneg_left hm (exp_pos _).le
    _ = _ := (exp_add _ _).symm

/-- Matching upper-degree bound, obtained from the lower tail of deletions. -/
theorem retained_degree_above_chernoff (L : Finset V) (p : unitInterval) (v : V)
    (a t : ℝ) (ht : t ≤ 0) :
    (sampleMeasure (Coin V) p).real
      {ω | v ∈ retained L ω ∧ a ≤ ((sampledSubgraph G L ω).spanningCoe.degree v : ℝ)} ≤
      exp (-t * ((G.degree v : ℝ) - a) + (G.degree v : ℝ) *
        (1 - (p : ℝ) ^ (if v ∈ L then 1 else 2)) * (exp t - 1)) := by
  let μ := sampleMeasure (Coin V) p
  let X := fun u : ↥(G.neighborFinset v) => deletionIndicator L v u
  have hb := measure_le_le_exp_mul_mgf (μ := μ) (X := ∑ u, X u)
    ((G.degree v : ℝ) - a) ht (Integrable.of_finite)
  have hm := mgf_indicator_sum_bound (μ := μ) Finset.univ
    (fun u => measurable_of_finite (X u)) (deletion_independent G L p v)
    (fun u => deletion_values L v u)
    (1 - (p : ℝ) ^ (if v ∈ L then 1 else 2)) t (deletion_integral G L p v)
  simp only [Finset.card_univ, Fintype.card_coe,
    SimpleGraph.card_neighborFinset_eq_degree] at hm
  calc
    _ ≤ μ.real {ω | (∑ u, X u) ω ≤ (G.degree v : ℝ) - a} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      simp only [Set.mem_ofPred_eq, Finset.sum_apply]
      change (∑ u : ↥(G.neighborFinset v), deletionIndicator L v u ω) ≤ (G.degree v : ℝ) - a
      rw [deletion_sum G L ω hω.1]
      linarith [hω.2]
    _ ≤ exp (-t * ((G.degree v : ℝ) - a)) * mgf (∑ u, X u) μ t := hb
    _ ≤ exp (-t * ((G.degree v : ℝ) - a)) *
        exp ((G.degree v : ℝ) * (1 - (p : ℝ) ^ (if v ∈ L then 1 else 2)) *
          (exp t - 1)) := mul_le_mul_of_nonneg_left hm (exp_pos _).le
    _ = _ := (exp_add _ _).symm

lemma exp_one_eighth_le : exp (1 / 8 : ℝ) ≤ 17 / 15 := by
  have h := exp_le_two_add_div_two_sub (x := (1 / 8 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

lemma exp_neg_one_sixteenth_le : exp (-(1 / 16 : ℝ)) ≤ 16 / 17 := by
  rw [exp_neg]
  apply (inv_le_comm₀ (exp_pos _) (by norm_num : (0 : ℝ) < 16 / 17)).mpr
  have h := add_one_le_exp (1 / 16 : ℝ)
  norm_num at *
  linarith

/-- Sharp enough lower-degree tail for the CJMM step. The high-degree input only
uses the weaker gap 5εd, which follows from γ ≥ 10ε. -/
theorem step_lower_tail (L : Finset V) (p : unitInterval) (v : V)
    (ε d : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hd : 0 ≤ d)
    (hp : (p : ℝ) = 1 - ε)
    (hD : if v ∈ L then d ≤ (G.degree v : ℝ)
      else (1 + 5 * ε) * d ≤ (G.degree v : ℝ)) :
    (sampleMeasure (Coin V) p).real
      {ω | v ∈ retained L ω ∧ ((sampledSubgraph G L ω).spanningCoe.degree v : ℝ) ≤
        (1 - 5 * ε / 4) * d} ≤ exp (-ε * d / 100) := by
  apply (retained_degree_below_chernoff G L p v ((1 - 5 * ε / 4) * d)
    (1 / 8) (by norm_num)).trans
  apply exp_le_exp.mpr
  rw [hp]
  have hD0 : 0 ≤ (G.degree v : ℝ) := Nat.cast_nonneg _
  by_cases hv : v ∈ L
  · simp only [hv, ↓reduceIte, pow_one] at hD ⊢
    have hmul := mul_le_mul_of_nonneg_left exp_one_eighth_le (mul_nonneg hD0 hε0)
    have hc : -1 / 8 + 2 * ε / 15 ≤ (0 : ℝ) := by linarith
    have hx := mul_nonpos_of_nonpos_of_nonneg hc (sub_nonneg.mpr hD)
    have hed := mul_nonneg hε0 hd
    nlinarith
  · simp only [hv, ↓reduceIte] at hD ⊢
    have hq : 0 ≤ 1 - (1 - ε) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left exp_one_eighth_le (mul_nonneg hD0 hq)
    have hqd : (G.degree v : ℝ) * (1 - (1 - ε) ^ 2) ≤
        (G.degree v : ℝ) * (2 * ε) := by
      apply mul_le_mul_of_nonneg_left _ hD0
      nlinarith [sq_nonneg ε]
    have hc : -1 / 8 + 4 * ε / 15 ≤ (0 : ℝ) := by linarith
    have hx := mul_nonpos_of_nonpos_of_nonneg hc (sub_nonneg.mpr hD)
    have hed := mul_nonneg hε0 hd
    have hsq := mul_le_mul_of_nonneg_right hε1 hed
    nlinarith

/-- Sharp high-vertex upper tail; M is any original maximum-degree bound. -/
theorem step_high_upper_tail (L : Finset V) (p : unitInterval) (v : V)
    (ε d M : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100)
    (hd : 0 ≤ d) (hdM : d ≤ M) (hDM : (G.degree v : ℝ) ≤ M)
    (hp : (p : ℝ) = 1 - ε) (hv : v ∉ L) :
    (sampleMeasure (Coin V) p).real
      {ω | v ∈ retained L ω ∧ (1 - 7 * ε / 4) * M ≤
        ((sampledSubgraph G L ω).spanningCoe.degree v : ℝ)} ≤ exp (-ε * d / 200) := by
  apply (retained_degree_above_chernoff G L p v ((1 - 7 * ε / 4) * M)
    (-(1 / 16)) (by norm_num)).trans
  apply exp_le_exp.mpr
  simp only [hp, hv, ↓reduceIte]
  have hD0 : 0 ≤ (G.degree v : ℝ) := Nat.cast_nonneg _
  have hM0 : 0 ≤ M := hd.trans hdM
  have hq : 0 ≤ 1 - (1 - ε) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left exp_neg_one_sixteenth_le (mul_nonneg hD0 hq)
  have hc : 0 ≤ 1 / 16 - (1 - (1 - ε) ^ 2) / 17 := by nlinarith [sq_nonneg ε]
  have hx := mul_le_mul_of_nonneg_left hDM hc
  have heM := mul_nonneg hε0 hM0
  have hsq := mul_le_mul_of_nonneg_right hε1 heM
  have heMd := mul_le_mul_of_nonneg_left hdM hε0
  nlinarith

/-- The paper's low-degree class is computed from the original graph. -/
noncomputable def lowVertices (γ d : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => (G.degree v : ℝ) ≤ (1 + γ / 2) * d)

lemma low_degree_upper_threshold (ε γ d : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 100) (hγ : 10 * ε ≤ γ) (hd : 0 ≤ d) :
    (1 + γ / 2) * d ≤ (1 - 7 * ε / 4) * ((1 + γ) * d) := by
  have hγ0 : 0 ≤ γ := by linarith
  have hprod := mul_le_mul_of_nonneg_right hε1 hγ0
  have h : 1 + γ / 2 ≤ (1 - 7 * ε / 4) * (1 + γ) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h hd]

/-- A single retained vertex satisfies the paper's proposed degree window,
except with the displayed genuine probability bound. -/
theorem step_vertex_failure_bound (p : unitInterval) (v : V) (ε γ d : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hγ : 10 * ε ≤ γ) (hd : 0 ≤ d)
    (hp : (p : ℝ) = 1 - ε)
    (hdeg : d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ (1 + γ) * d) :
    (sampleMeasure (Coin V) p).real
      {ω | v ∈ retained (lowVertices G γ d) ω ∧
        (((sampledSubgraph G (lowVertices G γ d) ω).spanningCoe.degree v : ℝ) <
          (1 - 5 * ε / 4) * d ∨
        (1 - 7 * ε / 4) * ((1 + γ) * d) <
          ((sampledSubgraph G (lowVertices G γ d) ω).spanningCoe.degree v : ℝ))} ≤
      2 * exp (-ε * d / 200) := by
  classical
  let L := lowVertices G γ d
  let μ := sampleMeasure (Coin V) p
  let A : Set (Coin V → Bool) := {ω | v ∈ retained L ω ∧
    ((sampledSubgraph G L ω).spanningCoe.degree v : ℝ) < (1 - 5 * ε / 4) * d}
  let B : Set (Coin V → Bool) := {ω | v ∈ retained L ω ∧
    (1 - 7 * ε / 4) * ((1 + γ) * d) <
      ((sampledSubgraph G L ω).spanningCoe.degree v : ℝ)}
  have hD : if v ∈ L then d ≤ (G.degree v : ℝ)
      else (1 + 5 * ε) * d ≤ (G.degree v : ℝ) := by
    split
    · exact hdeg.1
    · rename_i hv
      have hh : (1 + γ / 2) * d < (G.degree v : ℝ) := by
        simpa [L, lowVertices] using hv
      nlinarith [mul_le_mul_of_nonneg_right hγ hd]
  have hA : μ.real A ≤ exp (-ε * d / 200) := by
    calc
      _ ≤ μ.real {ω | v ∈ retained L ω ∧
          ((sampledSubgraph G L ω).spanningCoe.degree v : ℝ) ≤ (1 - 5 * ε / 4) * d} := by
        apply measureReal_mono _ (measure_ne_top _ _)
        exact fun ω h => ⟨h.1, h.2.le⟩
      _ ≤ exp (-ε * d / 100) := step_lower_tail G L p v ε d hε0 hε1 hd hp hD
      _ ≤ _ := exp_le_exp.mpr (by nlinarith [mul_nonneg hε0 hd])
  have hB : μ.real B ≤ exp (-ε * d / 200) := by
    by_cases hv : v ∈ L
    · have hlow : (G.degree v : ℝ) ≤ (1 + γ / 2) * d := by
        simpa [L, lowVertices] using hv
      have hBempty : B = ∅ := by
        ext ω
        simp only [B, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        have hsub : (sampledSubgraph G L ω).spanningCoe.degree v ≤ G.degree v :=
          SimpleGraph.degree_le_of_le (sampledSubgraph G L ω).spanningCoe_le
        have hsubReal : ((sampledSubgraph G L ω).spanningCoe.degree v : ℝ) ≤ G.degree v := by
          exact_mod_cast hsub
        have hthreshold := low_degree_upper_threshold ε γ d hε0 hε1 hγ hd
        linarith [h.2]
      rw [hBempty]
      simp only [measureReal_empty]
      exact (exp_pos _).le
    · have hγ0 : 0 ≤ γ := by linarith
      calc
        _ ≤ μ.real {ω | v ∈ retained L ω ∧
            (1 - 7 * ε / 4) * ((1 + γ) * d) ≤
              ((sampledSubgraph G L ω).spanningCoe.degree v : ℝ)} := by
          apply measureReal_mono _ (measure_ne_top _ _)
          exact fun ω h => ⟨h.1, h.2.le⟩
        _ ≤ _ := step_high_upper_tail G L p v ε d ((1 + γ) * d) hε0 hε1 hd
          (by nlinarith [mul_nonneg hγ0 hd]) hdeg.2 hp hv
  have heq : {ω | v ∈ retained L ω ∧
      (((sampledSubgraph G L ω).spanningCoe.degree v : ℝ) < (1 - 5 * ε / 4) * d ∨
      (1 - 7 * ε / 4) * ((1 + γ) * d) <
        ((sampledSubgraph G L ω).spanningCoe.degree v : ℝ))} = A ∪ B := by
    ext ω
    simp only [A, B, Set.mem_union, Set.mem_ofPred_eq]
    tauto
  change μ.real _ ≤ _
  rw [heq]
  have hu := measureReal_union_le (μ := μ) A B
  linarith

/-- Simultaneous window control, without an assumed good sample. -/
theorem step_all_failure_bound (p : unitInterval) (ε γ d : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hγ : 10 * ε ≤ γ) (hd : 0 ≤ d)
    (hp : (p : ℝ) = 1 - ε)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ (1 + γ) * d) :
    (sampleMeasure (Coin V) p).real
      {ω | ∃ v, v ∈ retained (lowVertices G γ d) ω ∧
        (((sampledSubgraph G (lowVertices G γ d) ω).spanningCoe.degree v : ℝ) <
          (1 - 5 * ε / 4) * d ∨
        (1 - 7 * ε / 4) * ((1 + γ) * d) <
          ((sampledSubgraph G (lowVertices G γ d) ω).spanningCoe.degree v : ℝ))} ≤
      (Fintype.card V : ℝ) * (2 * exp (-ε * d / 200)) := by
  let E : V → Set (Coin V → Bool) := fun v =>
    {ω | v ∈ retained (lowVertices G γ d) ω ∧
      (((sampledSubgraph G (lowVertices G γ d) ω).spanningCoe.degree v : ℝ) <
        (1 - 5 * ε / 4) * d ∨
      (1 - 7 * ε / 4) * ((1 + γ) * d) <
        ((sampledSubgraph G (lowVertices G γ d) ω).spanningCoe.degree v : ℝ))}
  have heq : {ω | ∃ v, ω ∈ E v} = ⋃ v ∈ (Finset.univ : Finset V), E v := by
    ext ω
    simp
  change (sampleMeasure (Coin V) p).real {ω | ∃ v, ω ∈ E v} ≤ _
  rw [heq]
  calc
    _ ≤ ∑ v ∈ (Finset.univ : Finset V), (sampleMeasure (Coin V) p).real (E v) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ (Finset.univ : Finset V), 2 * exp (-ε * d / 200) := by
      apply Finset.sum_le_sum
      intro v _
      exact step_vertex_failure_bound G p v ε γ d hε0 hε1 hγ hd hp (hdeg v)
    _ = _ := by simp

lemma degree_window_improves_ratio (ε γ d : ℝ) (hε0 : 0 ≤ ε)
    (hγ0 : 0 ≤ γ) (hd : 0 ≤ d) :
    (1 - 2 * ε) * d ≤ (1 - 5 * ε / 4) * d ∧
    (1 - 5 * ε / 4) * d ≤ d ∧
    (1 - 7 * ε / 4) * ((1 + γ) * d) ≤
      (1 - ε / 2) * (1 + γ) * ((1 - 5 * ε / 4) * d) := by
  have hed := mul_nonneg hε0 hd
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have hm : 0 ≤ (1 + γ) * d := mul_nonneg (by linarith) hd
  have h : 1 - 7 * ε / 4 ≤ (1 - ε / 2) * (1 - 5 * ε / 4) := by
    nlinarith [sq_nonneg ε]
  nlinarith [mul_le_mul_of_nonneg_right h hm]

                                                                                
                                                                          
theorem regularization_step_failure_probability (p : unitInterval) (ε γ d : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hγ : 10 * ε ≤ γ) (hd : 0 ≤ d)
    (hp : (p : ℝ) = 1 - ε)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ (1 + γ) * d) :
    (sampleMeasure (Coin V) p).real
      {ω | ¬ ∀ v, v ∈ (sampledSubgraph G (lowVertices G γ d) ω).verts →
        (1 - 5 * ε / 4) * d ≤
          ((sampledSubgraph G (lowVertices G γ d) ω).spanningCoe.degree v : ℝ) ∧
        ((sampledSubgraph G (lowVertices G γ d) ω).spanningCoe.degree v : ℝ) ≤
          (1 - ε / 2) * (1 + γ) * ((1 - 5 * ε / 4) * d)} ≤
      (Fintype.card V : ℝ) * (2 * exp (-ε * d / 200)) := by
  apply le_trans _ (step_all_failure_bound G p ε γ d hε0 hε1 hγ hd hp hdeg)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  classical
  simp only [Set.mem_ofPred_eq, not_forall, not_and_or, not_le] at hω
  obtain ⟨v, hv, hbad⟩ := hω
  refine ⟨v, hv, ?_⟩
  rcases hbad with h | h
  · exact Or.inl h
  · exact Or.inr (lt_of_le_of_lt
      (degree_window_improves_ratio ε γ d hε0 (by linarith) hd).2.2 h)

lemma exponential_budget_le_inverse_square (n ε d : ℝ) (hn : 2 ≤ n)
    (hlog : 10000 * log n ≤ ε * d) :
    n * (2 * exp (-ε * d / 200)) ≤ 1 / n ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hl : 0 ≤ log n := log_nonneg (by linarith)
  have he : exp (-ε * d / 200) ≤ 1 / n ^ 4 := by
    calc
      _ ≤ exp (-(4 : ℝ) * log n) := exp_le_exp.mpr (by linarith)
      _ = 1 / n ^ 4 := by
        rw [neg_mul, exp_neg, show exp (4 * log n) = n ^ 4 by
          simpa [exp_log hn0] using exp_nat_mul (log n) 4]
        simp only [one_div]
  calc
    _ ≤ n * (2 * (1 / n ^ 4)) := by gcongr
    _ ≤ 1 / n ^ 2 := by
      apply (le_div_iff₀ (pow_pos hn0 2)).mpr
      field_simp
      nlinarith [sq_nonneg (n - 2)]

/-- The numerical failure guarantee in Lemma 4.1, for n at least two. -/
theorem regularization_step_failure_inverse_square (p : unitInterval) (n ε γ d : ℝ)
    (hn : 2 ≤ n) (hcard : (Fintype.card V : ℝ) ≤ n)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hγ : 10 * ε ≤ γ) (hd : 0 ≤ d)
    (hp : (p : ℝ) = 1 - ε) (hlog : 10000 * log n ≤ ε * d)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ (1 + γ) * d) :
    (sampleMeasure (Coin V) p).real
      {ω | ¬ ∀ v, v ∈ (sampledSubgraph G (lowVertices G γ d) ω).verts →
        (1 - 5 * ε / 4) * d ≤
          ((sampledSubgraph G (lowVertices G γ d) ω).spanningCoe.degree v : ℝ) ∧
        ((sampledSubgraph G (lowVertices G γ d) ω).spanningCoe.degree v : ℝ) ≤
          (1 - ε / 2) * (1 + γ) * ((1 - 5 * ε / 4) * d)} ≤ 1 / n ^ 2 := by
  apply (regularization_step_failure_probability G p ε γ d hε0 hε1 hγ hd hp hdeg).trans
  exact (mul_le_mul_of_nonneg_right hcard (by positivity)).trans
    (exponential_budget_le_inverse_square n ε d hn hlog)

/-- Projection onto the genuinely independent vertex coins. -/
def vertexProjection (ω : Coin V → Bool) : V → Bool := fun v => ω (Sum.inl v)

theorem vertexProjection_measurePreserving (p : unitInterval) :
    MeasurePreserving (vertexProjection (V := V))
      (sampleMeasure (Coin V) p) (sampleMeasure V p) := by
  have hi : iIndepFun (fun i : Coin V => fun ω : Coin V → Bool => ω i)
      (sampleMeasure (Coin V) p) := by
    exact iIndepFun_pi (X := fun _ : Coin V => id)
      (fun _ => measurable_id.aemeasurable)
  have hs := hi.precomp (g := fun v : V => (Sum.inl v : Coin V)) Sum.inl_injective
  refine ⟨measurable_of_finite _, ?_⟩
  change (sampleMeasure (Coin V) p).map (fun ω v => ω (Sum.inl v)) = _
  rw [hs.map_fun_eq_pi_map (fun _ => (measurable_of_finite _).aemeasurable)]
  unfold sampleMeasure
  congr 1
  funext v
  exact (measurePreserving_eval (fun _ : Coin V => bernoulliMeasure true false p)
    (Sum.inl v)).map_eq

/-- The requested existential result depends only on the sampled vertex set,
not on auxiliary edge coins. Nat.card avoids choosing finite instances for H. -/
def HasStepSubgraph (A : V → Bool) (ε γ d : ℝ) : Prop :=
  ∃ H : G.Subgraph, {v | A v = true} ⊆ H.verts ∧
    ∃ d₁ : ℝ, (1 - 2 * ε) * d ≤ d₁ ∧ d₁ ≤ d ∧
      ∀ v, v ∈ H.verts → d₁ ≤ (Nat.card (H.neighborSet v) : ℝ) ∧
        (Nat.card (H.neighborSet v) : ℝ) ≤ (1 - ε / 2) * (1 + γ) * d₁

/-- Graph construction plus the exact measure on A in CJMM Lemma 4.1.
The only restriction beyond the displayed degree and logarithmic conditions is
n at least two; degenerate n can be handled separately. -/
theorem one_step_regularization (p : unitInterval) (n ε γ d : ℝ)
    (hn : 2 ≤ n) (hcard : (Fintype.card V : ℝ) ≤ n)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hγ : 10 * ε ≤ γ) (hd : 0 ≤ d)
    (hp : (p : ℝ) = 1 - ε) (hlog : 10000 * log n ≤ ε * d)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ (1 + γ) * d) :
    (sampleMeasure V p).real {A | ¬ HasStepSubgraph G A ε γ d} ≤ 1 / n ^ 2 := by
  classical
  have hproj := vertexProjection_measurePreserving (V := V) p
  have hmeasure : (sampleMeasure V p).real {A | ¬ HasStepSubgraph G A ε γ d} =
      (sampleMeasure (Coin V) p).real
        {ω | ¬ HasStepSubgraph G (vertexProjection ω) ε γ d} := by
    rw [Measure.real, ← hproj.map_eq, Measure.map_apply hproj.measurable
      (MeasurableSet.of_discrete)]
    rfl
  rw [hmeasure]
  apply le_trans _ (regularization_step_failure_inverse_square G p n ε γ d hn hcard
    hε0 hε1 hγ hd hp hlog hdeg)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hbad hgood
  apply hbad
  refine ⟨sampledSubgraph G (lowVertices G γ d) ω,
    sample_subset_retained _ _, (1 - 5 * ε / 4) * d, ?_, ?_, ?_⟩
  · exact (degree_window_improves_ratio ε γ d hε0 (by linarith) hd).1
  · exact (degree_window_improves_ratio ε γ d hε0 (by linarith) hd).2.1
  · intro v hv
    have heq : Nat.card ((sampledSubgraph G (lowVertices G γ d) ω).neighborSet v) =
        (sampledSubgraph G (lowVertices G γ d) ω).spanningCoe.degree v := by
      rw [SimpleGraph.Subgraph.degree_spanningCoe, SimpleGraph.Subgraph.degree,
        Nat.card_eq_fintype_card]
    rw [heq]
    exact hgood v hv

/-- Success-probability form of the same original-edge subgraph supplier. -/
theorem one_step_regularization_success (p : unitInterval) (n ε γ d : ℝ)
    (hn : 2 ≤ n) (hcard : (Fintype.card V : ℝ) ≤ n)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hγ : 10 * ε ≤ γ) (hd : 0 ≤ d)
    (hp : (p : ℝ) = 1 - ε) (hlog : 10000 * log n ≤ ε * d)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ (1 + γ) * d) :
    1 - 1 / n ^ 2 ≤ (sampleMeasure V p).real {A | HasStepSubgraph G A ε γ d} := by
  have h := one_step_regularization G p n ε γ d hn hcard hε0 hε1 hγ hd hp hlog hdeg
  have hc := measureReal_compl (μ := sampleMeasure V p)
    (s := {A | HasStepSubgraph G A ε γ d}) MeasurableSet.of_discrete
  have heq : ({A | HasStepSubgraph G A ε γ d}ᶜ : Set (V → Bool)) =
      {A | ¬ HasStepSubgraph G A ε γ d} := rfl
  rw [heq] at hc
  simp only [probReal_univ] at hc
  linarith

end Erdos585.Attempt6.RegularizationStep
