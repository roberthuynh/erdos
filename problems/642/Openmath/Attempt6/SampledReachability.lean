import Openmath.Attempt6.Reachability

   
                                                                         
                                                       
                                                                        
                                                                             
                                                                              
                                                                         
                                                                                  
                                                                      
  

namespace Erdos585.Attempt6.SampledReachability

open SimpleGraph MeasureTheory Real Finset
open RobustCore Reachability OAI.ErdosGallai.Sampling

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- All actual original-edge deletion sets of size at most u. -/
def deletionFamily (u : ℕ) : Finset (Finset (Sym2 V)) :=
  (Finset.range (u + 1)).biUnion (fun f => G.edgeFinset.powersetCard f)

theorem mem_deletionFamily (u : ℕ) (F : Finset (Sym2 V)) :
    F ∈ deletionFamily G u ↔ F ⊆ G.edgeFinset ∧ F.card ≤ u := by
  simp only [deletionFamily, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨f, hf, hFG, hcard⟩
    exact ⟨hFG, by omega⟩
  · rintro ⟨hFG, hcard⟩
    exact ⟨F.card, by omega, hFG, rfl⟩

omit [DecidableEq V] in
/-- The graph is simple, so its edge count is at most n squared. -/
theorem edge_count_le_order_sq : G.edgeFinset.card ≤ (Fintype.card V) ^ 2 :=
  G.card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ _)

/-- The deletion-set entropy is polynomial in n with exponent 2u. -/
theorem deletionFamily_card_le (u : ℕ) (hn : 1 ≤ Fintype.card V) :
    (deletionFamily G u).card ≤ (u + 1) * ((Fintype.card V) ^ 2) ^ u := by
  calc
    _ ≤ ∑ f ∈ Finset.range (u + 1), (G.edgeFinset.powersetCard f).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _f ∈ Finset.range (u + 1), ((Fintype.card V) ^ 2) ^ u := by
      apply Finset.sum_le_sum
      intro f hf
      rw [Finset.card_powersetCard]
      have hfu : f ≤ u := by have := Finset.mem_range.mp hf; omega
      exact (Nat.choose_le_pow _ _).trans
        ((Nat.pow_le_pow_left (edge_count_le_order_sq G) f).trans
          (Nat.pow_le_pow_right (by positivity) hfu))
    _ = _ := by simp

/-- Actual seed/deletion pairs with seed size exactly u. -/
def seedDeletionFamily (u : ℕ) : Finset (Finset V × Finset (Sym2 V)) :=
  (Finset.univ.powersetCard u) ×ˢ deletionFamily G u

theorem mem_seedDeletionFamily (u : ℕ) (U : Finset V) (F : Finset (Sym2 V)) :
    (U, F) ∈ seedDeletionFamily G u ↔ U.card = u ∧ F ⊆ G.edgeFinset ∧ F.card ≤ u := by
  simp [seedDeletionFamily, mem_deletionFamily]

/-- CJMM Section 7.5 entropy bound, including the empty deletion set. -/
theorem seedDeletionFamily_card_le (u : ℕ) (hn : 1 ≤ Fintype.card V) :
    (seedDeletionFamily G u).card ≤ (u + 1) * (Fintype.card V) ^ (3 * u) := by
  have hseed : (Finset.univ.powersetCard u : Finset (Finset V)).card ≤
      (Fintype.card V) ^ u := by
    simpa only [Finset.card_powersetCard, Finset.card_univ] using
      Nat.choose_le_pow (Fintype.card V) u
  have hpow : (Fintype.card V) ^ u * ((Fintype.card V) ^ 2) ^ u =
      (Fintype.card V) ^ (3 * u) := by
    rw [← mul_pow, pow_mul]
    congr 1
    ring
  calc
    _ = (Finset.univ.powersetCard u : Finset (Finset V)).card *
        (deletionFamily G u).card := Finset.card_product _ _
    _ ≤ (Fintype.card V) ^ u * ((u + 1) * ((Fintype.card V) ^ 2) ^ u) :=
      Nat.mul_le_mul hseed (deletionFamily_card_le G u hn)
    _ = (u + 1) * ((Fintype.card V) ^ u * ((Fintype.card V) ^ 2) ^ u) := by ring
    _ = _ := by rw [hpow]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Uniform fixed-size failure control using the actual seed/deletion entropy.
P is a deterministic eligibility predicate, for example well-expansion.
Only eligible fixed pairs need a probability estimate. -/
theorem fixed_size_seed_deletion_union_bound (u : ℕ) (hn : 1 ≤ Fintype.card V)
    (P : Finset V → Prop) (E : Finset V → Finset (Sym2 V) → Set Ω)
    (b : ℝ) (hb : 0 ≤ b)
    (hlocal : ∀ U F, U.card = u → P U → F ⊆ G.edgeFinset → F.card ≤ u →
      μ.real (E U F) ≤ b) :
    μ.real {ω | ∃ U F, U.card = u ∧ P U ∧ F ⊆ G.edgeFinset ∧ F.card ≤ u ∧
      ω ∈ E U F} ≤ ((u + 1 : ℕ) : ℝ) * (Fintype.card V : ℝ) ^ (3 * u) * b := by
  classical
  let K : (Finset V × Finset (Sym2 V)) → Set Ω := fun a =>
    {ω | P a.1 ∧ ω ∈ E a.1 a.2}
  have heq : {ω | ∃ U F, U.card = u ∧ P U ∧ F ⊆ G.edgeFinset ∧ F.card ≤ u ∧
      ω ∈ E U F} = ⋃ a ∈ seedDeletionFamily G u, K a := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨U, F, hU, hP, hFG, hF, hE⟩
      exact ⟨(U,F), (mem_seedDeletionFamily G u U F).mpr ⟨hU,hFG,hF⟩, hP, hE⟩
    · rintro ⟨⟨U,F⟩, ha, hP, hE⟩
      obtain ⟨hU,hFG,hF⟩ := (mem_seedDeletionFamily G u U F).mp ha
      exact ⟨U,F,hU,hP,hFG,hF,hE⟩
  have hK : ∀ a ∈ seedDeletionFamily G u, μ.real (K a) ≤ b := by
    rintro ⟨U,F⟩ ha
    obtain ⟨hU,hFG,hF⟩ := (mem_seedDeletionFamily G u U F).mp ha
    by_cases hP : P U
    · have hsub : K (U,F) ⊆ E U F := fun ω hω => hω.2
      exact (measureReal_mono hsub (measure_ne_top _ _)).trans (hlocal U F hU hP hFG hF)
    · have hempty : K (U,F) = ∅ := by ext ω; simp [K,hP]
      simpa only [hempty, measureReal_empty] using hb
  rw [heq]
  calc
    _ ≤ ∑ a ∈ seedDeletionFamily G u, μ.real (K a) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ seedDeletionFamily G u, b := Finset.sum_le_sum hK
    _ = ((seedDeletionFamily G u).card : ℝ) * b := by simp
    _ ≤ (((u + 1) * (Fintype.card V) ^ (3 * u) : ℕ) : ℝ) * b :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast seedDeletionFamily_card_le G u hn) hb
    _ = _ := by push_cast; ring

/-- Summing the valid entropy bounds over seed sizes makes the conclusion
uniform over all nonempty seeds and affordable original-edge deletion sets. -/
theorem all_seed_deletion_union_bound (hn : 1 ≤ Fintype.card V)
    (P : Finset V → Prop) (E : Finset V → Finset (Sym2 V) → Set Ω)
    (b : ℕ → ℝ) (hb : ∀ u, 0 ≤ b u)
    (hlocal : ∀ U F, U.Nonempty → P U → F ⊆ G.edgeFinset → F.card ≤ U.card →
      μ.real (E U F) ≤ b U.card) :
    μ.real {ω | ∃ U F, U.Nonempty ∧ P U ∧ F ⊆ G.edgeFinset ∧ F.card ≤ U.card ∧
      ω ∈ E U F} ≤ ∑ u ∈ Finset.Icc 1 (Fintype.card V),
      ((u + 1 : ℕ) : ℝ) * (Fintype.card V : ℝ) ^ (3 * u) * b u := by
  classical
  let K : ℕ → Set Ω := fun u =>
    {ω | ∃ U F, U.card = u ∧ P U ∧ F ⊆ G.edgeFinset ∧ F.card ≤ u ∧ ω ∈ E U F}
  have heq :
      {ω | ∃ U F, U.Nonempty ∧ P U ∧ F ⊆ G.edgeFinset ∧ F.card ≤ U.card ∧
        ω ∈ E U F} = ⋃ u ∈ Finset.Icc 1 (Fintype.card V), K u := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨U,F,hU,hP,hFG,hF,hE⟩
      refine ⟨U.card, Finset.mem_Icc.mpr ⟨hU.card_pos, Finset.card_le_univ _⟩,
        U,F,rfl,hP,hFG,hF,hE⟩
    · rintro ⟨u,hu,U,F,hU,hP,hFG,hF,hE⟩
      have hpos : 0 < U.card := by have := (Finset.mem_Icc.mp hu).1; omega
      exact ⟨U,F,Finset.card_pos.mp hpos,hP,hFG,by omega,hE⟩
  rw [heq]
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 (Fintype.card V), μ.real (K u) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro u hu
      apply fixed_size_seed_deletion_union_bound G u hn P E (b u) (hb u)
      intro U F hU hP hFG hF
      have hpos : 0 < U.card := by have := (Finset.mem_Icc.mp hu).1; omega
      simpa only [hU] using hlocal U F (Finset.card_pos.mp hpos) hP hFG (by omega)

/-- The literal CJMM Section 7.4 well-expansion eligibility threshold.
L is an ambient scale and is never identified with the actual core order. -/
noncomputable def WellExpandingAt (p : unitInterval) (L : ℝ) (U : Finset V) : Prop :=
  (U.card : ℝ) * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ (externalNeighbors G U).card

                                                                  
                                                                         
                                                                         
                                                                            
                                                                               
theorem exists_uniform_well_expanding_reservoir
    (hn : 1 ≤ Fintype.card V) (p : unitInterval) (L c : ℝ) (r : ℕ)
    (hlocal : ∀ U : Finset V, U.Nonempty → WellExpandingAt G p L U →
      ∀ F : Finset (Sym2 V), F ⊆ G.edgeFinset → F.card ≤ U.card →
      (sampleMeasure V p).real
        {ω | (reservoirBall (G.deleteEdges F) U (sampleVertices ω) r).card ≤
          (sampleVertices ω).card / (2 : ℝ)} ≤ exp (-c * U.card * L ^ 2))
    (hbudget : (∑ u ∈ Finset.Icc 1 (Fintype.card V),
      ((u + 1 : ℕ) : ℝ) * (Fintype.card V : ℝ) ^ (3 * u) * exp (-c * u * L ^ 2)) < 1) :
    ∃ Q : Finset V, ∀ U : Finset V, U.Nonempty → WellExpandingAt G p L U →
      ∀ F : Finset (Sym2 V), F ⊆ G.edgeFinset → F.card ≤ U.card →
      (Q.card : ℝ) / 2 < (reservoirBall (G.deleteEdges F) U Q r).card := by
  classical
  let μ := sampleMeasure V p
  let E : Finset V → Finset (Sym2 V) → Set (V → Bool) := fun U F =>
    {ω | (reservoirBall (G.deleteEdges F) U (sampleVertices ω) r).card ≤
      (sampleVertices ω).card / (2 : ℝ)}
  let A : Set (V → Bool) :=
    {ω | ∃ U F, U.Nonempty ∧ WellExpandingAt G p L U ∧
      F ⊆ G.edgeFinset ∧ F.card ≤ U.card ∧ ω ∈ E U F}
  have hprob : μ.real A < 1 := by
    apply lt_of_le_of_lt _ hbudget
    exact all_seed_deletion_union_bound G hn (WellExpandingAt G p L) E
      (fun u => exp (-c * u * L ^ 2)) (fun _ => (exp_pos _).le)
      (fun U F hU hW hFG hF => hlocal U hU hW F hFG hF)
  let K : Unit → Set (V → Bool) := fun _ => A
  have hfinite : ∑ i ∈ ({()} : Finset Unit), μ.real (K i) < 1 := by
    simpa [K] using hprob
  obtain ⟨ω,hω⟩ := exists_avoiding_finite_events (μ := μ) {()} K hfinite
  refine ⟨sampleVertices ω, ?_⟩
  intro U hU hW F hFG hF
  apply lt_of_not_ge
  intro hbad
  exact hω () (by simp) ⟨U,F,hU,hW,hFG,hF,hbad⟩

omit [DecidableEq V] in
/-- A fresh independent reservoir sample may be tested against an arbitrary
finite history-dependent event. Integrating uniform fixed-history estimates
does not require a union bound over possible histories or adaptive sets.
This is the conditional-probability step used in CJMM Lemma 7.12. The fixed
history estimate itself remains a separate mathematical obligation. -/
theorem fresh_sample_adaptive_failure_bound
    {H : Type*} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (η : Measure H) [IsProbabilityMeasure η] (p : unitInterval)
    (E : H → Set (V → Bool)) (b : ℝ) (hb : 0 ≤ b)
    (hfixed : ∀ h, (sampleMeasure V p).real (E h) ≤ b) :
    (η.prod (sampleMeasure V p)).real {z | z.2 ∈ E z.1} ≤ b := by
  change ((η.prod (sampleMeasure V p)) {z | z.2 ∈ E z.1}).toReal ≤ b
  apply ENNReal.toReal_le_of_le_ofReal hb
  rw [Measure.prod_apply (Set.Finite.measurableSet (Set.toFinite _))]
  calc
    _ ≤ ∫⁻ _h, ENNReal.ofReal b ∂η := by
      apply lintegral_mono
      intro h
      apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hb).mpr
      exact hfixed h
    _ = _ := by simp

/-- Every external vertex having a sampled neighbor in W. This samples the
inside endpoint, as required for the exposed-ball growth step of Lemma 7.12. -/
noncomputable def sampledHitBoundary (W Q : Finset V) : Finset V := by
  classical
  exact (externalNeighbors G W).filter (fun v =>
    (G.neighborFinset v ∩ W ∩ Q).Nonempty)

/-- Concrete history-adaptive boundary-growth failure control under a fresh
sample. The history determines W; the current independent sample determines
which inside endpoints of its boundary edges are selected. -/
theorem adaptive_hit_boundary_failure_bound
    {H : Type*} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (η : Measure H) [IsProbabilityMeasure η] (p : unitInterval)
    (W : H → Finset V) (a b : ℝ) (hb : 0 ≤ b)
    (hfixed : ∀ h, (sampleMeasure V p).real
      {ω | (sampledHitBoundary G (W h) (sampleVertices ω)).card < a * (W h).card} ≤ b) :
    (η.prod (sampleMeasure V p)).real
      {z | (sampledHitBoundary G (W z.1) (sampleVertices z.2)).card < a * (W z.1).card} ≤ b := by
  exact fresh_sample_adaptive_failure_bound η p
    (fun h => {ω | (sampledHitBoundary G (W h) (sampleVertices ω)).card < a * (W h).card})
    b hb hfixed

                                                                             
                                                                        
theorem exists_piece_deletion_le {A : Type*} [DecidableEq A] {k : ℕ}
    (E : Fin k → Finset A) (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (F : Finset A) (a : ℝ) (hk : 0 < k) (hF : (F.card : ℝ) ≤ (k : ℝ) * a) :
    ∃ i : Fin k, ((F ∩ E i).card : ℝ) ≤ a := by
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      ∀ j ∈ (Finset.univ : Finset (Fin k)), i ≠ j →
        Disjoint (F ∩ E i) (F ∩ E j) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e he hi
    exact Finset.disjoint_left.mp (hdisj hij) (Finset.mem_inter.mp he).2
      (Finset.mem_inter.mp hi).2
  have hc : ((Finset.univ : Finset (Fin k)).biUnion (fun i => F ∩ E i)).card =
      ∑ i : Fin k, (F ∩ E i).card := Finset.card_biUnion hd
  have hsub : (Finset.univ : Finset (Fin k)).biUnion (fun i => F ∩ E i) ⊆ F := by
    intro e he
    obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_inter.mp hei).1
  have hsum : (∑ i : Fin k, (F ∩ E i).card) ≤ F.card := by
    rw [← hc]
    exact Finset.card_le_card hsub
  have hsumR : ∑ i : Fin k, ((F ∩ E i).card : ℝ) ≤ ∑ _i : Fin k, a := by
    calc
      _ ≤ (F.card : ℝ) := by exact_mod_cast hsum
      _ ≤ (k : ℝ) * a := hF
      _ = _ := by simp
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le
    (show (Finset.univ : Finset (Fin k)).Nonempty from ⟨⟨0,hk⟩,Finset.mem_univ _⟩) hsumR
  exact ⟨i,hi⟩

omit [Fintype V] [DecidableEq V] in
/-- Literal original-edge reservoir balls are monotone under graph inclusion. -/
theorem reservoirBall_mono_graph {J K : SimpleGraph V} (hJK : J ≤ K)
    (U Q : Finset V) (r : ℕ) :
    reservoirBall J U Q r ⊆ reservoirBall K U Q r := by
  intro v hv
  obtain ⟨hvQ,u,hu,w,hw,hs⟩ := mem_reservoirBall.mp hv
  refine mem_reservoirBall.mpr ⟨hvQ,u,hu,w.mapLe hJK,?_,?_⟩
  · simpa only [SimpleGraph.Walk.length_mapLe] using hw
  · simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hs

omit [DecidableRel G.Adj] in
/-- Deterministic robustness amplification from CJMM Section 7.6.
The same reservoir must be uniformly reachable in every supplied edge-disjoint
piece. This theorem multiplies the deletion allowance by the number of pieces
and transfers the actual paths back to G. It does not construct the pieces. -/
theorem uniform_reachability_of_edge_disjoint_family {k : ℕ}
    (H : Fin k → SimpleGraph V) [∀ i, DecidableRel (H i).Adj]
    (hHG : ∀ i, H i ≤ G)
    (hdisj : Pairwise fun i j => Disjoint (H i).edgeFinset (H j).edgeFinset)
    (Q : Finset V) (r : ℕ) (a : ℝ) (hk : 0 < k)
    (hpieces : ∀ i, ReservoirReachableAt (H i) Q r a) :
    ReservoirReachableAt G Q r ((k : ℝ) * a) := by
  classical
  intro U hU F hFG hF
  obtain ⟨i,hi⟩ := exists_piece_deletion_le (fun i => (H i).edgeFinset) hdisj F
    (a * U.card) hk (by nlinarith [hF])
  let Fi : Finset (Sym2 V) := F ∩ (H i).edgeFinset
  have hlarge := hpieces i U hU Fi (by
    intro e he
    have hemem := (Finset.mem_inter.mp he).2
    simpa only [SimpleGraph.mem_edgeFinset] using hemem) hi
  have hgraph : (H i).deleteEdges (Fi : Set (Sym2 V)) ≤ G.deleteEdges F := by
    intro x y hxy
    simp only [SimpleGraph.deleteEdges_adj, Finset.mem_coe] at hxy ⊢
    refine ⟨hHG i hxy.1, ?_⟩
    intro hdeleted
    apply hxy.2
    exact Finset.mem_inter.mpr ⟨hdeleted, (H i).mem_edgeFinset.mpr hxy.1⟩
  have hc := Finset.card_le_card (reservoirBall_mono_graph hgraph U Q r)
  have hcR :
      ((reservoirBall ((H i).deleteEdges (Fi : Set (Sym2 V))) U Q r).card : ℝ) ≤
        (reservoirBall (G.deleteEdges F) U Q r).card := by exact_mod_cast hc
  exact hlarge.trans_le hcR

/-- Concrete star-case growth count from CJMM Lemma 7.12. Every sampled center
contributes t distinct original external neighbors, and disjoint leaf sets
make these contributions additive. -/
theorem sampled_star_boundary_count (W C Q : Finset V) (leaf : V → Finset V) (t : ℕ)
    (hCW : C ⊆ W)
    (houtside : ∀ c ∈ C, leaf c ⊆ externalNeighbors G W)
    (hadj : ∀ c ∈ C, ∀ v ∈ leaf c, G.Adj c v)
    (hdisj : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → Disjoint (leaf c) (leaf d))
    (hsize : ∀ c ∈ C, (leaf c).card = t) :
    t * (C ∩ Q).card ≤ (sampledHitBoundary G W Q).card := by
  classical
  let S := C ∩ Q
  have hsub : S.biUnion leaf ⊆ sampledHitBoundary G W Q := by
    intro v hv
    obtain ⟨c,hc,hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨hcC,hcQ⟩ := Finset.mem_inter.mp hc
    apply Finset.mem_filter.mpr
    refine ⟨houtside c hcC hv, ?_⟩
    refine ⟨c, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨?_,hCW hcC⟩,hcQ⟩⟩
    exact (G.mem_neighborFinset v c).mpr (hadj c hcC v hv).symm
  have hd : ∀ c ∈ S, ∀ d ∈ S, c ≠ d → Disjoint (leaf c) (leaf d) := by
    intro c hc d hd hcd
    exact hdisj c (Finset.mem_inter.mp hc).1 d (Finset.mem_inter.mp hd).1 hcd
  have hcount : (S.biUnion leaf).card = t * S.card := by
    rw [Finset.card_biUnion hd]
    calc
      _ = ∑ _c ∈ S, t := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hsize c (Finset.mem_inter.mp hc).1
      _ = _ := by simp [Nat.mul_comm]
  change t * S.card ≤ _
  rw [← hcount]
  exact Finset.card_le_card hsub

/-- Actual Bernoulli failure probability for the star alternative in
Lemma 7.12. This proves the sampling step for any supplied valid original-edge
star packing; it does not assume a good reservoir or manufacture the packing. -/
theorem sampled_star_boundary_lower_tail
    (W C : Finset V) (leaf : V → Finset V) (t : ℕ) (ht : 0 < t)
    (hCW : C ⊆ W)
    (houtside : ∀ c ∈ C, leaf c ⊆ externalNeighbors G W)
    (hadj : ∀ c ∈ C, ∀ v ∈ leaf c, G.Adj c v)
    (hdisj : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → Disjoint (leaf c) (leaf d))
    (hsize : ∀ c ∈ C, (leaf c).card = t) (p : unitInterval) :
    (sampleMeasure V p).real
      {ω | ((sampledHitBoundary G W (sampleVertices ω)).card : ℝ) <
        (t : ℝ) * (p : ℝ) * C.card / 2} ≤ exp (-(p : ℝ) * C.card / 8) := by
  apply le_trans _ (sample_card_lower_tail p C)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  have hc := sampled_star_boundary_count G W C (sampleVertices ω) leaf t
    hCW houtside hadj hdisj hsize
  have hcR : (t : ℝ) * (C ∩ sampleVertices ω).card ≤
      ((sampledHitBoundary G W (sampleVertices ω)).card : ℝ) := by exact_mod_cast hc
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  change ((sampledHitBoundary G W (sampleVertices ω)).card : ℝ) <
    (t : ℝ) * (p : ℝ) * C.card / 2 at hω
  change ((C ∩ sampleVertices ω).card : ℝ) ≤ (p : ℝ) * C.card / 2
  nlinarith

/-- The exposed ball used in CJMM Lemma 7.12: the last endpoint is unrestricted;
all other vertices except the starting seed lie in the already exposed layers.
This differs deliberately from reservoirBall, whose endpoint lies in Q. -/
noncomputable def exposedBall (U Q : Finset V) (r : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ u ∈ U, ∃ w : G.Walk u v,
    w.length ≤ r ∧ ∀ x ∈ w.support, x = u ∨ x = v ∨ x ∈ Q)

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem mem_exposedBall (U Q : Finset V) (r : ℕ) (v : V) :
    v ∈ exposedBall G U Q r ↔ ∃ u ∈ U, ∃ w : G.Walk u v,
      w.length ≤ r ∧ ∀ x ∈ w.support, x = u ∨ x = v ∨ x ∈ Q := by
  classical
  simp [exposedBall]

omit [DecidableRel G.Adj] in
/-- A newly sampled inside endpoint makes one more actual original-edge step
available, even when the new outside endpoint has not itself been sampled. -/
theorem exposedBall_extend (U Q R : Finset V) (r : ℕ) {v x : V}
    (hv : v ∈ exposedBall G U Q r) (hvx : G.Adj v x) (hvR : v ∈ R) :
    x ∈ exposedBall G U (Q ∪ R) (r + 1) := by
  obtain ⟨u,hu,w,hw,hs⟩ := (mem_exposedBall G U Q r v).mp hv
  apply (mem_exposedBall G U (Q ∪ R) (r + 1) x).mpr
  refine ⟨u,hu,w.concat hvx,?_,?_⟩
  · simpa only [SimpleGraph.Walk.length_concat] using Nat.add_le_add_right hw 1
  · intro y hy
    simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · rcases hs y hy with hstart | hend | hQ
      · exact Or.inl hstart
      · exact Or.inr (Or.inr (Finset.mem_union_right _ (hend.symm ▸ hvR)))
      · exact Or.inr (Or.inr (Finset.mem_union_left _ hQ))
    · exact Or.inr (Or.inl rfl)

/-- The literal sampled-inside-endpoint boundary supplies new exposed vertices.
The conclusion is exactly the growth inclusion used in CJMM equation (7). -/
theorem hit_boundary_subset_new_exposed_ball (U Q R : Finset V) (r : ℕ) :
    sampledHitBoundary G (exposedBall G U Q r) R ⊆
      exposedBall G U (Q ∪ R) (r + 1) \ exposedBall G U Q r := by
  classical
  intro x hx
  obtain ⟨hxout,hxhit⟩ := Finset.mem_filter.mp hx
  obtain ⟨v,hv⟩ := hxhit
  obtain ⟨hvNW,hvR⟩ := Finset.mem_inter.mp hv
  obtain ⟨hvadj,hvW⟩ := Finset.mem_inter.mp hvNW
  apply Finset.mem_sdiff.mpr
  refine ⟨exposedBall_extend G U Q R r hvW ((G.mem_neighborFinset x v).mp hvadj).symm hvR,?_⟩
  have hnot : x ∉ exposedBall G U Q r ∧
      ∃ v ∈ exposedBall G U Q r, G.Adj v x := by
    simpa only [externalNeighbors, Finset.mem_filter, Finset.mem_compl] using hxout
  exact hnot.1

omit [DecidableRel G.Adj] in
/-- The final fresh layer turns exposed endpoints into genuine reservoir-ball
vertices. This is the literal path inclusion behind CJMM equation (6). -/
theorem exposedBall_inter_subset_reservoirBall (U Q R : Finset V) (r : ℕ) :
    exposedBall G U Q r ∩ R ⊆ reservoirBall G U (Q ∪ R) r := by
  intro v hv
  obtain ⟨hvB,hvR⟩ := Finset.mem_inter.mp hv
  obtain ⟨u,hu,w,hw,hs⟩ := (mem_exposedBall G U Q r v).mp hvB
  apply mem_reservoirBall.mpr
  refine ⟨Finset.mem_union_right _ hvR,u,hu,w,hw,?_⟩
  intro x hx
  rcases hs x hx with hstart | hend | hQ
  · exact Or.inl hstart
  · exact Or.inr (Finset.mem_union_right _ (hend.symm ▸ hvR))
  · exact Or.inr (Finset.mem_union_left _ hQ)

/-- Actual exposed-ball growth under the star alternative, paid by a fresh
Bernoulli sample of centers. This supplies the probabilistic star step of
Lemma 7.12 for any valid star packing of the current literal exposed ball. -/
theorem sampled_star_exposed_ball_growth_tail
    (U Q C : Finset V) (r : ℕ) (leaf : V → Finset V) (t : ℕ) (ht : 0 < t)
    (hCW : C ⊆ exposedBall G U Q r)
    (houtside : ∀ c ∈ C, leaf c ⊆ externalNeighbors G (exposedBall G U Q r))
    (hadj : ∀ c ∈ C, ∀ v ∈ leaf c, G.Adj c v)
    (hdisj : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → Disjoint (leaf c) (leaf d))
    (hsize : ∀ c ∈ C, (leaf c).card = t) (p : unitInterval) :
    (sampleMeasure V p).real
      {ω | ((exposedBall G U (Q ∪ sampleVertices ω) (r + 1) \
        exposedBall G U Q r).card : ℝ) < (t : ℝ) * (p : ℝ) * C.card / 2} ≤
      exp (-(p : ℝ) * C.card / 8) := by
  apply le_trans _ (sampled_star_boundary_lower_tail G (exposedBall G U Q r) C leaf t ht
    hCW houtside hadj hdisj hsize p)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  have hc := Finset.card_le_card (hit_boundary_subset_new_exposed_ball G U Q (sampleVertices ω) r)
  have hcR : ((sampledHitBoundary G (exposedBall G U Q r) (sampleVertices ω)).card : ℝ) ≤
      ((exposedBall G U (Q ∪ sampleVertices ω) (r + 1) \ exposedBall G U Q r).card : ℝ) := by
    exact_mod_cast hc
  exact lt_of_le_of_lt hcR hω

/-- History-adaptive original-edge exposed-ball growth for the star alternative.
The earlier layers and star packing may depend on the entire finite history;
the current layer is genuinely independent, through the product measure.
The lower center-count bound controls the failure probability uniformly over
all histories, without enumerating their exponentially many possible values. -/
theorem adaptive_star_exposed_ball_growth_tail
    {H : Type*} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (η : Measure H) [IsProbabilityMeasure η] (U : Finset V)
    (Q C : H → Finset V) (r : ℕ) (leaf : H → V → Finset V)
    (t : ℕ) (ht : 0 < t) (m : ℝ)
    (hCW : ∀ h, C h ⊆ exposedBall G U (Q h) r)
    (houtside : ∀ h, ∀ c ∈ C h, leaf h c ⊆ externalNeighbors G (exposedBall G U (Q h) r))
    (hadj : ∀ h, ∀ c ∈ C h, ∀ v ∈ leaf h c, G.Adj c v)
    (hdisj : ∀ h, ∀ c ∈ C h, ∀ d ∈ C h, c ≠ d → Disjoint (leaf h c) (leaf h d))
    (hsize : ∀ h, ∀ c ∈ C h, (leaf h c).card = t)
    (hcenters : ∀ h, m ≤ ((C h).card : ℝ)) (p : unitInterval) :
    (η.prod (sampleMeasure V p)).real
      {z | ((exposedBall G U (Q z.1 ∪ sampleVertices z.2) (r + 1) \
        exposedBall G U (Q z.1) r).card : ℝ) <
          (t : ℝ) * (p : ℝ) * (C z.1).card / 2} ≤ exp (-(p : ℝ) * m / 8) := by
  apply fresh_sample_adaptive_failure_bound η p
    (fun h => {ω | ((exposedBall G U (Q h ∪ sampleVertices ω) (r + 1) \
      exposedBall G U (Q h) r).card : ℝ) < (t : ℝ) * (p : ℝ) * (C h).card / 2})
    (exp (-(p : ℝ) * m / 8)) (exp_pos _).le
  intro h
  calc
    _ ≤ exp (-(p : ℝ) * (C h).card / 8) :=
      sampled_star_exposed_ball_growth_tail G U (Q h) (C h) r (leaf h) t ht
        (hCW h) (houtside h) (hadj h) (hdisj h) (hsize h) p
    _ ≤ _ := exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left (hcenters h) p.property.1])

/-- A simple explicit bound on the complete entropy sum. A fixed-pair failure
exp(-c*u*L squared) beats the n^(3u) possibilities when the displayed ratio is
small. This bound includes every seed size, with no hidden asymptotic notation. -/
theorem entropy_series_le (n : ℕ) (L c : ℝ)
    (hsmall : (n : ℝ) ^ 3 * exp (-c * L ^ 2) ≤ 1) :
    (∑ u ∈ Finset.Icc 1 n,
      ((u + 1 : ℕ) : ℝ) * (n : ℝ) ^ (3 * u) * exp (-c * u * L ^ 2)) ≤
      (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) ^ 3 * exp (-c * L ^ 2)) := by
  let R := (n : ℝ) ^ 3 * exp (-c * L ^ 2)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := hsmall
  have hpower (u : ℕ) :
      (n : ℝ) ^ (3 * u) * exp (-c * u * L ^ 2) = R ^ u := by
    dsimp [R]
    rw [pow_mul, mul_pow]
    congr 1
    rw [← exp_nat_mul]
    congr 1
    ring
  have hterm : ∀ u ∈ Finset.Icc 1 n,
      ((u + 1 : ℕ) : ℝ) * (n : ℝ) ^ (3 * u) * exp (-c * u * L ^ 2) ≤
        ((n : ℝ) + 1) * R := by
    intro u hu
    have hu1 : 1 ≤ u := (Finset.mem_Icc.mp hu).1
    have hun : u ≤ n := (Finset.mem_Icc.mp hu).2
    have hcast : ((u + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hun 1
    have hp : R ^ u ≤ R := pow_le_of_le_one hR0 hR1 (by omega)
    calc
      _ = ((u + 1 : ℕ) : ℝ) *
          ((n : ℝ) ^ (3 * u) * exp (-c * u * L ^ 2)) := by ring
      _ = ((u + 1 : ℕ) : ℝ) * R ^ u := by rw [hpower]
      _ ≤ ((n : ℝ) + 1) * R ^ u := mul_le_mul_of_nonneg_right hcast (pow_nonneg hR0 _)
      _ ≤ ((n : ℝ) + 1) * R := mul_le_mul_of_nonneg_left hp (by positivity)
  calc
    _ ≤ ∑ _u ∈ Finset.Icc 1 n, ((n : ℝ) + 1) * R := Finset.sum_le_sum hterm
    _ = (n : ℝ) * ((n : ℝ) + 1) * R := by simp [Nat.card_Icc]; ring
    _ = _ := rfl

/-- Actual external vertices with at least d original neighbors in U. -/
noncomputable def robustNeighborhood (J : SimpleGraph V) [DecidableRel J.Adj]
    (U : Finset V) (d : ℝ) : Finset V := by
  classical
  exact (externalNeighbors J U).filter (fun v => d ≤ ((J.neighborFinset v ∩ U).card : ℝ))

/-- CJMM Proposition 7.6 with an explicit ambient logarithmic scale.
The proof deletes the actual low-incidence crossing edges and invokes the
robust certificate once; it supplies a concrete prerequisite of Lemma 7.7. -/
theorem robust_neighborhood_alternative
    (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (hU : 1 ≤ U.card)
    (hsmall : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3)
    (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset)
    (hF : (F.card : ℝ) ≤ s * U.card / 2)
    (d : ℝ) (hd : 0 < d) :
    s * U.card / (2 * d) ≤ ((externalNeighbors (G.deleteEdges F) U).card : ℝ) ∨
      epsilon * U.card / L ^ 2 ≤ ((robustNeighborhood (G.deleteEdges F) U d).card : ℝ) := by
  classical
  let J := G.deleteEdges F
  let N := externalNeighbors J U
  let B := N.filter (fun v => ((J.neighborFinset v ∩ U).card : ℝ) < d)
  let D : Finset (Sym2 V) := B.biUnion (fun v =>
    (J.neighborFinset v ∩ U).image (fun u => s(u,v)))
  by_cases hlarge : s * U.card / (2 * d) ≤ (N.card : ℝ)
  · exact Or.inl hlarge
  apply Or.inr
  have hN : (N.card : ℝ) < s * U.card / (2 * d) := lt_of_not_ge hlarge
  have hDcost : (D.card : ℝ) ≤ d * N.card := by
    have hbi := Finset.card_biUnion_le (s := B)
      (t := fun v => (J.neighborFinset v ∩ U).image (fun u => s(u,v)))
    have hbiR : (D.card : ℝ) ≤ ∑ v ∈ B,
        (((J.neighborFinset v ∩ U).image (fun u => s(u,v))).card : ℝ) := by exact_mod_cast hbi
    calc
      _ ≤ ∑ v ∈ B, (((J.neighborFinset v ∩ U).image (fun u => s(u,v))).card : ℝ) := hbiR
      _ ≤ ∑ v ∈ B, ((J.neighborFinset v ∩ U).card : ℝ) := by
        apply Finset.sum_le_sum
        intro v _
        exact_mod_cast Finset.card_image_le
      _ ≤ ∑ _v ∈ B, d := by
        apply Finset.sum_le_sum
        intro v hv
        exact (Finset.mem_filter.mp hv).2.le
      _ = d * B.card := by simp [mul_comm]
      _ ≤ d * N.card := mul_le_mul_of_nonneg_left
        (by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)) hd.le
  have hDhalf : (D.card : ℝ) ≤ s * U.card / 2 := by
    have hmul := (lt_div_iff₀ (by positivity : 0 < 2 * d)).mp hN
    nlinarith
  have hDG : D ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨v,hv,he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
    have hjuv : J.Adj v u := (J.mem_neighborFinset v u).mp (Finset.mem_inter.mp hu).1
    have hguv : G.Adj u v := (SimpleGraph.deleteEdges_adj.mp hjuv).1.symm
    exact G.mem_edgeFinset.mpr hguv
  have hFDG : F ∪ D ⊆ G.edgeFinset := Finset.union_subset hFG hDG
  have hcost : ((F ∪ D).card : ℝ) ≤ s * U.card := by
    have hc : ((F ∪ D).card : ℝ) ≤ (F.card : ℝ) + D.card := by
      exact_mod_cast Finset.card_union_le F D
    linarith
  have hexpand := hG U hU hsmall (F ∪ D) (by
    simpa only [Finset.subset_iff, SimpleGraph.mem_edgeFinset] using hFDG) hcost
  have hsub : externalNeighbors (G.deleteEdges (F ∪ D : Finset (Sym2 V))) U ⊆
      robustNeighborhood J U d := by
    intro x hx
    have hxpath : x ∉ U ∧ ∃ u ∈ U, (G.deleteEdges (F ∪ D : Finset (Sym2 V))).Adj u x := by
      simpa only [externalNeighbors, Finset.mem_filter, Finset.mem_compl] using hx
    obtain ⟨u,hu,hux⟩ := hxpath.2
    have huxG : G.Adj u x := (SimpleGraph.deleteEdges_adj.mp hux).1
    have hnot : s(u,x) ∉ (F ∪ D : Finset (Sym2 V)) := (SimpleGraph.deleteEdges_adj.mp hux).2
    have hnotF : s(u,x) ∉ F := fun he => hnot (Finset.mem_union_left _ he)
    have huxJ : J.Adj u x := SimpleGraph.deleteEdges_adj.mpr ⟨huxG,hnotF⟩
    have hxN : x ∈ N := by
      simp only [N, externalNeighbors, Finset.mem_filter, Finset.mem_compl]
      exact ⟨hxpath.1,u,hu,huxJ⟩
    have hdegree : d ≤ ((J.neighborFinset x ∩ U).card : ℝ) := by
      by_contra hn
      have hxB : x ∈ B := Finset.mem_filter.mpr ⟨hxN,lt_of_not_ge hn⟩
      have heD : s(u,x) ∈ D := by
        apply Finset.mem_biUnion.mpr
        refine ⟨x,hxB,Finset.mem_image.mpr ⟨u,?_,rfl⟩⟩
        exact Finset.mem_inter.mpr ⟨(J.mem_neighborFinset x u).mpr huxJ.symm,hu⟩
      exact hnot (Finset.mem_union_right _ heD)
    exact Finset.mem_filter.mpr ⟨hxN,hdegree⟩
  have hcard :
      ((externalNeighbors (G.deleteEdges (F ∪ D : Finset (Sym2 V))) U).card : ℝ) ≤
        ((robustNeighborhood J U d).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  exact hexpand.trans hcard

end Erdos585.Attempt6.SampledReachability
