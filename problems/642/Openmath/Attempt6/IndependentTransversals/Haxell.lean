/-
Copyright (c) 2025 Pjotr Buys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys
-/
import Openmath.Attempt6.IndependentTransversals.AugmentingSequences

   
                  

                                                                                         

               

                                                                           
                                               

             

                                                         
                                                               
  

namespace IndependentTransversals

variable {V : Type*} [DecidableEq V] [Fintype V]

section Haxell

variable (G : PartitionedGraph V) [DecidableRel G.graph.Adj]

/-! ## Small Reusable Counting Lemmas

These lemmas support both the standard Haxell theorem and the precolor variant
with a constraint set C. The key insight is that when we want to exclude both
the neighborhood N(C_m) and an additional constraint set C from V_{B_m}, we need:
  |V_{B_m}| > |N(C_m) ∩ V_{B_m}| + |C ∩ V_{B_m}|
-/

/-- If a set A has more elements than can be covered by B ∪ C (restricted to A),
    there exists an element in A avoiding both B and C.
    This is the pigeonhole principle for exclusion. -/
lemma Set.exists_mem_not_mem_of_ncard_gt_union {α : Type*} {A B C : Set α}
    (_hA_fin : A.Finite)
    (h_gt : A.ncard > (B ∩ A).ncard + (C ∩ A).ncard) :
    ∃ x ∈ A, x ∉ B ∧ x ∉ C := by
  -- If every element of A is in B or C, then A ⊆ B ∪ C
  by_contra h_all
  push_neg at h_all
  -- h_all : ∀ x ∈ A, x ∈ B ∨ x ∈ C
  have h_sub : A ⊆ B ∪ C := by
    intro x hx
    have h := h_all x hx
    by_cases hB : x ∈ B
    · left; exact hB
    · right; exact h hB
  have h_eq : A = (A ∩ B) ∪ (A ∩ C) := by
    ext x
    constructor
    · intro hx
      have hx_BC := h_sub hx
      rcases hx_BC with hB | hC
      · left; exact ⟨hx, hB⟩
      · right; exact ⟨hx, hC⟩
    · intro hx
      rcases hx with ⟨hxA, _⟩ | ⟨hxA, _⟩ <;> exact hxA
  have h_ncard : A.ncard ≤ (A ∩ B).ncard + (A ∩ C).ncard := by
    calc A.ncard = ((A ∩ B) ∪ (A ∩ C)).ncard := by rw [← h_eq]
      _ ≤ (A ∩ B).ncard + (A ∩ C).ncard := Set.ncard_union_le (A ∩ B) (A ∩ C)
  rw [Set.inter_comm A B, Set.inter_comm A C] at h_ncard
  omega

/-- The main counting inequality for precolor: Δ|C_m| + |C| < |V_{B_m}|.
    This ensures we can find v ∈ V_{B_m} avoiding both N(C_m) and C.

    Note: This requires the additional assumption that |C| ≤ |uncovered blocks|,
    which holds in the precolor setting where C = T ∩ X and each element of C
    corresponds to an uncovered block. -/
lemma PartitionedGraph.counting_with_constraint (t : G.FeasibleTuple)
    (h_thick : G.isThick (2 * G.maxDegree))
    (h_all_pos : ∀ i, i < t.seq.length → 0 < G.degreeAt t.S t.seq (i + 1))
    (h_not_full : (G.uncoveredBlocks t.S).Nonempty)
    (h_C_bound : t.C.ncard < G.maxDegree)
    (h_C_uncov : t.C.ncard ≤ (G.uncoveredBlocks t.S).ncard) :
    let m := t.seq.length
    let C_m := G.vertexSeq t.S t.C t.seq m
    let B_m := G.blocksSeq t.S t.seq m
    let V_Bm := G.blockUnion B_m
    G.maxDegree * C_m.ncard + t.C.ncard < V_Bm.ncard := by
  intro m C_m B_m V_Bm
  -- Step 1: |V_{B_m}| ≥ 2Δ|B_m| (thickness)
  have h_Bm_size : V_Bm.ncard ≥ 2 * G.maxDegree * B_m.ncard := by
    have hB_sub : B_m ⊆ G.blocks := G.blocksSeq_subset t.S t.seq m
    have hB_fin : B_m.Finite := Set.toFinite B_m
    have h_thick_Bm : ∀ U ∈ B_m, 2 * G.maxDegree ≤ U.ncard := fun U hU => h_thick U (hB_sub hU)
    exact G.ncard_blockUnion_ge_of_thick hB_sub hB_fin (2 * G.maxDegree) h_thick_Bm
  -- Step 2: Get the bounds
  let deg_sum := ((G.degreeSeq t.S t.seq).take m).sum
  have h_Bm_eq : B_m.ncard = (G.uncoveredBlocks t.S).ncard + deg_sum :=
    G.blocksSeq_card_eq t.S t.C t.seq t.isPartialIT t.isAugmenting m (le_refl m)
  have h_Cm_bound := G.vertexSeq_card_bound t m (le_refl m)
  -- Step 3: Σdᵢ ≥ m
  have h_sum_ge_m : m ≤ deg_sum := by
    have h_deg_len : (G.degreeSeq t.S t.seq).length = m := by
      simp only [degreeSeq, List.length_mapIdx, m]
    have h_take_all : (G.degreeSeq t.S t.seq).take m = G.degreeSeq t.S t.seq :=
      List.take_of_length_le (le_of_eq h_deg_len)
    simp only [deg_sum, h_take_all]
    have h_all_pos' : ∀ i (hi : i < (G.degreeSeq t.S t.seq).length),
        0 < (G.degreeSeq t.S t.seq)[i] := by
      intro i hi
      rw [h_deg_len] at hi
      simp only [degreeSeq, List.getElem_mapIdx]
      simp only [degreeAt] at h_all_pos
      have h_seq_idx : t.seq[(i + 1) - 1]? = some t.seq[i] := by
        simp only [Nat.add_sub_cancel]
        exact List.getElem?_eq_getElem hi
      specialize h_all_pos i hi
      simp only [h_seq_idx] at h_all_pos
      exact h_all_pos
    have h_sum_ge : (G.degreeSeq t.S t.seq).length ≤ (G.degreeSeq t.S t.seq).sum := by
      have : ∀ l : List ℕ, (∀ i (hi : i < l.length), 0 < l[i]) → l.length ≤ l.sum := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons x xs ih =>
          intro h_pos
          simp only [List.length_cons, List.sum_cons]
          have h_x_pos : 0 < x := h_pos 0 (Nat.zero_lt_succ _)
          have h_ih : xs.length ≤ xs.sum :=
            ih (fun i hi => h_pos (i + 1) (Nat.add_lt_add_right hi 1))
          omega
      exact this _ h_all_pos'
    rw [h_deg_len] at h_sum_ge
    exact h_sum_ge
  have h_uncovered_pos : 0 < (G.uncoveredBlocks t.S).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 h_not_full
  -- Step 4: The key calculation
  -- We need: Δ|C_m| + |C| < |V_{B_m}|
  -- Strategy: Show (Δ+1)|C| + 2ΔΣdᵢ < 2Δ|uncov| + 2ΔΣdᵢ
  -- i.e., (Δ+1)|C| < 2Δ|uncov|
  -- Case Δ ≥ 2: (Δ+1)|C| ≤ (Δ+1)|uncov| < 2Δ|uncov| (since Δ+1 < 2Δ for Δ ≥ 2)
  -- Case Δ = 1: |C| < 1 means |C| = 0, so (Δ+1)|C| = 0 < 2|uncov|
  -- Case Δ = 0: |C| < 0 is impossible, handled separately

  -- Use omega with all the bounds
  -- Key facts:
  -- h_Bm_size: V_Bm.ncard ≥ 2 * Δ * |B_m|
  -- h_Bm_eq: |B_m| = |uncov| + deg_sum
  -- h_Cm_bound: |C_m| ≤ |C| + m + deg_sum
  -- h_sum_ge_m: m ≤ deg_sum
  -- h_uncovered_pos: 0 < |uncov|
  -- h_C_bound: |C| < Δ
  -- h_C_uncov: |C| ≤ |uncov|
  -- Goal: Δ * |C_m| + |C| < V_Bm.ncard

  -- The proof works by showing:
  -- Δ|C_m| + |C| ≤ Δ(|C| + m + deg_sum) + |C|
  --             ≤ Δ|C| + Δ*deg_sum + Δ*deg_sum + |C|  (using m ≤ deg_sum)
  --             = (Δ+1)|C| + 2Δ*deg_sum
  --             < 2Δ|uncov| + 2Δ*deg_sum  (using (Δ+1)|C| < 2Δ|uncov|)
  --             = 2Δ(|uncov| + deg_sum)
  --             = 2Δ|B_m|
  --             ≤ V_Bm.ncard

  -- For the key inequality (Δ+1)|C| < 2Δ|uncov|:
  -- If Δ = 0: |C| < 0 impossible, so vacuously true
  -- If Δ = 1: |C| < 1 so |C| = 0, then 0 < 2|uncov| ✓
  -- If Δ ≥ 2: (Δ+1)|C| ≤ (Δ+1)|uncov| < 2Δ|uncov| (since Δ+1 < 2Δ and |uncov| > 0)
  by_cases h_delta_zero : G.maxDegree = 0
  · -- Case Δ = 0: impossible since |C| < 0 would be required
    simp only [h_delta_zero] at h_C_bound
    omega
  · by_cases h_delta_one : G.maxDegree = 1
    · -- Case Δ = 1: |C| = 0
      have h_C_zero : t.C.ncard = 0 := by omega
      simp only [h_C_zero, Nat.add_zero]
      have h_Cm_bound' : C_m.ncard ≤ m + deg_sum := by
        calc C_m.ncard ≤ t.C.ncard + m + deg_sum := h_Cm_bound
          _ = 0 + m + deg_sum := by rw [h_C_zero]
          _ = m + deg_sum := by omega
      have h_Cm_bound'' : C_m.ncard ≤ 2 * deg_sum := by omega
      calc G.maxDegree * C_m.ncard = 1 * C_m.ncard := by rw [h_delta_one]
        _ = C_m.ncard := Nat.one_mul _
        _ ≤ 2 * deg_sum := h_Cm_bound''
        _ < 2 * (G.uncoveredBlocks t.S).ncard + 2 * deg_sum := by omega
        _ = 2 * ((G.uncoveredBlocks t.S).ncard + deg_sum) := by rw [Nat.mul_add]
        _ = 2 * G.maxDegree * ((G.uncoveredBlocks t.S).ncard + deg_sum) := by rw [h_delta_one]
        _ = 2 * G.maxDegree * B_m.ncard := by rw [← h_Bm_eq]
        _ ≤ V_Bm.ncard := h_Bm_size
    · -- Case Δ ≥ 2
      have h_delta_ge_2 : G.maxDegree ≥ 2 := by omega
      -- Key inequality: (Δ+1)|C| < 2Δ|uncov|
      have h_key : (G.maxDegree + 1) * t.C.ncard <
          2 * G.maxDegree * (G.uncoveredBlocks t.S).ncard := by
        have h1 : (G.maxDegree + 1) * t.C.ncard ≤
            (G.maxDegree + 1) * (G.uncoveredBlocks t.S).ncard :=
          Nat.mul_le_mul_left _ h_C_uncov
        have h_coeff : G.maxDegree + 1 < 2 * G.maxDegree := by omega
        have h2 : (G.maxDegree + 1) * (G.uncoveredBlocks t.S).ncard <
            2 * G.maxDegree * (G.uncoveredBlocks t.S).ncard :=
          Nat.mul_lt_mul_of_pos_right h_coeff h_uncovered_pos
        exact Nat.lt_of_le_of_lt h1 h2
      -- Upper bound on Δ|C_m| + |C|
      have h_upper : G.maxDegree * C_m.ncard + t.C.ncard ≤
          (G.maxDegree + 1) * t.C.ncard + 2 * G.maxDegree * deg_sum := by
        have h_mul : G.maxDegree * C_m.ncard ≤ G.maxDegree * (t.C.ncard + m + deg_sum) :=
          Nat.mul_le_mul_left _ h_Cm_bound
        have h_m_bound : G.maxDegree * m ≤ G.maxDegree * deg_sum := Nat.mul_le_mul_left _ h_sum_ge_m
        -- Key: expand the RHS to make omega work
        have h_rhs_eq : (G.maxDegree + 1) * t.C.ncard + 2 * G.maxDegree * deg_sum =
            G.maxDegree * t.C.ncard + t.C.ncard +
            (G.maxDegree * deg_sum + G.maxDegree * deg_sum) := by
          simp only [Nat.add_mul, Nat.one_mul, Nat.two_mul]
        rw [h_rhs_eq]
        -- Now show: Δ|C_m| + |C| ≤ Δ|C| + |C| + 2Δ·deg_sum
        have h_expand : G.maxDegree * (t.C.ncard + m + deg_sum) =
            G.maxDegree * t.C.ncard + G.maxDegree * m + G.maxDegree * deg_sum := by
          simp only [Nat.mul_add]
        calc G.maxDegree * C_m.ncard + t.C.ncard
          ≤ G.maxDegree * (t.C.ncard + m + deg_sum) + t.C.ncard := Nat.add_le_add_right h_mul _
          _ = G.maxDegree * t.C.ncard + G.maxDegree * m + G.maxDegree * deg_sum + t.C.ncard := by
              rw [h_expand]
          _ ≤ G.maxDegree * t.C.ncard + G.maxDegree * deg_sum +
                G.maxDegree * deg_sum + t.C.ncard := by omega
          _ = G.maxDegree * t.C.ncard + t.C.ncard +
                (G.maxDegree * deg_sum + G.maxDegree * deg_sum) := by omega
      -- Lower bound on V_Bm.ncard
      have h_lower : 2 * G.maxDegree * (G.uncoveredBlocks t.S).ncard + 2 * G.maxDegree * deg_sum ≤
          V_Bm.ncard := by
        calc 2 * G.maxDegree * (G.uncoveredBlocks t.S).ncard + 2 * G.maxDegree * deg_sum
          = 2 * G.maxDegree * ((G.uncoveredBlocks t.S).ncard + deg_sum) := by rw [Nat.mul_add]
          _ = 2 * G.maxDegree * B_m.ncard := by rw [← h_Bm_eq]
          _ ≤ V_Bm.ncard := h_Bm_size
      -- Combine
      calc G.maxDegree * C_m.ncard + t.C.ncard
        ≤ (G.maxDegree + 1) * t.C.ncard + 2 * G.maxDegree * deg_sum := h_upper
        _ < 2 * G.maxDegree * (G.uncoveredBlocks t.S).ncard + 2 * G.maxDegree * deg_sum :=
            Nat.add_lt_add_right h_key _
        _ ≤ V_Bm.ncard := h_lower

/-- Variant of `can_extend_sequence` that works with a bounded constraint set C.
    This is the key lemma for precolor: we find v ∈ V_{B_m} such that:
    1. v is not adjacent to C_m (can continue augmenting sequence)
    2. v ∉ C (the new vertex avoids the constraint set)

    The additional hypothesis `h_C_uncov` captures that in the precolor setting,
    each element of C corresponds to an uncovered block. -/
lemma PartitionedGraph.can_extend_sequence_with_constraint (t : G.FeasibleTuple)
    (h_thick : G.isThick (2 * G.maxDegree))
    (h_all_pos : ∀ i, i < t.seq.length → 0 < G.degreeAt t.S t.seq (i + 1))
    (h_not_full : (G.uncoveredBlocks t.S).Nonempty)
    (h_C_bound : t.C.ncard < G.maxDegree)
    (h_C_uncov : t.C.ncard ≤ (G.uncoveredBlocks t.S).ncard) :
    ∃ v ∈ G.blockUnion (G.blocksSeq t.S t.seq t.seq.length),
      Disjoint (G.graph.neighborSet v) (G.vertexSeq t.S t.C t.seq t.seq.length) ∧
      v ∉ t.C := by
  let m := t.seq.length
  let B_m := G.blocksSeq t.S t.seq m
  let C_m := G.vertexSeq t.S t.C t.seq m
  let V_Bm := G.blockUnion B_m
  -- The counting inequality: Δ|C_m| + |C| < |V_{B_m}|
  have h_count := G.counting_with_constraint t h_thick h_all_pos h_not_full h_C_bound h_C_uncov
  -- We need to find v ∈ V_{B_m} with:
  --   v ∉ ⋃ c ∈ C_m, N(c)  (equivalently: N(v) ∩ C_m = ∅)
  --   v ∉ C
  -- The set to avoid is: (⋃ c ∈ C_m, N(c) ∩ V_{B_m}) ∪ (C ∩ V_{B_m})
  -- Size: |(⋃ c ∈ C_m, N(c) ∩ V_{B_m})| ≤ Δ|C_m| and |C ∩ V_{B_m}| ≤ |C|
  -- So total to avoid ≤ Δ|C_m| + |C| < |V_{B_m}| (by h_count)
  let avoid_nbhd := ⋃ c ∈ C_m, G.graph.neighborSet c ∩ V_Bm
  let avoid_C := t.C ∩ V_Bm
  -- Size bounds
  have h_nbhd_size : avoid_nbhd.ncard ≤ G.maxDegree * C_m.ncard :=
    G.ncard_biUnion_neighborSet_inter_le (Set.toFinite C_m)
  have h_C_size : avoid_C.ncard ≤ t.C.ncard := Set.ncard_inter_le_ncard_left t.C V_Bm
  -- Total size to avoid
  have h_total_avoid : (avoid_nbhd ∩ V_Bm).ncard + (avoid_C ∩ V_Bm).ncard < V_Bm.ncard := by
    have h1 : (avoid_nbhd ∩ V_Bm).ncard ≤ avoid_nbhd.ncard := Set.ncard_inter_le_ncard_left _ _
    have h2 : avoid_nbhd.ncard ≤ G.maxDegree * C_m.ncard := h_nbhd_size
    have h4 : avoid_C.ncard ≤ t.C.ncard := h_C_size
    -- avoid_C ∩ V_Bm = (C ∩ V_Bm) ∩ V_Bm = C ∩ V_Bm = avoid_C
    have h5 : avoid_C ∩ V_Bm = avoid_C := Set.inter_eq_left.mpr Set.inter_subset_right
    calc (avoid_nbhd ∩ V_Bm).ncard + (avoid_C ∩ V_Bm).ncard
      = (avoid_nbhd ∩ V_Bm).ncard + avoid_C.ncard := by rw [h5]
      _ ≤ avoid_nbhd.ncard + avoid_C.ncard := Nat.add_le_add_right h1 _
      _ ≤ G.maxDegree * C_m.ncard + t.C.ncard := Nat.add_le_add h2 h4
      _ < V_Bm.ncard := h_count
  -- Apply pigeonhole
  have h_exists := Set.exists_mem_not_mem_of_ncard_gt_union (Set.toFinite V_Bm) h_total_avoid
  obtain ⟨v, hv_mem, hv_not_nbhd, hv_not_C⟩ := h_exists
  use v, hv_mem
  constructor
  · -- Disjoint (neighborSet v) C_m
    rw [Set.disjoint_left]
    intro w hw_Nv hw_Cm
    apply hv_not_nbhd
    -- avoid_nbhd = ⋃ c ∈ C_m, N(c) ∩ V_Bm
    -- Need: v ∈ ⋃ c ∈ C_m, N(c) ∩ V_Bm
    -- w ∈ C_m, w ∈ N(v), v ∈ V_Bm
    -- So v ∈ N(w) ∩ V_Bm, and N(w) ∩ V_Bm ⊆ ⋃ c ∈ C_m, N(c) ∩ V_Bm
    exact Set.mem_biUnion hw_Cm ⟨G.graph.adj_symm hw_Nv, hv_mem⟩
  · -- v ∉ C
    intro hv_C
    apply hv_not_C
    exact ⟨hv_C, hv_mem⟩

/-- Key counting lemma: If all degrees in the sequence are positive, then
    |V_{B_m}| > Δ · |C_m|, so we can extend the sequence.

    Proof outline:
    1. By Equation 2.1, |C_m| ≤ |C| + m + Σᵢdᵢ
    2. By Equation 2.1, |B_m| ≤ |U\U_S| + Σᵢdᵢ
    3. Each block in B_m has size ≥ 2Δ (by thickness)
    4. So |V_{B_m}| ≥ 2Δ · |B_m|
    5. The neighborhood of C_m in V_{B_m} has size ≤ Δ · |C_m|
    6. By 2Δ > Δ and counting, there exists v ∈ V_{B_m} not in this neighborhood -/
lemma PartitionedGraph.can_extend_sequence (t : G.FeasibleTuple)
    (h_thick : G.isThick (2 * G.maxDegree))
    (h_all_pos : ∀ i, i < t.seq.length → 0 < G.degreeAt t.S t.seq (i + 1))
    (h_not_full : (G.uncoveredBlocks t.S).Nonempty)
    (h_C_empty : t.C = ∅) :
    ∃ v ∈ G.blockUnion (G.blocksSeq t.S t.seq t.seq.length),
      Disjoint (G.graph.neighborSet v) (G.vertexSeq t.S t.C t.seq t.seq.length) := by
  -- The proof uses a counting/pigeonhole argument
  let m := t.seq.length
  let B_m := G.blocksSeq t.S t.seq m
  let C_m := G.vertexSeq t.S t.C t.seq m
  let V_Bm := G.blockUnion B_m
  -- Step 1: |V_{B_m}| ≥ 2Δ · |B_m| by thickness
  -- Each block in B_m has size ≥ 2Δ, so sum of sizes ≥ 2Δ · (number of blocks)
  have h_Bm_size : V_Bm.ncard ≥ 2 * G.maxDegree * B_m.ncard := by
    -- Thickness: every block has size ≥ 2Δ
    -- V_Bm is the union of blocks in B_m
    -- Since blocks are disjoint, |V_Bm| = Σ_{U ∈ B_m} |U| ≥ Σ_{U ∈ B_m} 2Δ = 2Δ · |B_m|
    have hB_sub : B_m ⊆ G.blocks := G.blocksSeq_subset t.S t.seq m
    have hB_fin : B_m.Finite := Set.toFinite B_m
    have h_thick_Bm : ∀ U ∈ B_m, 2 * G.maxDegree ≤ U.ncard := by
      intro U hU
      exact h_thick U (hB_sub hU)
    exact G.ncard_blockUnion_ge_of_thick hB_sub hB_fin (2 * G.maxDegree) h_thick_Bm
  -- Step 2: The neighborhood of C_m in V_{B_m} has size ≤ Δ · |C_m|
  -- Each vertex in C_m has at most Δ neighbors total
  have h_nbhd_size : (⋃ c ∈ C_m, G.graph.neighborSet c ∩ V_Bm).ncard ≤ G.maxDegree * C_m.ncard := by
    -- Each vertex has degree ≤ Δ, so union of neighborhoods has size ≤ Δ · |C_m|
    exact G.ncard_biUnion_neighborSet_inter_le (Set.toFinite C_m)
  -- Step 3: By counting, V_Bm has a vertex not adjacent to anything in C_m
  -- We need: |⋃ c ∈ C_m, N(c) ∩ V_Bm| < |V_Bm|
  -- Then there exists v ∈ V_Bm with v ∉ ⋃ c ∈ C_m, N(c)
  -- Such v satisfies: for all c ∈ C_m, v ∉ N(c), i.e., ¬Adj c v
  -- Hence N(v) is disjoint from C_m
  -- The key inequality: Δ · |C_m| < 2Δ · |B_m|, i.e., |C_m| < 2|B_m|
  -- This follows from the bounds when the sequence is constructed properly
  have h_key_ineq : (⋃ c ∈ C_m, G.graph.neighborSet c ∩ V_Bm).ncard < V_Bm.ncard := by
    -- Strategy: show Δ · |C_m| < |V_Bm|
    -- We have: |V_Bm| ≥ 2Δ · |B_m| and |⋃ N(c) ∩ V_Bm| ≤ Δ · |C_m|
    -- Key bounds from Equation 2.1:
    -- |C_m| ≤ |C| + m + Σdᵢ
    -- |B_m| ≥ |uncoveredBlocks| (since B_0 = uncoveredBlocks and blocksSeq is monotone)
    -- First, B_m is nonempty (contains uncoveredBlocks which is nonempty)
    have h_Bm_nonempty : B_m.Nonempty := by
      have h_sub := G.uncoveredBlocks_subset_blocksSeq t.S t.seq m (le_refl m)
      exact Set.Nonempty.mono h_sub h_not_full
    -- V_Bm is nonempty since B_m is nonempty and each block is nonempty
    have h_V_Bm_nonempty : V_Bm.Nonempty := by
      obtain ⟨U, hU⟩ := h_Bm_nonempty
      have hU_blocks : U ∈ G.blocks := G.blocksSeq_subset t.S t.seq m hU
      have hU_nonempty := G.nonempty_of_mem hU_blocks
      obtain ⟨v, hv⟩ := hU_nonempty
      use v
      change v ∈ G.blockUnion B_m
      simp only [blockUnion, Set.mem_sUnion]
      exact ⟨U, Set.mem_inter hU hU_blocks, hv⟩
    -- Use the bounds: need Δ · |C_m| < 2Δ · |B_m|
    -- Use Equation 2.1 bounds
    have h_Cm_bound := G.vertexSeq_card_bound t m (le_refl m)
    have h_Bm_lower : (G.uncoveredBlocks t.S).ncard ≤ B_m.ncard := by
      have h_sub := G.uncoveredBlocks_subset_blocksSeq t.S t.seq m (le_refl m)
      exact Set.ncard_le_ncard h_sub (Set.toFinite _)
    -- Case split on whether C_m is empty or not
    by_cases h_Cm_empty : C_m = ∅
    · -- C_m = ∅: then ⋃ is empty, ncard = 0 < V_Bm.ncard (since V_Bm is nonempty)
      simp only [h_Cm_empty, Set.mem_empty_iff_false, Set.iUnion_of_empty, Set.iUnion_empty,
        Set.ncard_empty]
      exact (Set.ncard_pos (Set.toFinite _)).2 h_V_Bm_nonempty
    · -- C_m ≠ ∅: need the full counting argument
      -- Key insight: for augmenting sequences, |B_m| = |uncovered| + Σd_i (equality!)
      -- This is because v_k is not adjacent to C_{k-1},
      -- so N_S(v_k) is disjoint from ⋃_{i<k} N_S(v_i)
      -- Hence each step adds exactly d_k new covered blocks
      -- With C = ∅: |C_m| ≤ m + Σd_i and |B_m| = |uncovered| + Σd_i
      -- For |C_m| < 2|B_m|: m + Σd_i < 2(|uncovered| + Σd_i) = 2|uncovered| + 2Σd_i
      -- This simplifies to: m < 2|uncovered| + Σd_i
      -- Since each d_i ≥ 1 (from h_all_pos), Σd_i ≥ m, so 2|uncovered| + Σd_i ≥ 2 + m > m ✓
      let deg_sum := ((G.degreeSeq t.S t.seq).take m).sum
      -- Key equality: |B_m| = |uncovered| + Σd_i for augmenting sequences (Eq 2.1 in paper)
      -- Proof by induction on m:
      -- - Base (m=0): B_0 = uncoveredBlocks, deg_sum = 0
      -- - Step: B_{k+1} = B_k ∪ blocksIntersecting(N_S(v_k))
      --   Key insight: The new blocks are DISJOINT from B_k because:
      --   a) If U ∈ blocksIntersecting(N_S(v_k)) ∩ B_k, then U contains some s ∈ S
      --   b) Either U is uncovered (contradicts s ∈ S ∩ U nonempty) or
      --      U intersects N_S(v_j) for some j < k
      --   c) If U intersects both N_S(v_j) and N_S(v_k), there's s ∈ S ∩ U in both
      --      neighborhoods. Since S is a partial IT, |S ∩ U| ≤ 1, so s ∈ N(v_j) ∩ N(v_k).
      --   d) But s ∈ N(v_j) ∩ S means s ∈ C_k, and Disjoint(N(v_k), C_k) gives contradiction.
      -- Also: |blocksIntersecting(N_S(v_k))| = d_k because each s ∈ N_S(v_k) ⊆ S is in
      --       a distinct block (partial IT property).
      have h_Bm_eq : B_m.ncard = (G.uncoveredBlocks t.S).ncard + deg_sum := by
        -- Use the key equality lemma (Equation 2.1)
        exact G.blocksSeq_card_eq t.S t.C t.seq t.isPartialIT t.isAugmenting m (le_refl m)
      -- Σd_i ≥ m since each d_i ≥ 1 (from h_all_pos)
      have h_sum_ge_m : m ≤ deg_sum := by
        -- Each degree d_i > 0 for i < m
        -- degreeSeq has length = seq.length = m
        have h_deg_len : (G.degreeSeq t.S t.seq).length = m := by
          simp only [degreeSeq, List.length_mapIdx, m]
        have h_take_all : (G.degreeSeq t.S t.seq).take m = G.degreeSeq t.S t.seq := by
          exact List.take_of_length_le (le_of_eq h_deg_len)
        simp only [deg_sum, h_take_all]
        -- Now show: m ≤ (degreeSeq t.S t.seq).sum
        -- Each element of degreeSeq is > 0, so sum ≥ length = m
        have h_all_pos' : ∀ i (hi : i < (G.degreeSeq t.S t.seq).length),
            0 < (G.degreeSeq t.S t.seq)[i] := by
          intro i hi
          rw [h_deg_len] at hi
          simp only [degreeSeq, List.getElem_mapIdx]
          -- degreeAt t.S t.seq (i + 1) = N(seq[i]) ∩ S).ncard
          simp only [degreeAt] at h_all_pos
          have h_seq_idx : t.seq[(i + 1) - 1]? = some t.seq[i] := by
            simp only [Nat.add_sub_cancel]
            exact List.getElem?_eq_getElem hi
          specialize h_all_pos i hi
          simp only [h_seq_idx] at h_all_pos
          exact h_all_pos
        -- Sum of positive naturals is at least the count
        have h_sum_ge : (G.degreeSeq t.S t.seq).length ≤ (G.degreeSeq t.S t.seq).sum := by
          have : ∀ l : List ℕ, (∀ i (hi : i < l.length), 0 < l[i]) → l.length ≤ l.sum := by
            intro l
            induction l with
            | nil => intro _; simp
            | cons x xs ih =>
              intro h_pos
              simp only [List.length_cons, List.sum_cons]
              have h_x_pos : 0 < x :=
                h_pos 0 (by simp only [List.length_cons]; omega)
              have h_ih : xs.length ≤ xs.sum :=
                ih (fun i hi =>
                  h_pos (i + 1) (by simp only [List.length_cons]; omega))
              omega
          exact this _ h_all_pos'
        rw [h_deg_len] at h_sum_ge
        exact h_sum_ge
      have h_C_ncard : t.C.ncard = 0 := by simp only [h_C_empty, Set.ncard_empty]
      have h_Cm_bound' : C_m.ncard ≤ m + deg_sum := by
        have h := h_Cm_bound
        simp only [h_C_ncard, zero_add] at h ⊢
        exact h
      have h_uncovered_pos : 0 < (G.uncoveredBlocks t.S).ncard :=
        (Set.ncard_pos (Set.toFinite _)).2 h_not_full
      -- |C_m| < 2|B_m| follows from the bounds
      have h_Cm_lt_2Bm : C_m.ncard < 2 * B_m.ncard := by
        have h1 : C_m.ncard ≤ m + deg_sum := h_Cm_bound'
        have h2 : m ≤ deg_sum := h_sum_ge_m
        have h3 : 0 < (G.uncoveredBlocks t.S).ncard := h_uncovered_pos
        have h4 : B_m.ncard = (G.uncoveredBlocks t.S).ncard + deg_sum := h_Bm_eq
        omega
      -- Need Δ > 0: if Δ = 0, all degrees are 0, contradicting h_all_pos when m > 0
      have h_delta_pos : 0 < G.maxDegree := by
        -- C_m ≠ ∅ and C = ∅ implies m > 0
        have h_m_pos : 0 < m := by
          by_contra h_m_zero
          push_neg at h_m_zero
          have h_m_eq : m = 0 := Nat.le_zero.mp h_m_zero
          -- If m = 0, then C_m = vertexSeq t.S t.C t.seq 0 = t.C = ∅
          have : C_m = t.C := by
            simp only [C_m, h_m_eq]
            rfl  -- vertexSeq S C seq 0 = C by definition
          rw [h_C_empty] at this
          exact h_Cm_empty this
        -- h_all_pos at i = 0 gives d_1 > 0
        have h_d1_pos : 0 < G.degreeAt t.S t.seq 1 := h_all_pos 0 h_m_pos
        -- degreeAt t.S t.seq 1 = |N(seq[0]) ∩ S|
        simp only [degreeAt] at h_d1_pos
        have h_idx : t.seq[0]? = some t.seq[0] := List.getElem?_eq_getElem h_m_pos
        simp only [h_idx] at h_d1_pos
        -- |N(seq[0]) ∩ S| > 0 means seq[0] has a neighbor in S
        have h_nbhd_nonempty : (G.graph.neighborSet t.seq[0] ∩ t.S).Nonempty :=
          (Set.ncard_pos (Set.toFinite _)).mp h_d1_pos
        obtain ⟨s, hs_nbhd, _⟩ := h_nbhd_nonempty
        -- s is a neighbor of seq[0], so degree(seq[0]) ≥ 1, hence maxDegree ≥ 1
        have h_adj : G.graph.Adj t.seq[0] s := hs_nbhd
        have h_deg_pos : 0 < G.graph.degree t.seq[0] := by
          rw [SimpleGraph.degree, Finset.card_pos]
          use s
          simp only [SimpleGraph.mem_neighborFinset]
          exact h_adj
        exact Nat.lt_of_lt_of_le h_deg_pos (SimpleGraph.degree_le_maxDegree G.graph t.seq[0])
      calc (⋃ c ∈ C_m, G.graph.neighborSet c ∩ V_Bm).ncard
        ≤ G.maxDegree * C_m.ncard := h_nbhd_size
        _ < 2 * G.maxDegree * B_m.ncard := by
          have h_lt : G.maxDegree * C_m.ncard < G.maxDegree * (2 * B_m.ncard) :=
            Nat.mul_lt_mul_of_pos_left h_Cm_lt_2Bm h_delta_pos
          have h_assoc : G.maxDegree * (2 * B_m.ncard) = 2 * G.maxDegree * B_m.ncard := by
            rw [← Nat.mul_assoc, Nat.mul_comm G.maxDegree 2, Nat.mul_assoc]
          rw [h_assoc] at h_lt
          exact h_lt
        _ ≤ V_Bm.ncard := h_Bm_size
  -- Apply pigeonhole
  have h_exists := Set.exists_mem_notMem_of_ncard_lt_ncard h_key_ineq (Set.toFinite _)
  obtain ⟨v, hv_mem, hv_not_in_nbhd⟩ := h_exists
  use v, hv_mem
  -- v ∉ ⋃ c ∈ C_m, N(c) ∩ V_Bm means for all c ∈ C_m, v ∉ N(c) ∩ V_Bm
  -- Since v ∈ V_Bm, this means v ∉ N(c) for all c ∈ C_m
  -- Hence N(v) ∩ C_m = ∅
  rw [Set.disjoint_left]
  intro w hw_in_Nv hw_in_Cm
  apply hv_not_in_nbhd
  simp only [Set.mem_iUnion]
  use w, hw_in_Cm
  exact ⟨G.graph.adj_symm hw_in_Nv, hv_mem⟩

                                                                                
                                                    
lemma list_lex_of_prefix_and_lt {l1 l2 : List ℕ} {k : ℕ}
    (hk_lt_l1 : k < l1.length) (hk_lt_l2 : k < l2.length)
    (h_eq : ∀ i (hi : i < k), l1[i]'(Nat.lt_of_lt_of_le hi (Nat.le_of_lt hk_lt_l1)) =
                              l2[i]'(Nat.lt_of_lt_of_le hi (Nat.le_of_lt hk_lt_l2)))
    (h_lt : l1[k] < l2[k]) :
    List.Lex (· < ·) l1 l2 := by
  -- Prove by strong induction on k
  induction k generalizing l1 l2 with
  | zero =>
                                             
    match l1, l2 with
    | a :: l1', b :: l2' =>
      simp only [List.getElem_cons_zero] at *
      exact List.Lex.rel h_lt
    | [], _ => simp at hk_lt_l1
    | _, [] => simp at hk_lt_l2
  | succ k' ih =>
    -- k = k' + 1: first elements equal, recurse on tails
    match l1, l2 with
    | a :: l1', b :: l2' =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk_lt_l1 hk_lt_l2
      -- a = b (from h_eq at i = 0)
      have hab : a = b := by
        have h0 := h_eq 0 (Nat.zero_lt_succ k')
        simp only [List.getElem_cons_zero] at h0
        exact h0
      rw [hab]
      apply List.Lex.cons
      -- Apply induction on tails
      apply ih hk_lt_l1 hk_lt_l2
      · intro i hi
        have h_succ := h_eq (i + 1) (Nat.add_lt_add_right hi 1)
        simp only [List.getElem_cons_succ] at h_succ
        convert h_succ using 2
      · simp only [List.getElem_cons_succ] at h_lt ⊢
        convert h_lt using 2
    | [], _ => simp at hk_lt_l1
    | _, [] => simp at hk_lt_l2

                                                                           
lemma not_prefix_of_ne_at {l1 l2 : List ℕ} {k : ℕ}
    (hk_lt_l1 : k < l1.length)
    (hk_lt_l2 : k < l2.length)
    (h_ne : l1[k] ≠ l2[k]) :
    ¬(l1 <+: l2) := by
  intro h_prefix
  have h_eq := List.IsPrefix.getElem h_prefix hk_lt_l1
  exact h_ne h_eq

omit [DecidableRel G.graph.Adj] in
/-- If d_m = 0, we can improve the partial IT or reduce the sequence.

    Proof outline (from the paper):
    Since d_m = 0, the last vertex v_m has no neighbors in S (N_S(v_m) = ∅).
    This means v_m is independent from S.

    Let k be the smallest index for which v_m ∈ V_{B_k}.

    Case 1 (k = 0): v_m is in an uncovered block.
      Then S' = S ∪ {v_m} is a strictly larger partial IT.
      The tuple (S', ∅, []) has |S'| > |S|.

    Case 2 (k ≥ 1): v_m is in a block U that was added at step k.
      This means U ∈ blocksIntersecting(N_S(v_k)), so there exists s ∈ S ∩ U ∩ N(v_k).
      Since d_m = 0, we have v_m ≁ s (v_m has no S-neighbors).
      Let S' = S ⊕ v_m = (S \ U) ∪ {v_m} (replace s with v_m).
      Let seq' = (v_1, ..., v_k) (truncate the sequence).
      Then |S'| = |S| and d_i(seq') = d_i(seq) for i < k, but d_k(seq') = d_k(seq) - 1
      because s was the unique S-neighbor of v_k in U. -/
lemma PartitionedGraph.improve_from_zero_degree (t : G.FeasibleTuple)
    (h_nonempty : t.seq ≠ [])
    (h_last_zero : G.degreeAt t.S t.seq t.seq.length = 0) :
    ∃ t' : G.FeasibleTuple, t'.C = ∅ ∧
        (∀ x ∈ t'.S, x ∈ t.S ∨ ∃ i, ∃ _ : i < t.seq.length, x = t.seq[i]) ∧
        (∀ x ∈ t'.seq, x ∈ t.seq) ∧
        G.FeasibleTupleLt t' t := by
  have h_len_pos : 0 < t.seq.length := List.length_pos_of_ne_nil h_nonempty
  let m := t.seq.length - 1
  have hm : m < t.seq.length := Nat.sub_one_lt_of_lt h_len_pos
  have hm_eq : m + 1 = t.seq.length := Nat.sub_add_cancel h_len_pos
  let v_m := t.seq[m]
  -- d_m = 0 means v_m has no neighbors in S
  have h_no_neighbors : G.graph.neighborSet v_m ∩ t.S = ∅ := by
    rw [← Set.ncard_eq_zero]
    simp only [degreeAt] at h_last_zero
    have hseq : t.seq.length - 1 < t.seq.length := by omega
    simp only [List.getElem?_eq_getElem hseq] at h_last_zero
    exact h_last_zero
  -- v_m is independent from all vertices in S
  have h_indep : ∀ s ∈ t.S, ¬G.graph.Adj v_m s := by
    intro s hs hadj
    have : s ∈ G.graph.neighborSet v_m ∩ t.S := ⟨hadj, hs⟩
    rw [h_no_neighbors] at this
    exact this
  -- From augmenting property: v_m ∈ V_{B_m}
  have h_aug := t.isAugmenting ⟨m, hm⟩
  have h_vm_in_Bm : v_m ∈ G.blockUnion (G.blocksSeq t.S t.seq m) := h_aug.1
  -- v_m is in some block U ∈ B_m
  have ⟨U, hU_in_Bm, hv_in_U⟩ : ∃ U ∈ G.blocksSeq t.S t.seq m, v_m ∈ U := by
    have hBm_sub : G.blocksSeq t.S t.seq m ⊆ G.blocks := G.blocksSeq_subset t.S t.seq m
    rw [G.blockUnion_eq_sUnion hBm_sub] at h_vm_in_Bm
    exact Set.mem_sUnion.mp h_vm_in_Bm
  have hU_blocks : U ∈ G.blocks := G.blocksSeq_subset t.S t.seq m hU_in_Bm
  -- Use the blocksSeq_mem_cases lemma to analyze U's membership
  rcases G.blocksSeq_mem_cases t.S t.seq U m (le_of_lt hm) hU_in_Bm with
    hU_uncov | ⟨k, hk_len, hk_lt_m, hU_from_k⟩
  · -- Case 1: U ∈ uncoveredBlocks S (k = 0 case)
    -- S ∩ U = ∅ (U is uncovered)
    have hS_disjoint_U : Disjoint t.S U := by
      simp only [uncoveredBlocks, blocksIntersecting] at hU_uncov
      simp only [Set.mem_diff, Set.mem_setOf_eq, not_and] at hU_uncov
      have := hU_uncov.2 hU_blocks
      rw [Set.not_nonempty_iff_eq_empty, Set.inter_comm] at this
      exact Set.disjoint_iff_inter_eq_empty.mpr this
    -- S' = S ∪ {v_m} is independent (v_m has no S-neighbors)
    let S' := t.S ∪ {v_m}
    have hS'_indep : G.graph.IsIndepSet S' := by
      intro x hx y hy hne
      simp only [S', Set.mem_union, Set.mem_singleton_iff] at hx hy
      rcases hx, hy with ⟨hxS | hx_eq, hyS | hy_eq⟩
      · exact t.isPartialIT.1 hxS hyS hne
      · subst hy_eq; exact fun hadj => h_indep x hxS (G.graph.adj_symm hadj)
      · subst hx_eq; exact h_indep y hyS
      · subst hx_eq hy_eq; exact (hne rfl).elim
    -- S' is a partial IT
    have hS'_partial : G.IsPartialIT S' := by
      constructor
      · exact hS'_indep
      · intro U' hU'
        by_cases hU'_eq : U' = U
        · -- U' is the (now covered) block containing v_m
          rw [hU'_eq]
          have h_inter : S' ∩ U = {v_m} := by
            ext x
            simp only [S', Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
            constructor
            · intro ⟨hx_S', hx_U⟩
              rcases hx_S' with hxS | hx_eq
              · exact (Set.disjoint_left.mp hS_disjoint_U hxS hx_U).elim
              · exact hx_eq
            · intro hx_eq; subst hx_eq; exact ⟨Or.inr rfl, hv_in_U⟩
          rw [h_inter, Set.ncard_singleton]
        · -- U' ≠ U: v_m ∉ U' since blocks are disjoint
          have hv_not_in_U' : v_m ∉ U' := by
            intro hv_U'
            have hdisj := G.pairwiseDisjoint hU_blocks hU' (Ne.symm hU'_eq)
            exact Set.disjoint_left.mp hdisj hv_in_U hv_U'
          have h_inter : S' ∩ U' = t.S ∩ U' := by
            ext x
            simp only [S', Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
            constructor
            · intro ⟨hx_S', hx_U'⟩
              rcases hx_S' with hxS | hx_eq
              · exact ⟨hxS, hx_U'⟩
              · subst hx_eq; exact (hv_not_in_U' hx_U').elim
            · intro ⟨hxS, hx_U'⟩; exact ⟨Or.inl hxS, hx_U'⟩
          rw [h_inter]
          exact t.isPartialIT.2 U' hU'
    -- Construct the new feasible tuple with larger S
    let t' : G.FeasibleTuple := ⟨S', ∅, [], hS'_partial, Set.empty_subset _, fun k => Fin.elim0 k⟩
    use t'
    refine ⟨rfl, ?_, ?_, ?_⟩
    · -- t'.S ⊆ t.S ∪ {v_m}: every element is in t.S or is a seq element
      intro x hx
      have hx : x ∈ S' := hx
      simp only [S', Set.mem_union, Set.mem_singleton_iff] at hx
      rcases hx with hxS | hx_eq
      · left; exact hxS
      · right; exact ⟨m, hm, hx_eq⟩
    · -- t'.seq = []: vacuously true
      intro x hx; exact (List.not_mem_nil hx).elim
    · left  -- |S'| > |S|
      have hv_not_in_S : v_m ∉ t.S := Set.disjoint_left.mp hS_disjoint_U.symm hv_in_U
      calc S'.ncard = (t.S ∪ {v_m}).ncard := rfl
        _ = t.S.ncard + ({v_m} : Set V).ncard :=
            Set.ncard_union_eq (Set.disjoint_singleton_right.mpr hv_not_in_S)
        _ = t.S.ncard + 1 := by simp only [Set.ncard_singleton]
        _ > t.S.ncard := by omega
  · -- Case 2: U ∈ blocksIntersecting(N_S(seq[k])) for some k < m
    -- This means U contains some s ∈ S ∩ N(seq[k])
    simp only [blocksIntersecting, Set.mem_setOf_eq] at hU_from_k
    obtain ⟨_, s, hs_U, hs_NS⟩ := hU_from_k
    have hs_S : s ∈ t.S := hs_NS.2
    have hs_Nk : G.graph.Adj t.seq[k] s := hs_NS.1
    -- Key: v_m and s are in the same block U, but v_m ≁ s (since d_m = 0)
    have _h_vm_not_adj_s : ¬G.graph.Adj v_m s := h_indep s hs_S
    -- S' = S ⊕ v_m = (S \ U) ∪ {v_m}
    -- Note: We use blockOf v_m = U (since v_m ∈ U and blocks are unique)
    have hU_eq_blockOf : U = G.blockOf v_m := G.blockOf_unique v_m U hU_blocks hv_in_U
    let S' := G.oplus t.S v_m
    -- S' is independent: v_m is not adjacent to any vertex in S
    have hS'_indep : G.graph.IsIndepSet S' := by
      intro x hx y hy hne
      simp only [S', oplus, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff] at hx hy
      rcases hx, hy with ⟨⟨hxS, hxU⟩ | hx_eq, ⟨hyS, hyU⟩ | hy_eq⟩
      · exact t.isPartialIT.1 hxS hyS hne
      · subst hy_eq
        intro hadj
        exact h_indep x hxS (G.graph.adj_symm hadj)
      · subst hx_eq
        exact h_indep y hyS
      · subst hx_eq hy_eq; exact (hne rfl).elim
    -- S' is a partial IT
    have hS'_partial : G.IsPartialIT S' := by
      constructor
      · exact hS'_indep
      · intro U' hU'
        by_cases hU'_eq : U' = G.blockOf v_m
        · -- U' is v_m's block: S' ∩ U' = {v_m}
          rw [hU'_eq]
          have h_inter : S' ∩ G.blockOf v_m = {v_m} := by
            ext x
            simp only [S', oplus, Set.mem_inter_iff, Set.mem_union, Set.mem_diff,
              Set.mem_singleton_iff]
            constructor
            · intro ⟨hx_S', hx_U⟩
              rcases hx_S' with ⟨hxS, hxU⟩ | hx_eq
              · exact (hxU hx_U).elim
              · exact hx_eq
            · intro hx_eq; subst hx_eq; exact ⟨Or.inr rfl, G.mem_blockOf v_m⟩
          rw [h_inter, Set.ncard_singleton]
        · -- U' ≠ blockOf v_m: S' ∩ U' = S ∩ U' (removing s doesn't affect other blocks)
          have h_inter : S' ∩ U' = t.S ∩ U' := by
            ext x
            simp only [S', oplus, Set.mem_inter_iff, Set.mem_union, Set.mem_diff,
              Set.mem_singleton_iff]
            constructor
            · intro ⟨hx_S', hx_U'⟩
              rcases hx_S' with ⟨hxS, _⟩ | hx_eq
              · exact ⟨hxS, hx_U'⟩
              · -- x = v_m ∈ U', but v_m ∈ blockOf v_m ≠ U', contradiction
                subst hx_eq
                have hdisj := G.pairwiseDisjoint (G.blockOf_mem v_m) hU' (fun h => hU'_eq h.symm)
                exact (Set.disjoint_left.mp hdisj (G.mem_blockOf v_m) hx_U').elim
            · intro ⟨hxS, hx_U'⟩
              -- x ∈ S and x ∈ U' ≠ blockOf v_m, so x ∉ blockOf v_m
              have hx_not_in_block : x ∉ G.blockOf v_m := by
                intro hx_block
                have hdisj := G.pairwiseDisjoint (G.blockOf_mem v_m) hU' (fun h => hU'_eq h.symm)
                exact Set.disjoint_left.mp hdisj hx_block hx_U'
              exact ⟨Or.inl ⟨hxS, hx_not_in_block⟩, hx_U'⟩
          rw [h_inter]
          exact t.isPartialIT.2 U' hU'
    -- The truncated sequence seq' = t.seq.take (k + 1)
    let seq' := t.seq.take (k + 1)
    have h_seq'_len : seq'.length = k + 1 := by
      simp only [seq', List.length_take]
      -- k < m and m < seq.length, so k + 1 ≤ m + 1 ≤ seq.length
      have h_k1_le : k + 1 ≤ t.seq.length := by
        have : k + 1 ≤ m + 1 := Nat.add_le_add_right (Nat.le_of_lt hk_lt_m) 1
        omega
      exact Nat.min_eq_left h_k1_le
    -- Helper 1: uncoveredBlocks S' = uncoveredBlocks t.S
    -- Both S and S' cover the same blocks: U was covered by S (s ∈ S ∩ U) and
    -- is covered by S' (v_m ∈ S' ∩ U). Other blocks are unchanged.
    have hs_in_block : s ∈ G.blockOf v_m := by rw [← hU_eq_blockOf]; exact hs_U
    -- The intersection t.S ∩ G.blockOf v_m = {s} (used in multiple places)
    have h_S_inter_block : t.S ∩ G.blockOf v_m = {s} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · intro ⟨hz_S, hz_block⟩
        by_contra hne
        have h_two : 2 ≤ (t.S ∩ G.blockOf v_m).ncard := by
          have h_pair : ({z, s} : Set V) ⊆ t.S ∩ G.blockOf v_m := by
            intro w hw
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
            rcases hw with rfl | rfl
            · exact ⟨hz_S, hz_block⟩
            · exact ⟨hs_S, hs_in_block⟩
          exact (Set.ncard_pair hne).symm.trans_le
            (Set.ncard_le_ncard h_pair (Set.toFinite _))
        have h_one := t.isPartialIT.2 (G.blockOf v_m) (G.blockOf_mem v_m)
        omega
      · intro hz_eq; subst hz_eq; exact ⟨hs_S, hs_in_block⟩
    have h_uncov_eq : G.uncoveredBlocks S' = G.uncoveredBlocks t.S := by
      ext W
      simp only [uncoveredBlocks, blocksIntersecting, Set.mem_diff, Set.mem_setOf_eq]
      constructor
      · intro ⟨hW_block, hW_not_int⟩
        refine ⟨hW_block, ?_⟩
        intro hW_hyp
        -- hW_hyp : W ∈ G.blocks ∧ (W ∩ t.S).Nonempty
        obtain ⟨_, hW_int⟩ := hW_hyp
        obtain ⟨y, hy_W, hy_S⟩ := hW_int
        -- W ∩ S.Nonempty implies W ∩ S'.Nonempty
        apply hW_not_int
        refine ⟨hW_block, ?_⟩
        -- Either y ∈ S' directly, or y = s (unique element in blockOf v_m ∩ S) and we use v_m
        by_cases hy_in_block : y ∈ G.blockOf v_m
        · -- y ∈ S ∩ blockOf v_m, so y = s (unique). W contains s, so W = blockOf v_m.
          have hy_eq_s : y = s := by
            have hy_in_inter : y ∈ t.S ∩ G.blockOf v_m := ⟨hy_S, hy_in_block⟩
            rw [h_S_inter_block] at hy_in_inter
            exact Set.mem_singleton_iff.mp hy_in_inter
          -- y = s, so W contains s. Since s ∈ blockOf v_m and blocks are disjoint, W = blockOf v_m.
          have hW_eq_block : W = G.blockOf v_m := by
            have h := G.blockOf_unique s W hW_block (hy_eq_s ▸ hy_W)
            have h' := G.blockOf_unique s (G.blockOf v_m) (G.blockOf_mem v_m) hs_in_block
            rw [h, h']
          -- v_m ∈ W ∩ S'
          refine ⟨v_m, ?_, ?_⟩
          · rw [hW_eq_block]; exact G.mem_blockOf v_m
          · simp only [S', oplus, Set.mem_union, Set.mem_singleton_iff]; right; trivial
        · -- y ∉ blockOf v_m, so y ∈ S \ blockOf v_m ⊆ S'
          refine ⟨y, hy_W, ?_⟩
          simp only [S', oplus, Set.mem_union, Set.mem_diff]
          left; exact ⟨hy_S, hy_in_block⟩
      · intro ⟨hW_block, hW_not_int⟩
        refine ⟨hW_block, ?_⟩
        intro hW_hyp
        -- hW_hyp : W ∈ G.blocks ∧ (W ∩ S').Nonempty
        obtain ⟨_, hW_int⟩ := hW_hyp
        obtain ⟨y, hy_W, hy_S'⟩ := hW_int
        -- W ∩ S'.Nonempty implies W ∩ S.Nonempty
        apply hW_not_int
        refine ⟨hW_block, ?_⟩
        simp only [S', oplus, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff] at hy_S'
        rcases hy_S' with ⟨hy_S, _⟩ | hy_eq
        · exact ⟨y, hy_W, hy_S⟩
        · -- y = v_m ∈ W. Since v_m ∈ blockOf v_m and blocks are disjoint, W = blockOf v_m.
          subst hy_eq
          have hW_eq_block : W = G.blockOf v_m :=
            G.blockOf_unique v_m W hW_block hy_W
          refine ⟨s, ?_, hs_S⟩
          rw [hW_eq_block]; exact hs_in_block
    -- Helper 2: For j < m, seq[j] ≁ v_m (from augmenting disjointness: v_m ⊥ C_m)
    have h_vm_not_adj : ∀ j (hj : j < m), ¬G.graph.Adj t.seq[j] v_m := by
      intro j hj hadj
      -- seq[j] ∈ vertexSeq (j+1) ⊆ vertexSeq m
      have hj_lt_len : j < t.seq.length := Nat.lt_of_lt_of_le hj (Nat.le_of_lt hm)
      have h_seq_j_in_vtx : t.seq[j] ∈ G.vertexSeq t.S t.C t.seq (j + 1) := by
        simp only [vertexSeq]
        have hseq_j : t.seq[j]? = some t.seq[j] := List.getElem?_eq_getElem hj_lt_len
        simp only [hseq_j]
        right; rfl
      have h_mono := G.vertexSeq_mono t.S t.C t.seq (Nat.succ_le_of_lt hj) (Nat.le_of_lt hm)
      have h_seq_j_in_Cm : t.seq[j] ∈ G.vertexSeq t.S t.C t.seq m := h_mono h_seq_j_in_vtx
      -- v_m is disjoint from C_m (from augmenting property)
      have h_vm_disj := h_aug.2.1
      -- hadj : G.graph.Adj t.seq[j] v_m, need to show contradiction
      -- neighborSet v_m = {w | Adj v_m w}, so Adj t.seq[j] v_m means t.seq[j] ∈ neighborSet v_m
      have h_seq_j_in_N : t.seq[j] ∈ G.graph.neighborSet v_m := G.graph.adj_symm hadj
      exact Set.disjoint_left.mp h_vm_disj h_seq_j_in_N h_seq_j_in_Cm
    -- Helper 3: For j < k, s ∉ neighborSet seq[j] (from augmenting_neighborSets_disjoint)
    have h_s_not_in_Nj : ∀ j (hj : j < k), s ∉ G.graph.neighborSet t.seq[j] := by
      intro j hj hs_Nj
      -- s ∈ N(seq[k]) ∩ S and s ∈ N(seq[j]) ∩ S for j < k
      -- This contradicts augmenting_neighborSets_disjoint
      have h_disj := G.augmenting_neighborSets_disjoint t.S t.C t.seq t.isAugmenting hj hk_len
      have hs_in_Nk : s ∈ G.graph.neighborSet t.seq[k] ∩ t.S := ⟨hs_Nk, hs_S⟩
      have hs_in_Nj : s ∈ G.graph.neighborSet t.seq[j] ∩ t.S := ⟨hs_Nj, hs_S⟩
      have hs_in_both : s ∈ (G.graph.neighborSet t.seq[k] ∩ t.S) ∩
          (G.graph.neighborSet t.seq[j] ∩ t.S) := ⟨hs_in_Nk, hs_in_Nj⟩
      rw [Set.disjoint_iff_inter_eq_empty] at h_disj
      rw [h_disj] at hs_in_both
      exact Set.notMem_empty s hs_in_both
    -- Helper 4: For j < k, N_{S'}(seq[j]) = N_S(seq[j])
    have h_NS_eq : ∀ j (hj : j < k), G.graph.neighborSet t.seq[j] ∩ S' =
        G.graph.neighborSet t.seq[j] ∩ t.S := by
      intro j hj
      ext x
      simp only [S', oplus, Set.mem_inter_iff, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · intro ⟨hx_Nj, hx_S'⟩
        rcases hx_S' with ⟨hx_S, _⟩ | hx_eq
        · exact ⟨hx_Nj, hx_S⟩
        · -- x = v_m ∈ neighborSet seq[j], so seq[j] ~ v_m
          subst hx_eq
          exfalso
          have hj_lt_m : j < m := Nat.lt_trans hj hk_lt_m
          -- hx_Nj : v_m ∈ G.graph.neighborSet t.seq[j], i.e., Adj t.seq[j] v_m
          exact h_vm_not_adj j hj_lt_m hx_Nj
      · intro ⟨hx_Nj, hx_S⟩
        constructor
        · exact hx_Nj
        · -- Need x ∈ S' = (S \ U) ∪ {v_m}
          by_cases hx_vm : x = v_m
          · right; exact hx_vm
          · left
            constructor
            · exact hx_S
            · -- x ∈ S, need x ∉ U = blockOf v_m
              -- If x ∈ U, then x ∈ S ∩ U = {s}, so x = s
              -- But s ∉ neighborSet seq[j] for j < k
              intro hx_U
              have hs_in_block : s ∈ G.blockOf v_m := by rw [← hU_eq_blockOf]; exact hs_U
              have hx_eq_s : x = s := by
                have h_inter : t.S ∩ G.blockOf v_m = {s} := by
                  ext y
                  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
                  constructor
                  · intro ⟨hy_S, hy_U⟩
                    by_contra hne
                    have h_two : 2 ≤ (t.S ∩ G.blockOf v_m).ncard := by
                      have h_pair : ({y, s} : Set V) ⊆ t.S ∩ G.blockOf v_m := by
                        intro z hz
                        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
                        rcases hz with rfl | rfl
                        · exact ⟨hy_S, hy_U⟩
                        · exact ⟨hs_S, hs_in_block⟩
                      exact (Set.ncard_pair hne).symm.trans_le
                        (Set.ncard_le_ncard h_pair (Set.toFinite _))
                    have h_one := t.isPartialIT.2 (G.blockOf v_m) (G.blockOf_mem v_m)
                    omega
                  · intro hy_eq; subst hy_eq; exact ⟨hs_S, hs_in_block⟩
                have hx_in_inter : x ∈ t.S ∩ G.blockOf v_m := ⟨hx_S, hx_U⟩
                rw [h_inter] at hx_in_inter
                exact Set.mem_singleton_iff.mp hx_in_inter
              subst hx_eq_s
              exact h_s_not_in_Nj j hj hx_Nj
    -- Helper 5: blocksSeq S' seq' i = blocksSeq t.S t.seq i for i ≤ k
    have h_blocksSeq_eq : ∀ i (hi : i ≤ k), G.blocksSeq S' seq' i = G.blocksSeq t.S t.seq i := by
      intro i hi
      induction i with
      | zero => simp only [blocksSeq]; exact h_uncov_eq
      | succ i' ih =>
        have hi' : i' ≤ k := Nat.le_of_succ_le hi
        have hi'_lt_k : i' < k := Nat.lt_of_succ_le hi
        have hi'_lt_k1 : i' < k + 1 := Nat.lt_succ_of_lt hi'_lt_k
        have hi'_lt_len : i' < t.seq.length := Nat.lt_trans hi'_lt_k hk_len
        have hi'_lt_seq'_len : i' < seq'.length := by rw [h_seq'_len]; exact hi'_lt_k1
        simp only [blocksSeq]
        -- seq'[i']? = some seq'[i'] = some t.seq[i']
        have h_seq'_i' : seq'[i']? = some t.seq[i'] := by
          have h1 : seq'[i']? = some seq'[i'] := List.getElem?_eq_getElem hi'_lt_seq'_len
          have h2 : seq'[i'] = t.seq[i'] := by
            simp only [seq']
            rw [List.getElem_take]
          rw [h1, h2]
        have h_seq_i' : t.seq[i']? = some t.seq[i'] := List.getElem?_eq_getElem hi'_lt_len
        simp only [h_seq'_i', h_seq_i']
        rw [ih hi']
        -- Need: blocksIntersecting (N_{S'}(seq[i'])) = blocksIntersecting (N_S(seq[i']))
        congr 1
        exact congr_arg G.blocksIntersecting (h_NS_eq i' hi'_lt_k)
    -- Show seq' is augmenting for (S', ∅)
    have h_aug' : G.IsAugmenting S' ∅ seq' := by
      intro ⟨i, hi⟩
      have hi_lt_k1 : i < k + 1 := by rw [← h_seq'_len]; exact hi
      have hi_lt_len : i < t.seq.length := by
        have h_k1_le : k + 1 ≤ t.seq.length := by
          have : k + 1 ≤ m + 1 := Nat.add_le_add_right (Nat.le_of_lt hk_lt_m) 1
          omega
        omega
      -- seq'[i] = t.seq[i] for i < k + 1
      have h_seq'_i : seq'[i]'hi = t.seq[i]'hi_lt_len := by
        simp only [seq']
        rw [List.getElem_take]
      -- Get the augmenting property from the original tuple
      have h_aug_i := t.isAugmenting ⟨i, hi_lt_len⟩
      have hi_le_k : i ≤ k := Nat.lt_succ_iff.mp hi_lt_k1
      -- The goal involves seq'[⟨i, hi⟩]. We need to convert to t.seq[i] using h_seq'_i.
      constructor
      · -- Condition 1: seq'[i] ∈ V_{blocksSeq S' seq' i}
        change seq'.get ⟨i, hi⟩ ∈ G.blockUnion (G.blocksSeq S' seq' i)
        simp only [List.get_eq_getElem]
        rw [h_seq'_i, h_blocksSeq_eq i hi_le_k]
        exact h_aug_i.1
      constructor
      · -- Condition 2: Disjoint (neighborSet seq'[i]) (vertexSeq S' ∅ seq' i)
        change Disjoint (G.graph.neighborSet (seq'.get ⟨i, hi⟩)) (G.vertexSeq S' ∅ seq' i)
        simp only [List.get_eq_getElem]
        rw [h_seq'_i]
        -- Show vertexSeq S' ∅ seq' i ⊆ vertexSeq t.S t.C t.seq i
        have h_vtx_sub : G.vertexSeq S' ∅ seq' i ⊆ G.vertexSeq t.S t.C t.seq i := by
          induction i with
          | zero =>
            simp only [vertexSeq]
            exact Set.empty_subset _
          | succ i' ih_vtx =>
            have hi'_le_k : i' ≤ k := Nat.le_of_succ_le hi_le_k
            have hi'_lt_k : i' < k := Nat.lt_of_succ_le hi_le_k
            have hi'_lt_k1 : i' < k + 1 := Nat.lt_succ_of_lt hi'_lt_k
            have hi'_lt_seq'_len : i' < seq'.length := by rw [h_seq'_len]; exact hi'_lt_k1
            have hi'_lt_len' : i' < t.seq.length := Nat.lt_trans hi'_lt_k hk_len
            simp only [vertexSeq]
            have h_seq'_i'_some : seq'[i']? = some seq'[i'] :=
              List.getElem?_eq_getElem hi'_lt_seq'_len
            have h_seq_i'_some : t.seq[i']? = some t.seq[i'] :=
              List.getElem?_eq_getElem hi'_lt_len'
            simp only [h_seq'_i'_some, h_seq_i'_some]
            have h_seq'_i'_eq : seq'[i'] = t.seq[i'] := by
              simp only [seq']; rw [List.getElem_take]
            rw [h_seq'_i'_eq]
            intro x hx
            simp only [Set.mem_union, Set.mem_singleton_iff] at hx ⊢
            rcases hx with ((hx_vtx | hx_NS) | hx_eq)
            · left; left
              -- Need to provide all generalized arguments to ih_vtx
              have h_seq'_i' : seq'[i'] = t.seq[i'] := by simp only [seq']; rw [List.getElem_take]
              have h_aug_i' := t.isAugmenting ⟨i', hi'_lt_len'⟩
              exact ih_vtx hi'_lt_seq'_len hi'_lt_k1 hi'_lt_len' h_seq'_i' h_aug_i' hi'_le_k hx_vtx
            · left; right
              rw [h_NS_eq i' hi'_lt_k] at hx_NS
              exact hx_NS
            · right; exact hx_eq
        exact Set.disjoint_of_subset_right h_vtx_sub h_aug_i.2.1
      -- Condition 3: positive degree for non-last position
      intro h_not_last
      change 0 < (G.graph.neighborSet (seq'.get ⟨i, hi⟩) ∩ S').ncard
      simp only [List.get_eq_getElem]
      rw [h_seq'_i]
      have hi_lt_k : i < k := by
        simp only [] at h_not_last
        omega
      have h_deg_eq : (G.graph.neighborSet t.seq[i] ∩ S').ncard =
          (G.graph.neighborSet t.seq[i] ∩ t.S).ncard := by
        congr 1; exact h_NS_eq i hi_lt_k
      rw [h_deg_eq]
      have hi_not_last_orig : i + 1 < t.seq.length := by
        have : i + 1 ≤ k := hi_lt_k
        have : k < m := hk_lt_m
        have : m < t.seq.length := hm
        omega
      exact h_aug_i.2.2 hi_not_last_orig
    -- Construct the new feasible tuple
    let t' : G.FeasibleTuple := ⟨S', ∅, seq', hS'_partial, Set.empty_subset _, h_aug'⟩
    use t'
    refine ⟨rfl, ?_, ?_, ?_⟩
    · -- t'.S ⊆ t.S ∪ {v_m}: every element is in t.S or is a seq element
      intro x hx
      have hx : x ∈ S' := hx
      simp only [S', oplus, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff] at hx
      rcases hx with ⟨hxS, _⟩ | hx_eq
      · left; exact hxS
      · right; exact ⟨m, hm, hx_eq⟩
    · -- t'.seq elements come from t.seq (t'.seq is a prefix of t.seq)
      intro x hx
      exact List.mem_of_mem_take hx
    · -- Show FeasibleTupleLt t' t
      -- |S'| = |S| (we swapped one vertex for another)
      -- The degree sequence is smaller: d_i(seq') = d_i(seq) for i < k,
      -- and d_k(seq') = d_k(seq) - 1 (s was removed from N_S(v_k))
      right
      constructor
      · -- |S'| = |S|
        -- oplus replaces one vertex with another in the same block
        -- S' = (S \ blockOf v_m) ∪ {v_m}
        -- Since s ∈ S ∩ U and U = blockOf v_m, we have s ∈ S ∩ blockOf v_m
        -- The partial IT property ensures |S ∩ U| ≤ 1, so S ∩ U = {s}
        -- Therefore S' = (S \ {s}) ∪ {v_m} has the same cardinality
        have hs_in_block : s ∈ G.blockOf v_m := by rw [← hU_eq_blockOf]; exact hs_U
        have h_S_inter_block : t.S ∩ G.blockOf v_m = {s} := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
          constructor
          · intro ⟨hxS, hxU⟩
            -- x, s ∈ S ∩ blockOf v_m, and |S ∩ blockOf v_m| ≤ 1
            by_contra hne
            have h_pair : ({x, s} : Set V) ⊆ t.S ∩ G.blockOf v_m := by
              intro y hy
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
              rcases hy with rfl | rfl
              · exact ⟨hxS, hxU⟩
              · exact ⟨hs_S, hs_in_block⟩
            have h_two : 2 ≤ (t.S ∩ G.blockOf v_m).ncard :=
              (Set.ncard_pair hne).symm.trans_le (Set.ncard_le_ncard h_pair (Set.toFinite _))
            have h_one := t.isPartialIT.2 (G.blockOf v_m) (G.blockOf_mem v_m)
            omega
          · intro hx_eq
            subst hx_eq
            exact ⟨hs_S, hs_in_block⟩
        -- S' = (S \ blockOf v_m) ∪ {v_m}, where S ∩ blockOf v_m = {s}
        -- So |S'| = |S \ blockOf v_m| + 1 = |S| - |S ∩ blockOf v_m| + 1 = |S| - 1 + 1 = |S|
        have h_diff_card : (t.S \ G.blockOf v_m).ncard = t.S.ncard - 1 := by
          -- Use: (s ∩ t).ncard + (s \ t).ncard = s.ncard
          have h_add := Set.ncard_inter_add_ncard_diff_eq_ncard t.S (G.blockOf v_m) (Set.toFinite _)
          rw [h_S_inter_block, Set.ncard_singleton] at h_add
          omega
        have h_disj : Disjoint (t.S \ G.blockOf v_m) {v_m} := by
          rw [Set.disjoint_singleton_right]
          intro hv_in
          exact hv_in.2 (G.mem_blockOf v_m)
        calc S'.ncard = (G.oplus t.S v_m).ncard := rfl
          _ = ((t.S \ G.blockOf v_m) ∪ {v_m}).ncard := rfl
          _ = (t.S \ G.blockOf v_m).ncard + ({v_m} : Set V).ncard := by
              exact Set.ncard_union_eq h_disj (Set.toFinite _) (Set.toFinite _)
          _ = (t.S \ G.blockOf v_m).ncard + 1 := by simp only [Set.ncard_singleton]
          _ = (t.S.ncard - 1) + 1 := by rw [h_diff_card]
          _ = t.S.ncard := by
              have h_S_nonempty : t.S.Nonempty := ⟨s, hs_S⟩
              have h_ncard_pos : 0 < t.S.ncard := (Set.ncard_pos (Set.toFinite _)).mpr h_S_nonempty
              omega
      · -- degSeqLt (degreeSeq S' seq') (degreeSeq S seq)
        -- This requires showing that d_k(seq') = d_k(seq) - 1
        -- The key insight: N_{S'}(t.seq[k]) = N_S(t.seq[k]) \ {s}
        -- because s was the unique S-neighbor of t.seq[k] in block U,
        -- and S' = S \ U ∪ {v_m} with v_m ≁ t.seq[k] (from augmenting disjointness)
        simp only [degSeqLt]
        -- Use Case 2: List.Lex (· < ·) d1 d2 ∧ ¬(d1 <+: d2)
        right
        -- First establish key facts about the degree sequences
        let d1 := G.degreeSeq S' seq'
        let d2 := G.degreeSeq t.S t.seq
        have h_d1_len : d1.length = k + 1 := by
          simp only [d1, degreeSeq, List.length_mapIdx, h_seq'_len]
        have h_d2_len : d2.length = t.seq.length := by
          simp only [d2, degreeSeq, List.length_mapIdx]
        -- Key fact: N_{S'}(seq[k]) = N_S(seq[k]) \ {s}
        have h_NS_k : G.graph.neighborSet t.seq[k] ∩ S' =
            (G.graph.neighborSet t.seq[k] ∩ t.S) \ {s} := by
          ext x
          simp only [S', oplus, Set.mem_inter_iff, Set.mem_union, Set.mem_diff,
            Set.mem_singleton_iff]
          constructor
          · intro ⟨hx_Nk, hx_S'⟩
            rcases hx_S' with ⟨hx_S, hx_not_block⟩ | hx_vm
            · refine ⟨⟨hx_Nk, hx_S⟩, ?_⟩
              intro hx_eq
              subst hx_eq
              exact hx_not_block hs_in_block
            · -- x = v_m, but v_m ∉ N(seq[k]) by augmenting disjointness
              subst hx_vm
              exfalso
              exact h_vm_not_adj k hk_lt_m hx_Nk
          · intro ⟨⟨hx_Nk, hx_S⟩, hx_ne_s⟩
            refine ⟨hx_Nk, ?_⟩
            left
            constructor
            · exact hx_S
            · intro hx_block
              have hx_in_inter : x ∈ t.S ∩ G.blockOf v_m := ⟨hx_S, hx_block⟩
              rw [h_S_inter_block] at hx_in_inter
              exact hx_ne_s (Set.mem_singleton_iff.mp hx_in_inter)
        -- Therefore d1[k] < d2[k]
        have hs_in_NS_k : s ∈ G.graph.neighborSet t.seq[k] ∩ t.S := ⟨hs_Nk, hs_S⟩
        have h_finite_k : (G.graph.neighborSet t.seq[k] ∩ t.S).Finite := Set.toFinite _
        have h_dk_lt : (G.graph.neighborSet t.seq[k] ∩ S').ncard <
            (G.graph.neighborSet t.seq[k] ∩ t.S).ncard := by
          rw [h_NS_k]
          calc ((G.graph.neighborSet t.seq[k] ∩ t.S) \ {s}).ncard
            = (G.graph.neighborSet t.seq[k] ∩ t.S).ncard - 1 := by
                exact Set.ncard_diff_singleton_of_mem hs_in_NS_k
            _ < (G.graph.neighborSet t.seq[k] ∩ t.S).ncard := by
                have h_pos : 0 < (G.graph.neighborSet t.seq[k] ∩ t.S).ncard := by
                  rw [Set.ncard_pos h_finite_k]
                  exact ⟨s, hs_in_NS_k⟩
                omega
        -- For i < k: d1[i] = d2[i] (degrees agree)
        have h_deg_eq : ∀ i (hi : i < k), (G.graph.neighborSet t.seq[i] ∩ S').ncard =
            (G.graph.neighborSet t.seq[i] ∩ t.S).ncard := by
          intro i hi
          congr 1
          exact h_NS_eq i hi
        -- seq'[i] = seq[i] for i < k + 1
        have h_seq'_eq : ∀ i (hi : i < k + 1), seq'[i]'(by rw [h_seq'_len]; exact hi) =
            t.seq[i]'(Nat.lt_of_lt_of_le hi (by omega : k + 1 ≤ t.seq.length)) := by
          intro i hi
          simp only [seq', List.getElem_take]
        -- Need to show: List.Lex (·<·) d1 d2 ∧ ¬(d1 <+: d2)
        -- Length facts
        have hk_lt_d1 : k < d1.length := by simp only [h_d1_len]; exact Nat.lt_succ_self k
        have hk_lt_d2 : k < d2.length := by simp only [h_d2_len]; exact hk_len
        -- d1[i] = d2[i] for i < k
        have h_d_eq : ∀ i (hi : i < k),
            d1[i]'(Nat.lt_of_lt_of_le hi (Nat.le_of_lt hk_lt_d1)) =
            d2[i]'(Nat.lt_of_lt_of_le hi (Nat.le_of_lt hk_lt_d2)) := by
          intro i hi
          simp only [d1, d2, degreeSeq, List.getElem_mapIdx]
          have hi_lt_k1 : i < k + 1 := Nat.lt_of_lt_of_le hi (Nat.le_of_lt (Nat.lt_succ_self k))
          have h_seq'_i := h_seq'_eq i hi_lt_k1
          conv_lhs => rw [h_seq'_i]
          exact h_deg_eq i hi
        -- d1[k] < d2[k]
        have h_d_k_lt : d1[k]'hk_lt_d1 < d2[k]'hk_lt_d2 := by
          simp only [d1, d2, degreeSeq, List.getElem_mapIdx]
          have h_seq'_k := h_seq'_eq k (Nat.lt_succ_self k)
          conv_lhs => rw [h_seq'_k]
          exact h_dk_lt
        constructor
        · -- List.Lex (·<·) d1 d2
          exact list_lex_of_prefix_and_lt hk_lt_d1 hk_lt_d2 h_d_eq h_d_k_lt
        · -- ¬(d1 <+: d2)
          exact not_prefix_of_ne_at hk_lt_d1 hk_lt_d2 (Nat.ne_of_lt h_d_k_lt)

/-- Variant of `improve_from_zero_degree` for the precolor setting.
    Here Z is a set tracked by C (C = Z ∩ V_uncovered(S)), and X is a set to avoid.
    The key property is that added vertices avoid X, and C updates correctly with Z. -/
lemma PartitionedGraph.improve_from_zero_degree_precolor (t : G.FeasibleTuple)
    (Z : Set V) -- Set tracked by C (typically the original IT S)
    (X : Set V) -- The constraint set to avoid
    (h_C_eq : t.C = Z ∩ G.blockUnion (G.uncoveredBlocks t.S))
    (h_nonempty : t.seq ≠ [])
    (h_last_zero : G.degreeAt t.S t.seq t.seq.length = 0)
    (h_seq_avoid_X : ∀ i (hi : i < t.seq.length), t.seq[i] ∉ X)
    (_hX_bound : X.ncard < G.maxDegree) :
    ∃ (t' : G.FeasibleTuple) (v : V),
      t'.C = Z ∩ G.blockUnion (G.uncoveredBlocks t'.S) ∧
      (∀ i (hi : i < t'.seq.length), t'.seq[i] ∉ X) ∧
      G.FeasibleTupleLt t' t ∧
      v ∉ X ∧
      (∀ s ∈ t.S, ¬G.graph.Adj v s) ∧
      (∀ c ∈ t.C, ¬G.graph.Adj v c) ∧
      (t'.S = t.S ∪ {v} ∨ t'.S = G.oplus t.S v) := by
  -- Setup: same as improve_from_zero_degree
  have h_len_pos : 0 < t.seq.length := List.length_pos_of_ne_nil h_nonempty
  let m := t.seq.length - 1
  have hm : m < t.seq.length := Nat.sub_one_lt_of_lt h_len_pos
  have hm_eq : m + 1 = t.seq.length := Nat.sub_add_cancel h_len_pos
  let v_m := t.seq[m]
  -- d_m = 0 means v_m has no neighbors in S
  have h_no_neighbors : G.graph.neighborSet v_m ∩ t.S = ∅ := by
    rw [← Set.ncard_eq_zero]
    simp only [degreeAt] at h_last_zero
    have hseq : t.seq.length - 1 < t.seq.length := by omega
    simp only [List.getElem?_eq_getElem hseq] at h_last_zero
    exact h_last_zero
  have h_indep : ∀ s ∈ t.S, ¬G.graph.Adj v_m s := by
    intro s hs hadj
    have : s ∈ G.graph.neighborSet v_m ∩ t.S := ⟨hadj, hs⟩
    rw [h_no_neighbors] at this
    exact this
  -- v_m ∉ X (from h_seq_avoid_X)
  have h_vm_not_X : v_m ∉ X := h_seq_avoid_X m hm
  -- From augmenting property: v_m ∈ V_{B_m}
  have h_aug := t.isAugmenting ⟨m, hm⟩
  have h_vm_in_Bm : v_m ∈ G.blockUnion (G.blocksSeq t.S t.seq m) := h_aug.1
  -- v_m is in some block U ∈ B_m
  have ⟨U, hU_in_Bm, hv_in_U⟩ : ∃ U ∈ G.blocksSeq t.S t.seq m, v_m ∈ U := by
    have hBm_sub : G.blocksSeq t.S t.seq m ⊆ G.blocks := G.blocksSeq_subset t.S t.seq m
    rw [G.blockUnion_eq_sUnion hBm_sub] at h_vm_in_Bm
    exact Set.mem_sUnion.mp h_vm_in_Bm
  have hU_blocks : U ∈ G.blocks := G.blocksSeq_subset t.S t.seq m hU_in_Bm
  -- v_m has no neighbor in t.C
  -- (from augmenting: C ⊆ vertexSeq 0 ⊆ vertexSeq m, disjoint from N(v_m))
  have h_vm_indep_C : ∀ c ∈ t.C, ¬G.graph.Adj v_m c := by
    intro c hc hadj
    have h_c_vtx0 : c ∈ G.vertexSeq t.S t.C t.seq 0 := by simp only [vertexSeq]; exact hc
    have h_c_vtxm := G.vertexSeq_mono t.S t.C t.seq (Nat.zero_le m) (Nat.le_of_lt hm) h_c_vtx0
    exact absurd h_c_vtxm (Set.disjoint_left.mp h_aug.2.1 hadj)
  -- The rest follows improve_from_zero_degree with C' = X ∩ V_uncovered(S')
  -- Case analysis on whether U is uncovered or was added at step k
  rcases G.blocksSeq_mem_cases t.S t.seq U m (le_of_lt hm) hU_in_Bm with
    hU_uncov | ⟨k, hk_len, hk_lt_m, hU_from_k⟩
  · -- Case 1: U ∈ uncoveredBlocks S (k = 0 case)
    -- S ∩ U = ∅ (U is uncovered)
    have hS_disjoint_U : Disjoint t.S U := by
      simp only [uncoveredBlocks, blocksIntersecting] at hU_uncov
      simp only [Set.mem_diff, Set.mem_setOf_eq, not_and] at hU_uncov
      have := hU_uncov.2 hU_blocks
      rw [Set.not_nonempty_iff_eq_empty, Set.inter_comm] at this
      exact Set.disjoint_iff_inter_eq_empty.mpr this
    -- S' = S ∪ {v_m} is independent (v_m has no S-neighbors)
    let S' := t.S ∪ {v_m}
    have hS'_indep : G.graph.IsIndepSet S' := by
      intro x hx y hy hne
      simp only [S', Set.mem_union, Set.mem_singleton_iff] at hx hy
      rcases hx, hy with ⟨hxS | hx_eq, hyS | hy_eq⟩
      · exact t.isPartialIT.1 hxS hyS hne
      · subst hy_eq; exact fun hadj => h_indep x hxS (G.graph.adj_symm hadj)
      · subst hx_eq; exact h_indep y hyS
      · subst hx_eq hy_eq; exact (hne rfl).elim
    have hS'_partial : G.IsPartialIT S' := by
      constructor
      · exact hS'_indep
      · intro U' hU'
        by_cases hU'_eq : U' = U
        · rw [hU'_eq]
          have h_inter : S' ∩ U = {v_m} := by
            ext x
            simp only [S', Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
            constructor
            · intro ⟨hx_S', hx_U⟩
              rcases hx_S' with hxS | hx_eq
              · exact (Set.disjoint_left.mp hS_disjoint_U hxS hx_U).elim
              · exact hx_eq
            · intro hx_eq; subst hx_eq; exact ⟨Or.inr rfl, hv_in_U⟩
          rw [h_inter, Set.ncard_singleton]
        · have hv_not_in_U' : v_m ∉ U' := by
            intro hv_U'
            have hdisj := G.pairwiseDisjoint hU_blocks hU' (Ne.symm hU'_eq)
            exact Set.disjoint_left.mp hdisj hv_in_U hv_U'
          have h_inter : S' ∩ U' = t.S ∩ U' := by
            ext x
            simp only [S', Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
            constructor
            · intro ⟨hx_S', hx_U'⟩
              rcases hx_S' with hxS | hx_eq
              · exact ⟨hxS, hx_U'⟩
              · subst hx_eq; exact (hv_not_in_U' hx_U').elim
            · intro ⟨hxS, hx_U'⟩; exact ⟨Or.inl hxS, hx_U'⟩
          rw [h_inter]
          exact t.isPartialIT.2 U' hU'
    -- C' = Z ∩ V_uncovered(S')
    let C' := Z ∩ G.blockUnion (G.uncoveredBlocks S')
    -- V_uncovered(S') = V_uncovered(S) \ {U} since U is now covered
    have h_uncov_eq : G.uncoveredBlocks S' = G.uncoveredBlocks t.S \ {U} := by
      ext W
      constructor
      · intro hW_uncov_S'
        simp only [uncoveredBlocks, blocksIntersecting, Set.mem_diff, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at hW_uncov_S' ⊢
        obtain ⟨hW_block, hW_not_int⟩ := hW_uncov_S'
        constructor
        · constructor
          · exact hW_block
          · intro ⟨_, hW_int⟩
            obtain ⟨y, hy_W, hy_S⟩ := hW_int
            apply hW_not_int
            exact ⟨hW_block, y, hy_W, Or.inl hy_S⟩
        · intro hW_eq
          apply hW_not_int
          exact ⟨hW_eq ▸ hU_blocks, v_m, hW_eq ▸ hv_in_U, Or.inr rfl⟩
      · intro hW_mem
        simp only [uncoveredBlocks, blocksIntersecting, Set.mem_diff, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at hW_mem ⊢
        obtain ⟨⟨hW_block, hW_uncov⟩, hW_ne_U⟩ := hW_mem
        refine ⟨hW_block, ?_⟩
        intro ⟨_, y, hy_W, hy_S'⟩
        rcases hy_S' with hy_S | hy_eq
        · exact hW_uncov ⟨hW_block, y, hy_W, hy_S⟩
        · subst hy_eq
          have hW_eq_U : W = U := by
            have h := G.blockOf_unique v_m W hW_block hy_W
            have h' := G.blockOf_unique v_m U hU_blocks hv_in_U
            rw [h, h']
          exact hW_ne_U hW_eq_U
    -- C' ⊆ V_uncovered(S')
    have hC'_subset : C' ⊆ G.blockUnion (G.uncoveredBlocks S') := Set.inter_subset_right
    -- Construct the new feasible tuple
    let t' : G.FeasibleTuple := ⟨S', C', [], hS'_partial, hC'_subset, fun k => Fin.elim0 k⟩
    refine ⟨t', v_m, rfl, fun i hi => (Nat.not_lt_zero i hi).elim, ?_,
            h_vm_not_X, h_indep, h_vm_indep_C, Or.inl rfl⟩
    -- FeasibleTupleLt: |S'| > |S|
    left
    have hv_not_in_S : v_m ∉ t.S := Set.disjoint_left.mp hS_disjoint_U.symm hv_in_U
    calc S'.ncard = (t.S ∪ {v_m}).ncard := rfl
      _ = t.S.ncard + ({v_m} : Set V).ncard :=
          Set.ncard_union_eq (Set.disjoint_singleton_right.mpr hv_not_in_S)
      _ = t.S.ncard + 1 := by simp only [Set.ncard_singleton]
      _ > t.S.ncard := by omega
  · -- Case 2: U was added at step k (covered block case)
    -- This follows improve_from_zero_degree with the key observation:
    -- Since U is already covered by S (it was added at step k), we have:
    -- 1. V_uncovered(S') = V_uncovered(S) (swapping doesn't change covered/uncovered)
    -- 2. Therefore C' = X ∩ V_uncovered(S') = X ∩ V_uncovered(S) = C
    -- 3. The truncated sequence seq' = seq.take(k+1) still avoids X
    --    (it's a prefix of seq which avoids X by h_seq_avoid_X)
    -- The tuple ordering decreases via the degree sequence comparison
    simp only [blocksIntersecting, Set.mem_setOf_eq] at hU_from_k
    obtain ⟨_, s, hs_U, hs_NS⟩ := hU_from_k
    have hs_S : s ∈ t.S := hs_NS.2
    have hs_Nk : G.graph.Adj t.seq[k] s := hs_NS.1
    have _h_vm_not_adj_s : ¬G.graph.Adj v_m s := h_indep s hs_S
    have hU_eq_blockOf : U = G.blockOf v_m := G.blockOf_unique v_m U hU_blocks hv_in_U
    let S' := G.oplus t.S v_m
    -- S' is independent: v_m is not adjacent to any vertex in S
    have hS'_indep : G.graph.IsIndepSet S' := by
      intro x hx y hy hne
      simp only [S', oplus, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff] at hx hy
      rcases hx, hy with ⟨⟨hxS, hxU⟩ | hx_eq, ⟨hyS, hyU⟩ | hy_eq⟩
      · exact t.isPartialIT.1 hxS hyS hne
      · subst hy_eq; intro hadj; exact h_indep x hxS (G.graph.adj_symm hadj)
      · subst hx_eq; exact h_indep y hyS
      · subst hx_eq hy_eq; exact (hne rfl).elim
    have hS'_partial : G.IsPartialIT S' := by
      constructor
      · exact hS'_indep
      · intro U' hU'
        by_cases hU'_eq : U' = G.blockOf v_m
        · rw [hU'_eq]
          have h_inter : S' ∩ G.blockOf v_m = {v_m} := by
            ext x
            simp only [S', oplus, Set.mem_inter_iff, Set.mem_union, Set.mem_diff,
              Set.mem_singleton_iff]
            constructor
            · intro ⟨hx_S', hx_U⟩
              rcases hx_S' with ⟨_, hxU⟩ | hx_eq
              · exact (hxU hx_U).elim
              · exact hx_eq
            · intro hx_eq; subst hx_eq; exact ⟨Or.inr rfl, G.mem_blockOf v_m⟩
          rw [h_inter, Set.ncard_singleton]
        · have h_inter : S' ∩ U' = t.S ∩ U' := by
            ext x
            simp only [S', oplus, Set.mem_inter_iff, Set.mem_union, Set.mem_diff,
              Set.mem_singleton_iff]
            constructor
            · intro ⟨hx_S', hx_U'⟩
              rcases hx_S' with ⟨hxS, _⟩ | hx_eq
              · exact ⟨hxS, hx_U'⟩
              · subst hx_eq
                have hdisj := G.pairwiseDisjoint (G.blockOf_mem v_m) hU' (fun h => hU'_eq h.symm)
                exact (Set.disjoint_left.mp hdisj (G.mem_blockOf v_m) hx_U').elim
            · intro ⟨hxS, hx_U'⟩
              have hx_not_in_block : x ∉ G.blockOf v_m := by
                intro hx_block
                have hdisj := G.pairwiseDisjoint (G.blockOf_mem v_m) hU' (fun h => hU'_eq h.symm)
                exact Set.disjoint_left.mp hdisj hx_block hx_U'
              exact ⟨Or.inl ⟨hxS, hx_not_in_block⟩, hx_U'⟩
          rw [h_inter]
          exact t.isPartialIT.2 U' hU'
    -- Key: V_uncovered(S') = V_uncovered(S) since U is already covered
    have h_uncov_eq : G.uncoveredBlocks S' = G.uncoveredBlocks t.S := by
      ext W
      constructor
      · intro hW_uncov_S'
        simp only [uncoveredBlocks, blocksIntersecting, Set.mem_diff,
          Set.mem_setOf_eq] at hW_uncov_S' ⊢
        obtain ⟨hW_block, hW_not_int⟩ := hW_uncov_S'
        refine ⟨hW_block, ?_⟩
        intro ⟨_, y, hy_W, hy_S⟩
        apply hW_not_int
        -- y ∈ S, need y ∈ S' = (S \ blockOf v_m) ∪ {v_m}
        by_cases hy_block : y ∈ G.blockOf v_m
        · -- y ∈ S ∩ blockOf v_m, but we can use v_m instead
          have hW_eq : W = G.blockOf v_m := by
            have h := G.blockOf_unique y W hW_block hy_W
            have h' := G.blockOf_unique y (G.blockOf v_m) (G.blockOf_mem v_m) hy_block
            rw [h, h']
          exact ⟨hW_block, v_m, hW_eq ▸ G.mem_blockOf v_m, Or.inr rfl⟩
        · exact ⟨hW_block, y, hy_W, Or.inl ⟨hy_S, hy_block⟩⟩
      · intro hW_uncov_S
        simp only [uncoveredBlocks, blocksIntersecting, Set.mem_diff,
          Set.mem_setOf_eq] at hW_uncov_S ⊢
        obtain ⟨hW_block, hW_not_int⟩ := hW_uncov_S
        refine ⟨hW_block, ?_⟩
        intro ⟨_, y, hy_W, hy_S'⟩
        apply hW_not_int
        rcases hy_S' with ⟨hy_S, _⟩ | hy_eq
        · exact ⟨hW_block, y, hy_W, hy_S⟩
        · -- y = v_m, so W = blockOf v_m (which is covered by s ∈ S)
          subst hy_eq
          have hs_in_block : s ∈ G.blockOf v_m := by rw [← hU_eq_blockOf]; exact hs_U
          have hW_eq : W = G.blockOf v_m := G.blockOf_unique v_m W hW_block hy_W
          exact ⟨hW_block, s, hW_eq ▸ hs_in_block, hs_S⟩
    -- C' = t.C
    let C' := Z ∩ G.blockUnion (G.uncoveredBlocks S')
    have hC'_eq : C' = t.C := by
      simp only [C', h_uncov_eq, h_C_eq]
    have hC'_subset : C' ⊆ G.blockUnion (G.uncoveredBlocks S') := Set.inter_subset_right
    -- The truncated sequence
    let seq' := t.seq.take (k + 1)
    have h_seq'_len : seq'.length = k + 1 := by
      simp only [seq', List.length_take]
      have h_k1_le : k + 1 ≤ t.seq.length := by
        have : k + 1 ≤ m + 1 := Nat.add_le_add_right (Nat.le_of_lt hk_lt_m) 1
        omega
      exact Nat.min_eq_left h_k1_le
    -- Sequence avoidance: seq' is a prefix of seq, so inherits avoidance
    have h_seq'_avoid_X : ∀ i (hi : i < seq'.length), seq'[i] ∉ X := by
      intro i hi
      have hi_lt_len : i < t.seq.length := by
        rw [h_seq'_len] at hi
        have h_k1_le : k + 1 ≤ t.seq.length := by
          have : k + 1 ≤ m + 1 := Nat.add_le_add_right (Nat.le_of_lt hk_lt_m) 1
          omega
        omega
      have h_seq'_i : seq'[i] = t.seq[i] := by
        simp only [seq', List.getElem_take]
      rw [h_seq'_i]
      exact h_seq_avoid_X i hi_lt_len
    -- Additional helpers (following improve_from_zero_degree Case 2)
    have hs_in_block : s ∈ G.blockOf v_m := by rw [← hU_eq_blockOf]; exact hs_U
    have h_S_inter_block : t.S ∩ G.blockOf v_m = {s} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · intro ⟨hz_S, hz_block⟩
        by_contra hne
        have h_two : 2 ≤ (t.S ∩ G.blockOf v_m).ncard := by
          have h_pair : ({z, s} : Set V) ⊆ t.S ∩ G.blockOf v_m := by
            intro w hw
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
            rcases hw with rfl | rfl
            · exact ⟨hz_S, hz_block⟩
            · exact ⟨hs_S, hs_in_block⟩
          exact (Set.ncard_pair hne).symm.trans_le
            (Set.ncard_le_ncard h_pair (Set.toFinite _))
        have h_one := t.isPartialIT.2 (G.blockOf v_m) (G.blockOf_mem v_m)
        omega
      · intro hz_eq; subst hz_eq; exact ⟨hs_S, hs_in_block⟩
    -- v_m not adjacent to seq[j] for j < m (from augmenting disjointness)
    have h_vm_not_adj : ∀ j (hj : j < m), ¬G.graph.Adj t.seq[j] v_m := by
      intro j hj hadj
      have hj_lt_len : j < t.seq.length := Nat.lt_of_lt_of_le hj (Nat.le_of_lt hm)
      have h_seq_j_in_vtx : t.seq[j] ∈ G.vertexSeq t.S t.C t.seq (j + 1) := by
        simp only [vertexSeq]
        have hseq_j : t.seq[j]? = some t.seq[j] := List.getElem?_eq_getElem hj_lt_len
        simp only [hseq_j]
        right; rfl
      have h_mono := G.vertexSeq_mono t.S t.C t.seq (Nat.succ_le_of_lt hj) (Nat.le_of_lt hm)
      have h_seq_j_in_Cm : t.seq[j] ∈ G.vertexSeq t.S t.C t.seq m := h_mono h_seq_j_in_vtx
      have h_vm_disj := h_aug.2.1
      have h_seq_j_in_N : t.seq[j] ∈ G.graph.neighborSet v_m := G.graph.adj_symm hadj
      exact Set.disjoint_left.mp h_vm_disj h_seq_j_in_N h_seq_j_in_Cm
    -- s not in neighborSet seq[j] for j < k
    have h_s_not_in_Nj : ∀ j (hj : j < k), s ∉ G.graph.neighborSet t.seq[j] := by
      intro j hj hs_Nj
      have h_disj := G.augmenting_neighborSets_disjoint t.S t.C t.seq t.isAugmenting hj hk_len
      have hs_in_Nk : s ∈ G.graph.neighborSet t.seq[k] ∩ t.S := ⟨hs_Nk, hs_S⟩
      have hs_in_Nj' : s ∈ G.graph.neighborSet t.seq[j] ∩ t.S := ⟨hs_Nj, hs_S⟩
      have hs_in_both : s ∈ (G.graph.neighborSet t.seq[k] ∩ t.S) ∩
          (G.graph.neighborSet t.seq[j] ∩ t.S) := ⟨hs_in_Nk, hs_in_Nj'⟩
      rw [Set.disjoint_iff_inter_eq_empty] at h_disj
      rw [h_disj] at hs_in_both
      exact Set.notMem_empty s hs_in_both
    -- N_{S'}(seq[j]) = N_S(seq[j]) for j < k
    have h_NS_eq : ∀ j (hj : j < k), G.graph.neighborSet t.seq[j] ∩ S' =
        G.graph.neighborSet t.seq[j] ∩ t.S := by
      intro j hj
      ext x
      simp only [S', oplus, Set.mem_inter_iff, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · intro ⟨hx_Nj, hx_S'⟩
        rcases hx_S' with ⟨hx_S, _⟩ | hx_eq
        · exact ⟨hx_Nj, hx_S⟩
        · subst hx_eq
          exfalso
          have hj_lt_m : j < m := Nat.lt_trans hj hk_lt_m
          exact h_vm_not_adj j hj_lt_m hx_Nj
      · intro ⟨hx_Nj, hx_S⟩
        constructor
        · exact hx_Nj
        · by_cases hx_vm : x = v_m
          · right; exact hx_vm
          · left
            constructor
            · exact hx_S
            · intro hx_U
              have hx_eq_s : x = s := by
                have hx_in_inter : x ∈ t.S ∩ G.blockOf v_m := ⟨hx_S, hx_U⟩
                rw [h_S_inter_block] at hx_in_inter
                exact Set.mem_singleton_iff.mp hx_in_inter
              subst hx_eq_s
              exact h_s_not_in_Nj j hj hx_Nj
    -- blocksSeq S' seq' i = blocksSeq t.S t.seq i for i ≤ k
    have h_blocksSeq_eq : ∀ i (hi : i ≤ k), G.blocksSeq S' seq' i = G.blocksSeq t.S t.seq i := by
      intro i hi
      induction i with
      | zero => simp only [blocksSeq]; exact h_uncov_eq
      | succ i' ih =>
        have hi' : i' ≤ k := Nat.le_of_succ_le hi
        have hi'_lt_k : i' < k := Nat.lt_of_succ_le hi
        have hi'_lt_k1 : i' < k + 1 := Nat.lt_succ_of_lt hi'_lt_k
        have hi'_lt_len : i' < t.seq.length := Nat.lt_trans hi'_lt_k hk_len
        have hi'_lt_seq'_len : i' < seq'.length := by rw [h_seq'_len]; exact hi'_lt_k1
        simp only [blocksSeq]
        have h_seq'_i' : seq'[i']? = some t.seq[i'] := by
          have h1 : seq'[i']? = some seq'[i'] := List.getElem?_eq_getElem hi'_lt_seq'_len
          have h2 : seq'[i'] = t.seq[i'] := by simp only [seq']; rw [List.getElem_take]
          rw [h1, h2]
        have h_seq_i' : t.seq[i']? = some t.seq[i'] := List.getElem?_eq_getElem hi'_lt_len
        simp only [h_seq'_i', h_seq_i']
        rw [ih hi']
        congr 1
        exact congr_arg G.blocksIntersecting (h_NS_eq i' hi'_lt_k)
    -- Show seq' is augmenting for (S', C')
    have h_aug' : G.IsAugmenting S' C' seq' := by
      intro ⟨i, hi⟩
      have hi_lt_k1 : i < k + 1 := by rw [← h_seq'_len]; exact hi
      have hi_lt_len : i < t.seq.length := by
        have h_k1_le : k + 1 ≤ t.seq.length := by
          have : k + 1 ≤ m + 1 := Nat.add_le_add_right (Nat.le_of_lt hk_lt_m) 1
          omega
        omega
      have h_seq'_i : seq'[i]'hi = t.seq[i]'hi_lt_len := by
        simp only [seq']; rw [List.getElem_take]
      have h_aug_i := t.isAugmenting ⟨i, hi_lt_len⟩
      have hi_le_k : i ≤ k := Nat.lt_succ_iff.mp hi_lt_k1
      constructor
      · -- seq'[i] ∈ V_{blocksSeq S' seq' i}
        change seq'.get ⟨i, hi⟩ ∈ G.blockUnion (G.blocksSeq S' seq' i)
        simp only [List.get_eq_getElem]
        rw [h_seq'_i, h_blocksSeq_eq i hi_le_k]
        exact h_aug_i.1
      constructor
      · -- Disjoint (neighborSet seq'[i]) (vertexSeq S' C' seq' i)
        change Disjoint (G.graph.neighborSet (seq'.get ⟨i, hi⟩)) (G.vertexSeq S' C' seq' i)
        simp only [List.get_eq_getElem]
        rw [h_seq'_i]
        -- Show vertexSeq S' C' seq' i ⊆ vertexSeq t.S t.C t.seq i
        -- Key: C' = t.C (by hC'_eq), so the base case is the same
        have h_vtx_sub : G.vertexSeq S' C' seq' i ⊆ G.vertexSeq t.S t.C t.seq i := by
          induction i with
          | zero =>
            simp only [vertexSeq]
            rw [hC'_eq]
          | succ i' ih_vtx =>
            have hi'_le_k : i' ≤ k := Nat.le_of_succ_le hi_le_k
            have hi'_lt_k : i' < k := Nat.lt_of_succ_le hi_le_k
            have hi'_lt_k1 : i' < k + 1 := Nat.lt_succ_of_lt hi'_lt_k
            have hi'_lt_seq'_len : i' < seq'.length := by rw [h_seq'_len]; exact hi'_lt_k1
            have hi'_lt_len' : i' < t.seq.length := Nat.lt_trans hi'_lt_k hk_len
            simp only [vertexSeq]
            have h_seq'_i'_some : seq'[i']? = some seq'[i'] :=
              List.getElem?_eq_getElem hi'_lt_seq'_len
            have h_seq_i'_some : t.seq[i']? = some t.seq[i'] :=
              List.getElem?_eq_getElem hi'_lt_len'
            simp only [h_seq'_i'_some, h_seq_i'_some]
            have h_seq'_i'_eq : seq'[i'] = t.seq[i'] := by
              simp only [seq']; rw [List.getElem_take]
            rw [h_seq'_i'_eq]
            intro x hx
            simp only [Set.mem_union, Set.mem_singleton_iff] at hx ⊢
            rcases hx with ((hx_vtx | hx_NS) | hx_eq)
            · left; left
              have h_seq'_i' : seq'[i'] = t.seq[i'] := by simp only [seq']; rw [List.getElem_take]
              have h_aug_i' := t.isAugmenting ⟨i', hi'_lt_len'⟩
              exact ih_vtx hi'_lt_seq'_len hi'_lt_k1 hi'_lt_len' h_seq'_i' h_aug_i' hi'_le_k hx_vtx
            · left; right
              rw [h_NS_eq i' hi'_lt_k] at hx_NS
              exact hx_NS
            · right; exact hx_eq
        exact Set.disjoint_of_subset_right h_vtx_sub h_aug_i.2.1
      -- Positive degree for non-last position
      intro h_not_last
      change 0 < (G.graph.neighborSet (seq'.get ⟨i, hi⟩) ∩ S').ncard
      simp only [List.get_eq_getElem]
      rw [h_seq'_i]
      have hi_lt_k : i < k := by
        simp only [h_seq'_len] at h_not_last
        omega
      have h_deg_eq : (G.graph.neighborSet t.seq[i] ∩ S').ncard =
          (G.graph.neighborSet t.seq[i] ∩ t.S).ncard := by
        congr 1; exact h_NS_eq i hi_lt_k
      rw [h_deg_eq]
      have hi_not_last_orig : i + 1 < t.seq.length := by
        have : i + 1 ≤ k := hi_lt_k
        have : k < m := hk_lt_m
        have : m < t.seq.length := hm
        omega
      exact h_aug_i.2.2 hi_not_last_orig
    -- Construct the new feasible tuple
    let t' : G.FeasibleTuple := ⟨S', C', seq', hS'_partial, hC'_subset, h_aug'⟩
    refine ⟨t', v_m, ?_, h_seq'_avoid_X, ?_, h_vm_not_X, h_indep, h_vm_indep_C, Or.inr rfl⟩
    · -- t'.C = X ∩ V_uncovered(S')
      simp only [t']
      rw [h_uncov_eq]
      exact hC'_eq.symm ▸ h_C_eq
    · -- Show FeasibleTupleLt t' t
      right
      constructor
      · -- |S'| = |S|
        have h_diff_card : (t.S \ G.blockOf v_m).ncard = t.S.ncard - 1 := by
          have h_add := Set.ncard_inter_add_ncard_diff_eq_ncard t.S (G.blockOf v_m) (Set.toFinite _)
          rw [h_S_inter_block, Set.ncard_singleton] at h_add
          omega
        have h_disj : Disjoint (t.S \ G.blockOf v_m) {v_m} := by
          rw [Set.disjoint_singleton_right]
          intro hv_in
          exact hv_in.2 (G.mem_blockOf v_m)
        calc S'.ncard = (G.oplus t.S v_m).ncard := rfl
          _ = ((t.S \ G.blockOf v_m) ∪ {v_m}).ncard := rfl
          _ = (t.S \ G.blockOf v_m).ncard + ({v_m} : Set V).ncard := by
              exact Set.ncard_union_eq h_disj (Set.toFinite _) (Set.toFinite _)
          _ = (t.S \ G.blockOf v_m).ncard + 1 := by simp only [Set.ncard_singleton]
          _ = (t.S.ncard - 1) + 1 := by rw [h_diff_card]
          _ = t.S.ncard := by
              have h_S_nonempty : t.S.Nonempty := ⟨s, hs_S⟩
              have h_ncard_pos : 0 < t.S.ncard := (Set.ncard_pos (Set.toFinite _)).mpr h_S_nonempty
              omega
      · -- degSeqLt (degreeSeq S' seq') (degreeSeq S seq)
        simp only [degSeqLt]
        right
        let d1 := G.degreeSeq S' seq'
        let d2 := G.degreeSeq t.S t.seq
        have h_d1_len : d1.length = k + 1 := by
          simp only [d1, degreeSeq, List.length_mapIdx, h_seq'_len]
        have h_d2_len : d2.length = t.seq.length := by
          simp only [d2, degreeSeq, List.length_mapIdx]
        -- Key: N_{S'}(seq[k]) = N_S(seq[k]) \ {s}
        have h_NS_k : G.graph.neighborSet t.seq[k] ∩ S' =
            (G.graph.neighborSet t.seq[k] ∩ t.S) \ {s} := by
          ext x
          simp only [S', oplus, Set.mem_inter_iff, Set.mem_union, Set.mem_diff,
            Set.mem_singleton_iff]
          constructor
          · intro ⟨hx_Nk, hx_S'⟩
            rcases hx_S' with ⟨hx_S, hx_not_block⟩ | hx_vm
            · refine ⟨⟨hx_Nk, hx_S⟩, ?_⟩
              intro hx_eq
              subst hx_eq
              exact hx_not_block hs_in_block
            · subst hx_vm
              exfalso
              exact h_vm_not_adj k hk_lt_m hx_Nk
          · intro ⟨⟨hx_Nk, hx_S⟩, hx_ne_s⟩
            refine ⟨hx_Nk, ?_⟩
            left
            constructor
            · exact hx_S
            · intro hx_block
              have hx_in_inter : x ∈ t.S ∩ G.blockOf v_m := ⟨hx_S, hx_block⟩
              rw [h_S_inter_block] at hx_in_inter
              exact hx_ne_s (Set.mem_singleton_iff.mp hx_in_inter)
        have hs_in_NS_k : s ∈ G.graph.neighborSet t.seq[k] ∩ t.S := ⟨hs_Nk, hs_S⟩
        have h_finite_k : (G.graph.neighborSet t.seq[k] ∩ t.S).Finite := Set.toFinite _
        have h_dk_lt : (G.graph.neighborSet t.seq[k] ∩ S').ncard <
            (G.graph.neighborSet t.seq[k] ∩ t.S).ncard := by
          rw [h_NS_k]
          calc ((G.graph.neighborSet t.seq[k] ∩ t.S) \ {s}).ncard
            = (G.graph.neighborSet t.seq[k] ∩ t.S).ncard - 1 := by
                exact Set.ncard_diff_singleton_of_mem hs_in_NS_k
            _ < (G.graph.neighborSet t.seq[k] ∩ t.S).ncard := by
                have h_pos : 0 < (G.graph.neighborSet t.seq[k] ∩ t.S).ncard := by
                  rw [Set.ncard_pos h_finite_k]
                  exact ⟨s, hs_in_NS_k⟩
                omega
        have h_deg_eq' : ∀ i (hi : i < k), (G.graph.neighborSet t.seq[i] ∩ S').ncard =
            (G.graph.neighborSet t.seq[i] ∩ t.S).ncard := by
          intro i hi
          congr 1
          exact h_NS_eq i hi
        have h_seq'_eq : ∀ i (hi : i < k + 1), seq'[i]'(by rw [h_seq'_len]; exact hi) =
            t.seq[i]'(Nat.lt_of_lt_of_le hi (by omega : k + 1 ≤ t.seq.length)) := by
          intro i hi
          simp only [seq', List.getElem_take]
        have hk_lt_d1 : k < d1.length := by simp only [h_d1_len]; exact Nat.lt_succ_self k
        have hk_lt_d2 : k < d2.length := by simp only [h_d2_len]; exact hk_len
        have h_d_eq : ∀ i (hi : i < k),
            d1[i]'(Nat.lt_of_lt_of_le hi (Nat.le_of_lt hk_lt_d1)) =
            d2[i]'(Nat.lt_of_lt_of_le hi (Nat.le_of_lt hk_lt_d2)) := by
          intro i hi
          simp only [d1, d2, degreeSeq, List.getElem_mapIdx]
          have hi_lt_k1 : i < k + 1 := Nat.lt_of_lt_of_le hi (Nat.le_of_lt (Nat.lt_succ_self k))
          have h_seq'_i := h_seq'_eq i hi_lt_k1
          conv_lhs => rw [h_seq'_i]
          exact h_deg_eq' i hi
        have h_d_k_lt : d1[k]'hk_lt_d1 < d2[k]'hk_lt_d2 := by
          simp only [d1, d2, degreeSeq, List.getElem_mapIdx]
          have h_seq'_k := h_seq'_eq k (Nat.lt_succ_self k)
          conv_lhs => rw [h_seq'_k]
          exact h_dk_lt
        constructor
        · exact list_lex_of_prefix_and_lt hk_lt_d1 hk_lt_d2 h_d_eq h_d_k_lt
        · exact not_prefix_of_ne_at hk_lt_d1 hk_lt_d2 (Nat.ne_of_lt h_d_k_lt)

/-- **Haxell's Theorem**: Let G be a graph of maximum degree Δ and let U be a
    (2Δ)-thick partition of V(G). Then there exists an independent transversal
    of (G, U).

    Here `h_thick : G.isThick (2 * G.maxDegree)` means each block has
    at least 2Δ vertices.

    Proof by well-founded induction:
    1. Consider the set of all feasible tuples (S, C, v)
    2. This set is nonempty (contains (∅, ∅, []))
    3. The partial order FeasibleTupleLt is well-founded
    4. Take a minimal tuple t = (S, C, v)
    5. If S is a full IT, we're done
    6. Otherwise, analyze the sequence v:
       - If v = [] and S is not full, can_extend_sequence gives a contradiction
       - If v ≠ [] and d_m = 0, improve_from_zero_degree gives a contradiction
       - If v ≠ [] and all d_i > 0, can_extend_sequence gives a contradiction
    7. Therefore S must be a full IT -/
theorem PartitionedGraph.haxell_theorem
    (h_thick : G.isThick (2 * G.maxDegree)) : ∃ S, G.IsIndependentTransversal S := by
  -- The proof uses well-founded induction on feasible tuples
  -- Key insight: for any feasible tuple t that's not a full IT, we can find a strictly smaller one
  -- By well-foundedness, any minimal tuple must have S being a full IT
  suffices h : ∀ t : G.FeasibleTuple, t.C = ∅ → (G.uncoveredBlocks t.S).Nonempty →
      ∃ t' : G.FeasibleTuple, t'.C = ∅ ∧ G.FeasibleTupleLt t' t by
    -- Use well-founded recursion to find a tuple where uncoveredBlocks is empty
    have hwf := G.feasibleTuple_lt_wf
    -- Start with the empty tuple
    let t₀ : G.FeasibleTuple := ⟨∅, ∅, [], G.isPartialIT_empty, Set.empty_subset _,
      fun k => Fin.elim0 k⟩
    have h_t0_C_empty : t₀.C = ∅ := rfl
    -- Use WellFounded.min to find a minimal feasible tuple in the subset with C = ∅
    -- Define the set of feasible tuples with C = ∅ (nonempty since it contains t₀)
    let tuples : Set G.FeasibleTuple := {t | t.C = ∅}
    have h_nonempty : tuples.Nonempty := ⟨t₀, h_t0_C_empty⟩
    -- Get a minimal element using well-foundedness
    let t_min := hwf.min tuples h_nonempty
    have h_t_min_C_empty : t_min.C = ∅ := hwf.min_mem tuples h_nonempty
    -- The minimal tuple has empty uncoveredBlocks (otherwise h would give a smaller one)
    have h_uncovered_empty : G.uncoveredBlocks t_min.S = ∅ := by
      by_contra h_ne
      have h_ne' : (G.uncoveredBlocks t_min.S).Nonempty := Set.nonempty_iff_ne_empty.mpr h_ne
      obtain ⟨t', h_t'_C, ht'⟩ := h t_min h_t_min_C_empty h_ne'
      have h_t'_mem : t' ∈ tuples := h_t'_C
      exact hwf.not_lt_min tuples h_t'_mem ht'
    -- A partial IT with no uncovered blocks is a full IT
    use t_min.S
    exact PartitionedGraph.partialIT_of_no_uncovered G t_min.S t_min.isPartialIT h_uncovered_empty
  -- Prove the key lemma: if uncoveredBlocks is nonempty and C = ∅,
  -- we can find a smaller tuple with C = ∅
  intro t h_C_empty h_not_full
  -- Case analysis on the sequence
  by_cases h_seq_empty : t.seq = []
  · -- Empty sequence: use can_extend_sequence to extend it
    have h_can_extend := G.can_extend_sequence t h_thick
      (fun i hi => by simp [h_seq_empty] at hi) h_not_full h_C_empty
    -- h_can_extend gives a vertex v that can extend the sequence
    obtain ⟨v, hv_mem, hv_disj⟩ := h_can_extend
    -- Construct new tuple with sequence [v]
    let new_seq : List V := [v]
    -- Show the extended sequence gives a valid FeasibleTuple
    have h_aug_new : G.IsAugmenting t.S t.C new_seq := by
      intro ⟨k, hk⟩
      simp only [new_seq, List.length_singleton] at hk
      have hk0 : k = 0 := Nat.lt_one_iff.mp hk
      subst hk0
      simp only [new_seq]
      refine ⟨?_, ?_, ?_⟩
      · -- v ∈ V_{B_0}
        -- blocksSeq t.S [v] 0 = uncoveredBlocks t.S
        simp only [blocksSeq]
        simp only [h_seq_empty] at hv_mem
        exact hv_mem
      · -- Disjoint (neighborSet v) (vertexSeq t.S t.C [v] 0)
        -- vertexSeq t.S t.C [v] 0 = t.C
        simp only [vertexSeq]
        simp only [h_seq_empty] at hv_disj
        exact hv_disj
      · -- Condition 3: k + 1 < length → positive degree
        -- k = 0 and length = 1, so k + 1 = 1 = length, condition is vacuous
        intro h_lt
        simp only [List.length_singleton] at h_lt
        omega
    let t' : G.FeasibleTuple := ⟨t.S, t.C, new_seq, t.isPartialIT, t.C_subset, h_aug_new⟩
    use t'
    constructor
    · -- t'.C = t.C = ∅
      exact h_C_empty
    · -- Show t' < t: same |S|, but new_seq = [v] extends [] = t.seq
      right
      constructor
      · rfl  -- same S, same ncard
      · -- degSeqLt (degreeSeq S [v]) (degreeSeq S [])
        -- [] is a prefix of [v], so [v] < [] in our ordering
        simp only [degSeqLt, h_seq_empty, degreeSeq, List.mapIdx_nil]
        left
        constructor
        · exact List.nil_prefix
        · exact List.cons_ne_nil _ _
  · -- Non-empty sequence: check if last degree is zero
    by_cases h_last_zero : G.degreeAt t.S t.seq t.seq.length = 0
    · -- Last degree is zero: use improve_from_zero_degree
      obtain ⟨t', hC, _, _, hlt⟩ := G.improve_from_zero_degree t h_seq_empty h_last_zero
      exact ⟨t', hC, hlt⟩
    · -- All degrees are positive
      have h_all_pos : ∀ i, i < t.seq.length → 0 < G.degreeAt t.S t.seq (i + 1) := by
        intro i hi
        by_cases h_last : i + 1 = t.seq.length
        · simp only [h_last] at h_last_zero ⊢
          omega
        · -- For earlier indices, augmenting condition gives positive degree
          have h_aug := t.isAugmenting ⟨i, hi⟩
          have h_lt_len : i + 1 < t.seq.length := by omega
          -- h_aug.2.2 gives: (G.graph.neighborSet t.seq[i] ∩ t.S).ncard > 0
          -- Need to show this equals degreeAt t.S t.seq (i + 1)
          simp only [degreeAt]
          have h_idx : t.seq[(i + 1) - 1]? = some t.seq[i] := by
            simp only [Nat.add_sub_cancel]
            exact List.getElem?_eq_getElem hi
          simp only [h_idx]
          exact h_aug.2.2 h_lt_len
      have h_can_extend := G.can_extend_sequence t h_thick h_all_pos h_not_full h_C_empty
      -- h_can_extend gives a vertex v that can extend the sequence
      -- Construct new tuple with extended sequence t.seq ++ [v]
      obtain ⟨v, hv_mem, hv_disj⟩ := h_can_extend
      let new_seq : List V := t.seq ++ [v]
      -- Show the extended sequence gives a valid FeasibleTuple
      have h_aug_new : G.IsAugmenting t.S t.C new_seq := by
        -- The extended sequence satisfies augmenting:
        -- Key: blocksSeq and vertexSeq use List.take, so they agree on prefixes
        intro ⟨k, hk⟩
        simp only [new_seq, List.length_append, List.length_singleton] at hk
        by_cases h_last : k = t.seq.length
        · -- k is the new last index (for vertex v)
          subst h_last
          constructor
          · -- v ∈ V_{B_{t.seq.length}}
            -- new_seq[t.seq.length] = v and blocksSeq agrees with t.seq
            change (t.seq ++ [v])[t.seq.length] ∈
                G.blockUnion (G.blocksSeq t.S (t.seq ++ [v]) t.seq.length)
            rw [List.getElem_append_right (le_refl _)]
            simp only [Nat.sub_self, List.getElem_cons_zero]
            rw [PartitionedGraph.blocksSeq_append G t.S t.seq v t.seq.length (le_refl _)]
            exact hv_mem
          constructor
          · -- Condition 2: Disjoint (neighborSet v) (vertexSeq ... t.seq.length)
            change Disjoint (G.graph.neighborSet (t.seq ++ [v])[t.seq.length])
                (G.vertexSeq t.S t.C (t.seq ++ [v]) t.seq.length)
            rw [List.getElem_append_right (le_refl _)]
            simp only [Nat.sub_self, List.getElem_cons_zero]
            rw [PartitionedGraph.vertexSeq_append G t.S t.C t.seq v t.seq.length (le_refl _)]
            exact hv_disj
          · -- Condition 3: k+1 < new_seq.length → positive degree
            -- But k = t.seq.length and new_seq.length = t.seq.length + 1, so k+1 = new_seq.length
            intro h_lt
            -- h_lt says t.seq.length + 1 < (t.seq ++ [v]).length = t.seq.length + 1
            exfalso
            simp only [new_seq, List.length_append, List.length_singleton] at h_lt
            omega
        · -- k < t.seq.length: inherited from t.isAugmenting
          have hk_lt : k < t.seq.length := by omega
          have h_aug_k := t.isAugmenting ⟨k, hk_lt⟩
          constructor
          · -- Condition 1: v_k ∈ V_{B_k}
            change (t.seq ++ [v])[k] ∈ G.blockUnion (G.blocksSeq t.S (t.seq ++ [v]) k)
            rw [List.getElem_append_left hk_lt]
            rw [PartitionedGraph.blocksSeq_append G t.S t.seq v k (le_of_lt hk_lt)]
            exact h_aug_k.1
          constructor
          · -- Condition 2: v_k not adjacent to C_k
            change Disjoint (G.graph.neighborSet (t.seq ++ [v])[k])
                (G.vertexSeq t.S t.C (t.seq ++ [v]) k)
            rw [List.getElem_append_left hk_lt]
            rw [PartitionedGraph.vertexSeq_append G t.S t.C t.seq v k (le_of_lt hk_lt)]
            exact h_aug_k.2.1
          -- Condition 3: positive degree if k+1 < new_seq.length
          intro hk_lt_new
          change 0 < (G.graph.neighborSet (t.seq ++ [v])[k] ∩ t.S).ncard
          rw [List.getElem_append_left hk_lt]
          -- Either k + 1 < t.seq.length (use h_aug_k.2.2) or k + 1 = t.seq.length (use h_all_pos)
          by_cases h_case : k + 1 < t.seq.length
          · exact h_aug_k.2.2 h_case
          · -- k + 1 = t.seq.length, so k = t.seq.length - 1
            have h_eq : k + 1 = t.seq.length := by
              simp only [new_seq, List.length_append, List.length_singleton] at hk_lt_new
              omega
            -- Use h_all_pos: for k < t.seq.length, 0 < degreeAt t.S t.seq (k + 1)
            have h_pos := h_all_pos k hk_lt
            simp only [degreeAt, Nat.add_sub_cancel] at h_pos
            rw [List.getElem?_eq_getElem hk_lt] at h_pos
            exact h_pos
      let t' : G.FeasibleTuple := ⟨t.S, t.C, new_seq, t.isPartialIT, t.C_subset, h_aug_new⟩
      use t'
      constructor
      · -- t'.C = t.C = ∅
        exact h_C_empty
      · -- Show t' < t: same |S|, but new_seq extends t.seq
        right
        constructor
        · rfl  -- same S, same ncard
        · -- degSeqLt (degreeSeq S new_seq) (degreeSeq S t.seq)
          -- t.seq is a proper prefix of new_seq, so new_seq < t.seq in our ordering
          simp only [degSeqLt]
          left
          constructor
          · -- degreeSeq t.S t.seq is a prefix of degreeSeq t.S new_seq
            simp only [degreeSeq]
            rw [List.mapIdx_append]
            exact List.prefix_append _ _
          · -- degreeSeq t.S new_seq ≠ degreeSeq t.S t.seq
            -- The append of a non-empty list is not equal to the original (lengths differ)
            simp only [degreeSeq, ne_eq]
            rw [List.mapIdx_append]
            intro h_eq
            have h_len_eq : (List.mapIdx (fun i v => (G.graph.neighborSet v ∩ t.S).ncard) t.seq ++
                List.mapIdx (fun i v => (G.graph.neighborSet v ∩ t.S).ncard) [v]).length =
                (List.mapIdx (fun i v => (G.graph.neighborSet v ∩ t.S).ncard) t.seq).length := by
              congr 1
            simp only [List.length_append, List.mapIdx_cons, List.length_singleton,
              List.mapIdx_nil] at h_len_eq
            omega

omit [DecidableEq V] [Fintype V] in
/-- Helper: union preserves X-disjointness -/
lemma disjoint_union_singleton {S X : Set V} {v : V}
    (hSX : Disjoint S X) (hv : v ∉ X) : Disjoint (S ∪ {v}) X := by
  rw [Set.disjoint_iff] at hSX ⊢
  intro x ⟨hx_S, hx_X⟩
  rcases hx_S with hxS | hxv
  · exact hSX ⟨hxS, hx_X⟩
  · rw [Set.mem_singleton_iff] at hxv; subst hxv; exact hv hx_X

omit [Fintype V] [DecidableRel G.graph.Adj] in
/-- Helper: oplus preserves X-disjointness -/
lemma PartitionedGraph.oplus_disjoint {S X : Set V} {v : V}
    (hSX : Disjoint S X) (hv : v ∉ X) : Disjoint (G.oplus S v) X := by
  simp only [oplus]
  rw [Set.disjoint_iff] at hSX ⊢
  intro x ⟨hx_S', hx_X⟩
  rcases hx_S' with ⟨hxS, _⟩ | hxv
  · exact hSX ⟨hxS, hx_X⟩
  · rw [Set.mem_singleton_iff] at hxv; subst hxv; exact hv hx_X

omit [DecidableRel G.graph.Adj] in
/-- Strengthen `improve_from_zero_degree` to track X-disjointness.
    Key observation: S' ⊆ S ∪ {seq[m]}, so if S ∩ X = ∅ and seq[m] ∉ X, then S' ∩ X = ∅. -/
lemma PartitionedGraph.improve_from_zero_degree_X (t : G.FeasibleTuple)
    (X : Set V)
    (h_nonempty : t.seq ≠ [])
    (h_last_zero : G.degreeAt t.S t.seq t.seq.length = 0)
    (_h_C_empty : t.C = ∅)
    (h_SX : Disjoint t.S X)
    (h_seq_avoid : ∀ i (hi : i < t.seq.length), t.seq[i] ∉ X) :
    ∃ t' : G.FeasibleTuple, t'.C = ∅ ∧ Disjoint t'.S X ∧
        (∀ i (hi : i < t'.seq.length), t'.seq[i] ∉ X) ∧ G.FeasibleTupleLt t' t := by
  -- Get the tuple from improve_from_zero_degree (with structural properties)
  obtain ⟨t', h_t'_C, h_S_struct, h_seq_struct, ht'_lt⟩ :=
    G.improve_from_zero_degree t h_nonempty h_last_zero
  use t'
  refine ⟨h_t'_C, ?_, ?_, ht'_lt⟩
  · -- Disjoint t'.S X: every element of t'.S is in t.S (disjoint from X) or a seq element (∉ X)
    rw [Set.disjoint_left]
    intro x hx hx_X
    rcases h_S_struct x hx with hxS | ⟨i, hi, hx_eq⟩
    · exact Set.disjoint_left.mp h_SX hxS hx_X
    · exact h_seq_avoid i hi (hx_eq ▸ hx_X)
  · -- t'.seq avoids X: each element of t'.seq is in t.seq, and t.seq avoids X
    intro i hi
    have h_mem : t'.seq[i] ∈ t.seq := h_seq_struct _ (List.getElem_mem hi)
    obtain ⟨j, hj, h_eq⟩ := List.mem_iff_getElem.mp h_mem
    rw [← h_eq]; exact h_seq_avoid j hj

/-- **Haxell's theorem with constraint**: Let G be a (2Δ)-thick partitioned graph.
    Given a partial IT S₀ and a constraint set X with |X| < Δ, there exists a
    full IT S' that avoids X.

    This is a key building block for the precolor theorem. The proof follows the
    standard Haxell descent but uses `can_extend_sequence_with_constraint` and
    `improve_from_zero_degree_precolor` to ensure all vertices in the final IT
    avoid X.

    Note: This theorem doesn't guarantee S' extends S₀ - the descent may swap
    vertices even in blocks originally covered by S₀. For the full precolor
    theorem, reconfigurability is tracked separately. -/
theorem PartitionedGraph.haxell_with_constraint
    (S₀ : Set V) (X : Set V)
    (_hS₀ : G.IsPartialIT S₀)
    (hX_bound : X.ncard < G.maxDegree)
    (h_thick : G.isThick (2 * G.maxDegree)) :
    ∃ S', G.IsIndependentTransversal S' ∧ Disjoint S' X := by
  -- The proof uses well-founded descent tracking:
  -- 1. C = ∅ (like standard Haxell)
  -- 2. S ∩ X = ∅ (X-avoidance invariant)
  -- 3. All seq vertices avoid X
  --
  -- The key insight: we start from (∅, ∅, []) and ensure every vertex
  -- added to S avoids X (via can_extend_sequence_with_constraint).
  suffices h : ∀ t : G.FeasibleTuple, t.C = ∅ → Disjoint t.S X →
      (∀ i (hi : i < t.seq.length), t.seq[i] ∉ X) →
      (G.uncoveredBlocks t.S).Nonempty →
      ∃ t' : G.FeasibleTuple, t'.C = ∅ ∧ Disjoint t'.S X ∧
          (∀ i (hi : i < t'.seq.length), t'.seq[i] ∉ X) ∧ G.FeasibleTupleLt t' t by
    -- Use well-founded descent to find minimal tuple with our invariants
    have hwf := G.feasibleTuple_lt_wf
    let t₀ : G.FeasibleTuple := ⟨∅, ∅, [], G.isPartialIT_empty, Set.empty_subset _,
      fun k => Fin.elim0 k⟩
    -- t₀ satisfies all invariants
    have h_t0_C : t₀.C = ∅ := rfl
    have h_t0_SX : Disjoint t₀.S X := Set.empty_disjoint X
    have h_t0_seq : ∀ i (hi : i < t₀.seq.length), t₀.seq[i] ∉ X := fun i hi =>
      (Nat.not_lt_zero i hi).elim
    -- Define the set of tuples satisfying our invariants
    let good : Set G.FeasibleTuple := {t | t.C = ∅ ∧ Disjoint t.S X ∧
        ∀ i (hi : i < t.seq.length), t.seq[i] ∉ X}
    have h_good_nonempty : good.Nonempty := ⟨t₀, h_t0_C, h_t0_SX, h_t0_seq⟩
    -- Get minimal tuple in good
    let t_min := hwf.min good h_good_nonempty
    have h_min_mem := hwf.min_mem good h_good_nonempty
    have h_min_C : t_min.C = ∅ := h_min_mem.1
    have h_min_SX : Disjoint t_min.S X := h_min_mem.2.1
    have h_min_seq : ∀ i (hi : i < t_min.seq.length), t_min.seq[i] ∉ X := h_min_mem.2.2
    -- t_min has empty uncoveredBlocks (otherwise h gives a smaller good tuple)
    have h_uncovered_empty : G.uncoveredBlocks t_min.S = ∅ := by
      by_contra h_ne
      have h_ne' : (G.uncoveredBlocks t_min.S).Nonempty := Set.nonempty_iff_ne_empty.mpr h_ne
      obtain ⟨t', h_t'_C, h_t'_SX, h_t'_seq, ht'_lt⟩ := h t_min h_min_C h_min_SX h_min_seq h_ne'
      have h_t'_mem : t' ∈ good := ⟨h_t'_C, h_t'_SX, h_t'_seq⟩
      exact hwf.not_lt_min good h_t'_mem ht'_lt
    -- t_min.S is a full IT avoiding X
    use t_min.S
    constructor
    · exact G.partialIT_of_no_uncovered t_min.S t_min.isPartialIT h_uncovered_empty
    · exact h_min_SX
  -- Prove the key descent lemma
  intro t h_C_empty h_SX h_seq_avoid h_not_full
  by_cases h_seq_empty : t.seq = []
  · -- Empty sequence: extend with vertex avoiding X
    -- We need to use can_extend_sequence_with_constraint even though C = ∅
    -- The constraint v ∉ X comes from choosing v disjoint from C ∪ (something involving X)
    -- Actually, for C = ∅, can_extend_sequence already works, but we need v ∉ X
    -- Use the counting argument: |N(C_m) ∩ V_{B_m}| + |X ∩ V_{B_m}| < |V_{B_m}|
    -- Since C_m = ∅ (from C = ∅ and empty seq), we just need |X| < |V_{B_m}|
    -- This follows from |X| < Δ and |V_{B_m}| ≥ 2Δ (thickness)
    have h_can_extend : ∃ v ∈ G.blockUnion (G.blocksSeq t.S t.seq t.seq.length),
        Disjoint (G.graph.neighborSet v) (G.vertexSeq t.S t.C t.seq t.seq.length) ∧ v ∉ X := by
      -- Need v ∈ V_uncovered with v ∉ X
      -- |V_uncovered| ≥ 2Δ (from thickness applied to any uncovered block)
      -- |X| < Δ
      -- So V_uncovered \ X is nonempty
      obtain ⟨U, hU⟩ := h_not_full
      have hU_blocks : U ∈ G.blocks := by
        simp only [uncoveredBlocks, Set.mem_diff, blocksIntersecting] at hU
        exact hU.1
      have hU_size : (2 * G.maxDegree) ≤ U.ncard := h_thick U hU_blocks
      -- U \ X is nonempty since |U| ≥ 2Δ > Δ > |X|
      have h_U_diff_X_nonempty : (U \ X).Nonempty := by
        by_contra h_empty
        rw [Set.not_nonempty_iff_eq_empty] at h_empty
        have hU_sub_X : U ⊆ X := by
          intro u hu
          by_contra hu_not_X
          have : u ∈ U \ X := ⟨hu, hu_not_X⟩
          rw [h_empty] at this
          exact this
        have hU_le_X : U.ncard ≤ X.ncard := Set.ncard_le_ncard hU_sub_X (Set.toFinite _)
        omega
      obtain ⟨v, hv_U, hv_not_X⟩ := h_U_diff_X_nonempty
      refine ⟨v, ?_, ?_, hv_not_X⟩
      · -- v ∈ blockUnion (blocksSeq t.S [] 0) = blockUnion uncoveredBlocks
        simp only [h_seq_empty, List.length_nil, blocksSeq]
        rw [G.blockUnion_eq_sUnion (G.uncoveredBlocks_subset t.S)]
        exact Set.mem_sUnion_of_mem hv_U hU
      · -- Disjoint (neighborSet v) (vertexSeq t.S t.C [] 0) = Disjoint _ C = Disjoint _ ∅
        simp only [h_seq_empty, List.length_nil, vertexSeq, h_C_empty]
        exact Set.disjoint_right.mpr (fun _ hx => hx.elim)
    obtain ⟨v, hv_mem, hv_disj, hv_not_X⟩ := h_can_extend
    -- Construct new tuple with sequence [v]
    let new_seq : List V := [v]
    have h_aug_new : G.IsAugmenting t.S t.C new_seq := by
      intro ⟨k, hk⟩
      simp only [new_seq, List.length_singleton] at hk
      have hk0 : k = 0 := Nat.lt_one_iff.mp hk
      subst hk0
      simp only [new_seq]
      refine ⟨?_, ?_, ?_⟩
      · simp only [blocksSeq, h_seq_empty] at hv_mem ⊢; exact hv_mem
      · simp only [vertexSeq, h_seq_empty, h_C_empty] at hv_disj ⊢; exact hv_disj
      · intro h_lt; simp only [List.length_singleton] at h_lt; omega
    let t' : G.FeasibleTuple := ⟨t.S, t.C, new_seq, t.isPartialIT, t.C_subset, h_aug_new⟩
    use t'
    refine ⟨h_C_empty, h_SX, ?_, ?_⟩
    · -- new seq avoids X
      intro i hi
      have hi0 : i = 0 := Nat.lt_one_iff.mp hi
      subst hi0
      exact hv_not_X
    · -- FeasibleTupleLt
      right; constructor
      · rfl
      simp only [degSeqLt, h_seq_empty, degreeSeq, List.mapIdx_nil]
      left; exact ⟨List.nil_prefix, List.cons_ne_nil _ _⟩
  · -- Non-empty sequence: check if last degree is zero
    by_cases h_last_zero : G.degreeAt t.S t.seq t.seq.length = 0
    · -- Last degree is zero: use improve_from_zero_degree_X
      exact G.improve_from_zero_degree_X t X h_seq_empty h_last_zero h_C_empty h_SX h_seq_avoid
    · -- All degrees positive: extend sequence with vertex avoiding X
      -- Use counting to find v ∈ V_{B_m} avoiding both N(C_m) and X
      have h_all_pos : ∀ i, i < t.seq.length → 0 < G.degreeAt t.S t.seq (i + 1) := by
        intro i hi
        by_cases h_last : i + 1 = t.seq.length
        · simp only [h_last] at h_last_zero ⊢; omega
        · have h_aug := t.isAugmenting ⟨i, hi⟩
          have h_lt_len : i + 1 < t.seq.length := by omega
          simp only [degreeAt]
          have h_idx : t.seq[(i + 1) - 1]? = some t.seq[i] := by
            simp only [Nat.add_sub_cancel]; exact List.getElem?_eq_getElem hi
          simp only [h_idx]; exact h_aug.2.2 h_lt_len
      -- Standard counting gives v ∈ V_{B_m} with v ⊥ C_m (since C = ∅)
      have h_can_extend := G.can_extend_sequence t h_thick h_all_pos h_not_full h_C_empty
      obtain ⟨v, hv_mem, hv_disj⟩ := h_can_extend
      -- Now check if v ∉ X; if so, we're done. Otherwise, find another vertex.
      by_cases hv_X : v ∈ X
      · -- Need to find a different vertex. The counting argument:
        -- |N(C_m) ∩ V_{B_m}| + |X ∩ V_{B_m}| < |V_{B_m}|
        -- Since V_{B_m} \ (N(C_m) ∪ X) is nonempty.
        -- We use the counting lemma structure with X as additional exclusion.
        let m := t.seq.length
        let B_m := G.blocksSeq t.S t.seq m
        let C_m := G.vertexSeq t.S t.C t.seq m
        let V_Bm := G.blockUnion B_m
        -- From counting_with_constraint: Δ|C_m| + |C| < |V_{B_m}|, with |C| = 0 since C = ∅
        have h_C_ncard_zero : t.C.ncard = 0 := by simp only [h_C_empty, Set.ncard_empty]
        have h_C_bound' : t.C.ncard < G.maxDegree := by
          simp only [h_C_ncard_zero]
          -- Δ > 0 follows from hX_bound: X.ncard < G.maxDegree
          -- If Δ = 0, then X.ncard < 0, contradiction
          omega
        have h_C_uncov' : t.C.ncard ≤ (G.uncoveredBlocks t.S).ncard := by
          simp only [h_C_ncard_zero]; exact Nat.zero_le _
        have h_standard := G.counting_with_constraint t h_thick h_all_pos h_not_full
          h_C_bound' h_C_uncov'
        simp only [h_C_ncard_zero, add_zero] at h_standard
        -- We need Δ|C_m| + |X| < |V_{B_m}|
        have h_Bm_pos : 0 < B_m.ncard := by
          have h_uncov_subset : G.uncoveredBlocks t.S ⊆ B_m :=
            G.uncoveredBlocks_subset_blocksSeq t.S t.seq m (le_refl m)
          exact (Set.ncard_pos (Set.toFinite _)).mpr (h_not_full.mono h_uncov_subset)
        have h_VBm_large : 2 * G.maxDegree ≤ V_Bm.ncard := by
          -- Each block in B_m has at least 2Δ vertices
          -- V_Bm = ⋃ U ∈ B_m, U, so |V_Bm| ≥ max{|U| : U ∈ B_m} ≥ 2Δ
          have ⟨U, hU_mem⟩ := (Set.ncard_pos (Set.toFinite B_m)).mp h_Bm_pos
          have hU_blocks : U ∈ G.blocks := G.blocksSeq_subset t.S t.seq m hU_mem
          have hU_thick : 2 * G.maxDegree ≤ U.ncard := h_thick U hU_blocks
          have hU_sub : U ⊆ V_Bm := by
            change U ⊆ G.blockUnion B_m
            rw [G.blockUnion_eq_sUnion (G.blocksSeq_subset t.S t.seq m)]
            exact Set.subset_sUnion_of_mem hU_mem
          calc 2 * G.maxDegree ≤ U.ncard := hU_thick
            _ ≤ V_Bm.ncard := Set.ncard_le_ncard hU_sub (Set.toFinite _)
        -- Counting: |N(C_m) ∩ V_Bm| + |X ∩ V_Bm| ≤ Δ|C_m| + |X| < |V_Bm|
        -- This follows from h_standard (Δ|C_m| < |V_Bm|), h3 (2Δ ≤ |V_Bm|), and hX_bound (|X| < Δ)
        -- Key insight: if Δ|C_m| ≤ |V_Bm|/2, then |V_Bm| - Δ|C_m| ≥ |V_Bm|/2 ≥ Δ > |X|
        -- If Δ|C_m| > |V_Bm|/2, then since Δ|C_m| < |V_Bm| we need
        -- |X| < |V_Bm| - Δ|C_m| < |V_Bm|/2 ≤ Δ
        have h_count_with_X : G.maxDegree * C_m.ncard + X.ncard < V_Bm.ncard := by
          -- Use structural bounds: |V_Bm| ≥ 2Δ|B_m| and |C_m|+1 ≤ 2|B_m|
          -- Step 1: |V_Bm| ≥ 2Δ|B_m|
          have h_Bm_size : 2 * G.maxDegree * B_m.ncard ≤ V_Bm.ncard :=
            G.ncard_blockUnion_ge_of_thick (G.blocksSeq_subset t.S t.seq m)
              (Set.toFinite B_m) (2 * G.maxDegree)
              (fun U hU => h_thick U (G.blocksSeq_subset t.S t.seq m hU))
          -- Step 2: Structural bounds on |C_m| and |B_m|
          let deg_sum := ((G.degreeSeq t.S t.seq).take m).sum
          have h_Cm_bound := G.vertexSeq_card_bound t m (le_refl m)
          have h_Bm_eq : B_m.ncard = (G.uncoveredBlocks t.S).ncard + deg_sum :=
            G.blocksSeq_card_eq t.S t.C t.seq t.isPartialIT t.isAugmenting m (le_refl m)
          -- Step 3: deg_sum ≥ m (each d_i ≥ 1)
          have h_sum_ge_m : m ≤ deg_sum := by
            have h_deg_len : (G.degreeSeq t.S t.seq).length = m := by
              simp only [degreeSeq, List.length_mapIdx, m]
            have h_take_all : (G.degreeSeq t.S t.seq).take m = G.degreeSeq t.S t.seq :=
              List.take_of_length_le (le_of_eq h_deg_len)
            simp only [deg_sum, h_take_all]
            have h_all_pos' : ∀ i (hi : i < (G.degreeSeq t.S t.seq).length),
                0 < (G.degreeSeq t.S t.seq)[i] := by
              intro i hi
              rw [h_deg_len] at hi
              simp only [degreeSeq, List.getElem_mapIdx]
              simp only [degreeAt] at h_all_pos
              have h_seq_idx : t.seq[(i + 1) - 1]? = some t.seq[i] := by
                simp only [Nat.add_sub_cancel]
                exact List.getElem?_eq_getElem hi
              specialize h_all_pos i hi
              simp only [h_seq_idx] at h_all_pos
              exact h_all_pos
            have h_sum_ge : (G.degreeSeq t.S t.seq).length ≤
                (G.degreeSeq t.S t.seq).sum := by
              have : ∀ l : List ℕ, (∀ i (hi : i < l.length), 0 < l[i]) →
                  l.length ≤ l.sum := by
                intro l
                induction l with
                | nil => intro _; simp
                | cons x xs ih =>
                  intro h_pos
                  simp only [List.length_cons, List.sum_cons]
                  have h_x_pos : 0 < x := h_pos 0 (Nat.zero_lt_succ _)
                  have h_ih : xs.length ≤ xs.sum :=
                    ih (fun i hi => h_pos (i + 1) (Nat.add_lt_add_right hi 1))
                  omega
              exact this _ h_all_pos'
            rw [h_deg_len] at h_sum_ge
            exact h_sum_ge
          -- Step 4: |uncov| ≥ 1
          have h_uncov_pos : 0 < (G.uncoveredBlocks t.S).ncard :=
            (Set.ncard_pos (Set.toFinite _)).2 h_not_full
          -- Step 5: |C_m| ≤ m + deg_sum and |C_m| + 1 ≤ 2|B_m|
          have h_Cm_le : C_m.ncard ≤ m + deg_sum := by
            calc C_m.ncard ≤ t.C.ncard + m + deg_sum := h_Cm_bound
              _ = 0 + m + deg_sum := by rw [h_C_ncard_zero]
              _ = m + deg_sum := by omega
          have h_Cm_plus_one : C_m.ncard + 1 ≤ 2 * B_m.ncard := by
            rw [h_Bm_eq]; omega
          -- Step 6: Chain Δ|C_m| + |X| < Δ(|C_m|+1) ≤ 2Δ|B_m| ≤ |V_Bm|
          have h_mul_step : G.maxDegree * (C_m.ncard + 1) ≤
              2 * G.maxDegree * B_m.ncard := by
            have h1 := Nat.mul_le_mul_left G.maxDegree h_Cm_plus_one
            rw [← mul_assoc, mul_comm G.maxDegree 2] at h1
            exact h1
          calc G.maxDegree * C_m.ncard + X.ncard
            < G.maxDegree * C_m.ncard + G.maxDegree := by omega
            _ = G.maxDegree * (C_m.ncard + 1) := by
                rw [mul_add, mul_one]
            _ ≤ 2 * G.maxDegree * B_m.ncard := h_mul_step
            _ ≤ V_Bm.ncard := h_Bm_size
        -- Find v ∈ V_Bm \ (N(C_m) ∪ X)
        let avoid_nbhd := ⋃ c ∈ C_m, G.graph.neighborSet c ∩ V_Bm
        let avoid_X := X ∩ V_Bm
        have h_nbhd_size : avoid_nbhd.ncard ≤ G.maxDegree * C_m.ncard :=
          G.ncard_biUnion_neighborSet_inter_le (Set.toFinite C_m)
        have h_X_size : avoid_X.ncard ≤ X.ncard := Set.ncard_inter_le_ncard_left X V_Bm
        have h_total_avoid : (avoid_nbhd ∩ V_Bm).ncard + (avoid_X ∩ V_Bm).ncard < V_Bm.ncard := by
          have h1 : (avoid_nbhd ∩ V_Bm).ncard ≤ avoid_nbhd.ncard :=
            Set.ncard_inter_le_ncard_left _ _
          have h2 : avoid_X ∩ V_Bm = avoid_X := Set.inter_eq_left.mpr Set.inter_subset_right
          calc (avoid_nbhd ∩ V_Bm).ncard + (avoid_X ∩ V_Bm).ncard
            = (avoid_nbhd ∩ V_Bm).ncard + avoid_X.ncard := by rw [h2]
            _ ≤ avoid_nbhd.ncard + avoid_X.ncard := Nat.add_le_add_right h1 _
            _ ≤ G.maxDegree * C_m.ncard + X.ncard := Nat.add_le_add h_nbhd_size h_X_size
            _ < V_Bm.ncard := h_count_with_X
        have h_exists := Set.exists_mem_not_mem_of_ncard_gt_union
          (Set.toFinite V_Bm) h_total_avoid
        obtain ⟨v', hv'_mem, hv'_not_nbhd, hv'_not_X⟩ := h_exists
        -- v' ∈ V_Bm, v' ∉ N(C_m), v' ∉ X
        have hv'_disj : Disjoint (G.graph.neighborSet v') C_m := by
          rw [Set.disjoint_left]
          intro w hw_Nv' hw_Cm
          apply hv'_not_nbhd
          exact Set.mem_biUnion hw_Cm ⟨G.graph.adj_symm hw_Nv', hv'_mem⟩
        have hv'_not_X' : v' ∉ X := fun h => hv'_not_X ⟨h, hv'_mem⟩
        -- Construct new tuple with extended sequence
        let new_seq : List V := t.seq ++ [v']
        have h_aug_new : G.IsAugmenting t.S t.C new_seq := by
          intro ⟨k, hk⟩
          simp only [new_seq, List.length_append, List.length_singleton] at hk
          by_cases h_last : k = t.seq.length
          · subst h_last
            constructor
            · change (t.seq ++ [v'])[t.seq.length] ∈
                  G.blockUnion (G.blocksSeq t.S (t.seq ++ [v']) t.seq.length)
              rw [List.getElem_append_right (le_refl _)]
              simp only [Nat.sub_self, List.getElem_cons_zero]
              rw [PartitionedGraph.blocksSeq_append G t.S t.seq v' t.seq.length (le_refl _)]
              exact hv'_mem
            constructor
            · change Disjoint (G.graph.neighborSet (t.seq ++ [v'])[t.seq.length])
                  (G.vertexSeq t.S t.C (t.seq ++ [v']) t.seq.length)
              rw [List.getElem_append_right (le_refl _)]
              simp only [Nat.sub_self, List.getElem_cons_zero]
              rw [PartitionedGraph.vertexSeq_append G t.S t.C t.seq v' t.seq.length (le_refl _)]
              exact hv'_disj
            · intro h_lt
              simp only [new_seq, List.length_append, List.length_singleton] at h_lt
              omega
          · have hk_lt : k < t.seq.length := by omega
            have h_aug_k := t.isAugmenting ⟨k, hk_lt⟩
            constructor
            · change (t.seq ++ [v'])[k] ∈ G.blockUnion (G.blocksSeq t.S (t.seq ++ [v']) k)
              rw [List.getElem_append_left hk_lt]
              rw [PartitionedGraph.blocksSeq_append G t.S t.seq v' k (le_of_lt hk_lt)]
              exact h_aug_k.1
            constructor
            · change Disjoint (G.graph.neighborSet (t.seq ++ [v'])[k])
                  (G.vertexSeq t.S t.C (t.seq ++ [v']) k)
              rw [List.getElem_append_left hk_lt]
              rw [PartitionedGraph.vertexSeq_append G t.S t.C t.seq v' k (le_of_lt hk_lt)]
              exact h_aug_k.2.1
            intro hk_lt_new
            change 0 < (G.graph.neighborSet (t.seq ++ [v'])[k] ∩ t.S).ncard
            rw [List.getElem_append_left hk_lt]
            by_cases h_case : k + 1 < t.seq.length
            · exact h_aug_k.2.2 h_case
            · have h_eq : k + 1 = t.seq.length := by
                simp only [new_seq, List.length_append, List.length_singleton] at hk_lt_new
                omega
              have h_pos := h_all_pos k hk_lt
              simp only [degreeAt, Nat.add_sub_cancel] at h_pos
              rw [List.getElem?_eq_getElem hk_lt] at h_pos
              exact h_pos
        let t' : G.FeasibleTuple := ⟨t.S, t.C, new_seq, t.isPartialIT, t.C_subset, h_aug_new⟩
        use t'
        refine ⟨h_C_empty, h_SX, ?_, ?_⟩
        · -- t'.seq[i] ∉ X for all i < t'.seq.length
          -- t'.seq = new_seq = t.seq ++ [v']
          intro i hi
          have hi' : i < new_seq.length := hi
          simp only [new_seq, List.length_append, List.length_singleton] at hi'
          by_cases h_last : i = t.seq.length
          · subst h_last
            change (t.seq ++ [v'])[t.seq.length] ∉ X
            simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
            exact hv'_not_X'
          · have hi_lt : i < t.seq.length := by omega
            change (t.seq ++ [v'])[i] ∉ X
            simp only [List.getElem_append_left hi_lt]
            exact h_seq_avoid i hi_lt
        · right; constructor; · rfl
          simp only [degSeqLt]
          left
          constructor
          · simp only [degreeSeq]; rw [List.mapIdx_append]; exact List.prefix_append _ _
          · simp only [degreeSeq, ne_eq]; rw [List.mapIdx_append]
            intro h_eq
            have h_len_eq : (List.mapIdx (fun _ v => (G.graph.neighborSet v ∩ t.S).ncard) t.seq ++
                List.mapIdx (fun _ v => (G.graph.neighborSet v ∩ t.S).ncard) [v']).length =
                (List.mapIdx (fun _ v => (G.graph.neighborSet v ∩ t.S).ncard) t.seq).length := by
              congr 1
            simp only [List.length_append, List.mapIdx_cons, List.length_singleton,
              List.mapIdx_nil] at h_len_eq
            omega
      · -- v ∉ X: use v directly
        let new_seq : List V := t.seq ++ [v]
        have h_aug_new : G.IsAugmenting t.S t.C new_seq := by
          intro ⟨k, hk⟩
          simp only [new_seq, List.length_append, List.length_singleton] at hk
          by_cases h_last : k = t.seq.length
          · subst h_last
            constructor
            · change (t.seq ++ [v])[t.seq.length] ∈
                  G.blockUnion (G.blocksSeq t.S (t.seq ++ [v]) t.seq.length)
              rw [List.getElem_append_right (le_refl _)]
              simp only [Nat.sub_self, List.getElem_cons_zero]
              rw [PartitionedGraph.blocksSeq_append G t.S t.seq v t.seq.length (le_refl _)]
              exact hv_mem
            constructor
            · change Disjoint (G.graph.neighborSet (t.seq ++ [v])[t.seq.length])
                  (G.vertexSeq t.S t.C (t.seq ++ [v]) t.seq.length)
              rw [List.getElem_append_right (le_refl _)]
              simp only [Nat.sub_self, List.getElem_cons_zero]
              rw [PartitionedGraph.vertexSeq_append G t.S t.C t.seq v t.seq.length (le_refl _)]
              exact hv_disj
            · intro h_lt
              simp only [new_seq, List.length_append, List.length_singleton] at h_lt
              omega
          · have hk_lt : k < t.seq.length := by omega
            have h_aug_k := t.isAugmenting ⟨k, hk_lt⟩
            constructor
            · change (t.seq ++ [v])[k] ∈ G.blockUnion (G.blocksSeq t.S (t.seq ++ [v]) k)
              rw [List.getElem_append_left hk_lt]
              rw [PartitionedGraph.blocksSeq_append G t.S t.seq v k (le_of_lt hk_lt)]
              exact h_aug_k.1
            constructor
            · change Disjoint (G.graph.neighborSet (t.seq ++ [v])[k])
                  (G.vertexSeq t.S t.C (t.seq ++ [v]) k)
              rw [List.getElem_append_left hk_lt]
              rw [PartitionedGraph.vertexSeq_append G t.S t.C t.seq v k (le_of_lt hk_lt)]
              exact h_aug_k.2.1
            intro hk_lt_new
            change 0 < (G.graph.neighborSet (t.seq ++ [v])[k] ∩ t.S).ncard
            rw [List.getElem_append_left hk_lt]
            by_cases h_case : k + 1 < t.seq.length
            · exact h_aug_k.2.2 h_case
            · have h_eq : k + 1 = t.seq.length := by
                simp only [new_seq, List.length_append, List.length_singleton] at hk_lt_new
                omega
              have h_pos := h_all_pos k hk_lt
              simp only [degreeAt, Nat.add_sub_cancel] at h_pos
              rw [List.getElem?_eq_getElem hk_lt] at h_pos
              exact h_pos
        let t' : G.FeasibleTuple := ⟨t.S, t.C, new_seq, t.isPartialIT, t.C_subset, h_aug_new⟩
        use t'
        refine ⟨h_C_empty, h_SX, ?_, ?_⟩
        · -- t'.seq[i] ∉ X for all i < t'.seq.length
          -- t'.seq = new_seq = t.seq ++ [v]
          intro i hi
          have hi' : i < new_seq.length := hi
          simp only [new_seq, List.length_append, List.length_singleton] at hi'
          by_cases h_last : i = t.seq.length
          · subst h_last
            change (t.seq ++ [v])[t.seq.length] ∉ X
            simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
            exact hv_X
          · have hi_lt : i < t.seq.length := by omega
            change (t.seq ++ [v])[i] ∉ X
            simp only [List.getElem_append_left hi_lt]
            exact h_seq_avoid i hi_lt
        · right; constructor; · rfl
          simp only [degSeqLt]
          left
          constructor
          · simp only [degreeSeq]; rw [List.mapIdx_append]; exact List.prefix_append _ _
          · simp only [degreeSeq, ne_eq]; rw [List.mapIdx_append]
            intro h_eq
            have h_len_eq : (List.mapIdx (fun _ v => (G.graph.neighborSet v ∩ t.S).ncard) t.seq ++
                List.mapIdx (fun _ v => (G.graph.neighborSet v ∩ t.S).ncard) [v]).length =
                (List.mapIdx (fun _ v => (G.graph.neighborSet v ∩ t.S).ncard) t.seq).length := by
              congr 1
            simp only [List.length_append, List.mapIdx_cons, List.length_singleton,
              List.mapIdx_nil] at h_len_eq
            omega

end Haxell

end IndependentTransversals
