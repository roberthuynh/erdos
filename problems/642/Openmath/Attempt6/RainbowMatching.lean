  
                                                   
                                                                         
                                                              
                                                                           
                                                                               
  
import Openmath.Attempt6.IndependentTransversals.Haxell
import Mathlib

namespace IndependentTransversals
variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : PartitionedGraph V) [DecidableRel G.graph.Adj]

omit [DecidableRel G.graph.Adj] in
theorem PartitionedGraph.transversal_of_extension
    (hext : ∀ t : G.FeasibleTuple,
      (∀ i, i < t.seq.length → 0 < G.degreeAt t.S t.seq (i + 1)) →
      (G.uncoveredBlocks t.S).Nonempty → t.C = ∅ →
      ∃ v ∈ G.blockUnion (G.blocksSeq t.S t.seq t.seq.length),
        Disjoint (G.graph.neighborSet v) (G.vertexSeq t.S t.C t.seq t.seq.length)) :
    ∃ S, G.IsIndependentTransversal S := by
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
    have h_can_extend := hext t
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
      have h_can_extend := hext t h_all_pos h_not_full h_C_empty
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

                                                                                
                                                                           
                                                  
theorem PartitionedGraph.transversal_of_avoidance
    (havoid : ∀ R : Set (Set V), R ⊆ G.blocks → R.Nonempty →
      ∀ D : Set V, D.ncard ≤ 2 * (R.ncard - 1) →
      ∃ v ∈ G.blockUnion R, Disjoint (G.graph.neighborSet v) D) :
    ∃ S, G.IsIndependentTransversal S := by
  apply G.transversal_of_extension
  intro t h_all_pos h_not_full h_C_empty
  let m := t.seq.length
  let B_m := G.blocksSeq t.S t.seq m
  let C_m := G.vertexSeq t.S t.C t.seq m
  let deg_sum := ((G.degreeSeq t.S t.seq).take m).sum
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

  have h_Bm_eq : B_m.ncard = (G.uncoveredBlocks t.S).ncard + deg_sum :=
    G.blocksSeq_card_eq t.S t.C t.seq t.isPartialIT t.isAugmenting m (le_refl m)
  have h_Cm_bound := G.vertexSeq_card_bound t m (le_refl m)
  have h_C_ncard : t.C.ncard = 0 := by simp only [h_C_empty, Set.ncard_empty]
  have h_uncovered_pos : 0 < (G.uncoveredBlocks t.S).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 h_not_full
  have h_Bm_nonempty : B_m.Nonempty :=
    Set.Nonempty.mono (G.uncoveredBlocks_subset_blocksSeq t.S t.seq m (le_refl m)) h_not_full
  have hsize : C_m.ncard ≤ 2 * (B_m.ncard - 1) := by
    change C_m.ncard ≤ t.C.ncard + m + deg_sum at h_Cm_bound
    omega
  exact havoid B_m (G.blocksSeq_subset t.S t.seq m) h_Bm_nonempty C_m hsize

end IndependentTransversals

namespace Erdos585.Attempt6.RainbowMatching

open IndependentTransversals

variable {I X : Type*} [Fintype I] [DecidableEq I] [DecidableEq X]

abbrev TaggedEdge (H : I → Finset (Finset X)) := Σ i, {e // e ∈ H i}

def taggedSet {H : I → Finset (Finset X)} (v : TaggedEdge H) : Finset X := v.2.val

def conflictGraph (H : I → Finset (Finset X)) : SimpleGraph (TaggedEdge H) where
  Adj v w := v ≠ w ∧ ¬ Disjoint (taggedSet v) (taggedSet w)
  symm := ⟨fun _v _w h => ⟨Ne.symm h.1, fun hd => h.2 hd.symm⟩⟩
  loopless := ⟨fun _v h => h.1 rfl⟩

def colorBlock (H : I → Finset (Finset X)) (i : I) : Set (TaggedEdge H) :=
  {v | v.1 = i}

omit [Fintype I] [DecidableEq I] [DecidableEq X] in
theorem colorBlock_injective (H : I → Finset (Finset X))
    (hne : ∀ i, (H i).Nonempty) : Function.Injective (colorBlock H) := by
  intro i j hij
  obtain ⟨e, he⟩ := hne i
  have hv : (⟨i, ⟨e, he⟩⟩ : TaggedEdge H) ∈ colorBlock H j := by
    rw [← hij]
    rfl
  exact hv

def partitionedConflict (H : I → Finset (Finset X))
    (hne : ∀ i, (H i).Nonempty) : PartitionedGraph (TaggedEdge H) where
  graph := conflictGraph H
  blocks := Set.range (colorBlock H)
  isPartition := by
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨e, he⟩ := hne i
      have hv : (⟨i, ⟨e, he⟩⟩ : TaggedEdge H) ∈ colorBlock H i := rfl
      rw [hi] at hv
      exact hv
    · intro v
      refine ⟨colorBlock H v.1, ⟨⟨v.1, rfl⟩, rfl⟩, ?_⟩
      rintro B ⟨⟨i, rfl⟩, hi⟩
      change v.1 = i at hi
      rw [hi]

theorem matching_avoids_small_set (M : Finset (Finset X))
    (hM : (M : Set (Finset X)).Pairwise (fun e f => Disjoint e f)) (B : Finset X)
    (hsmall : B.card < M.card) : ∃ e ∈ M, Disjoint e B := by
  classical
  by_contra hn
  have hhit : ∀ e : M, ∃ x, x ∈ e.val ∧ x ∈ B := by
    intro e
    have hd : ¬ Disjoint e.val B := fun hd => hn ⟨e.val, e.prop, hd⟩
    exact Finset.not_disjoint_iff.mp hd
  choose f hf using hhit
  let g : M → B := fun e => ⟨f e, (hf e).2⟩
  have hginj : Function.Injective g := by
    intro e q heq
    by_contra hne
    have hed : e.val ≠ q.val := fun h => hne (Subtype.ext h)
    have hdis := hM e.prop q.prop hed
    have hx : f e = f q := congrArg Subtype.val heq
    exact Finset.disjoint_left.mp hdis (hf e).1 (by rw [hx]; exact (hf q).1)
  have hc := Fintype.card_le_of_injective g hginj
  have hcard : M.card ≤ B.card := by simpa using hc
  omega

/-- A finite rank-r family with more than 2r(|J|-1) disjoint edges in each
nonempty color union has an actual rainbow matching. No transversal or
dominating-set conclusion is assumed. -/
theorem rainbow_matching_of_union_matching (H : I → Finset (Finset X)) (r : ℕ)
    (hrank : ∀ i e, e ∈ H i → e.card ≤ r)
    (hmatch : ∀ J : Finset I, J.Nonempty →
      ∃ M : Finset (Finset X),
        (∀ e ∈ M, ∃ i ∈ J, e ∈ H i) ∧
        (M : Set (Finset X)).Pairwise (fun e f => Disjoint e f) ∧
        2 * r * (J.card - 1) < M.card) :
    ∃ f : I → Finset X, (∀ i, f i ∈ H i) ∧
      Pairwise (fun i j => Disjoint (f i) (f j)) := by
  classical
  have hne : ∀ i, (H i).Nonempty := by
    intro i
    obtain ⟨M, hmem, _, hcard⟩ := hmatch {i} (Finset.singleton_nonempty i)
    have hpos : 0 < M.card := by simpa using hcard
    obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
    obtain ⟨j, hj, hej⟩ := hmem e he
    have hji : j = i := Finset.mem_singleton.mp hj
    exact ⟨e, hji ▸ hej⟩
  let G := partitionedConflict H hne
  have havoid : ∀ R : Set (Set (TaggedEdge H)), R ⊆ G.blocks → R.Nonempty →
      ∀ D : Set (TaggedEdge H), D.ncard ≤ 2 * (R.ncard - 1) →
      ∃ v ∈ G.blockUnion R, Disjoint (G.graph.neighborSet v) D := by
    intro R hRG hR D hD
    let J : Finset I := Finset.univ.filter (fun i => colorBlock H i ∈ R)
    have hJ : ∀ i, i ∈ J ↔ colorBlock H i ∈ R := by
      intro i
      simp [J]
    have hJne : J.Nonempty := by
      obtain ⟨B, hB⟩ := hR
      obtain ⟨i, rfl⟩ := hRG hB
      exact ⟨i, (hJ i).mpr hB⟩
    have himage : colorBlock H '' (J : Set I) = R := by
      ext B
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact (hJ i).mp hi
      · intro hB
        obtain ⟨i, rfl⟩ := hRG hB
        exact ⟨i, (hJ i).mpr hB, rfl⟩
    have hJcard : J.card = R.ncard := by
      rw [← himage, Set.ncard_image_of_injective _ (colorBlock_injective H hne)]
      simp
    let B := D.toFinset.biUnion taggedSet
    have hB : B.card ≤ D.ncard * r := by
      have hh := Finset.card_biUnion_le_card_mul D.toFinset taggedSet r
        (fun v hv => hrank v.1 v.2.val v.2.prop)
      simpa only [B, Set.toFinset_card, Set.fintypeCard_eq_ncard] using hh
    obtain ⟨M, hMmem, hMdis, hMcard⟩ := hmatch J hJne
    have hsmall : B.card < M.card := by
      have hd := Nat.mul_le_mul_right r hD
      rw [← hJcard] at hd
      have hbound : B.card ≤ 2 * r * (J.card - 1) := by nlinarith
      exact hbound.trans_lt hMcard
    obtain ⟨e, heM, heB⟩ := matching_avoids_small_set M hMdis B hsmall
    obtain ⟨i, hiJ, hei⟩ := hMmem e heM
    let v : TaggedEdge H := ⟨i, ⟨e, hei⟩⟩
    have hvR : v ∈ G.blockUnion R := by
      exact Set.mem_sUnion.mpr ⟨colorBlock H i,
        ⟨(hJ i).mp hiJ, ⟨i, rfl⟩⟩, rfl⟩
    refine ⟨v, hvR, ?_⟩
    rw [Set.disjoint_left]
    intro w hwadj hwD
    have hdis : Disjoint (taggedSet v) (taggedSet w) := by
      apply Finset.disjoint_left.mpr
      intro x hxv hxw
      have hxB : x ∈ B := Finset.mem_biUnion.mpr
        ⟨w, by simpa using hwD, hxw⟩
      exact Finset.disjoint_left.mp heB hxv hxB
    exact hwadj.2 hdis
  obtain ⟨S, hS⟩ := G.transversal_of_avoidance havoid
  have hchoose : ∀ i, ∃ v, v ∈ S ∧ v ∈ colorBlock H i := by
    intro i
    obtain ⟨v, hv, _⟩ := hS.2 (colorBlock H i) ⟨i, rfl⟩
    exact ⟨v, hv⟩
  choose v hv using hchoose
  refine ⟨fun i => taggedSet (v i), ?_, ?_⟩
  · intro i
    have hcolor : (v i).1 = i := (hv i).2
    simpa only [taggedSet, hcolor] using (v i).2.prop
  · intro i j hij
    have hvne : v i ≠ v j := by
      intro heq
      have hh := congrArg Sigma.fst heq
      change (v i).1 = (v j).1 at hh
      exact hij ((hv i).2.symm.trans (hh.trans (hv j).2))
    by_contra hd
    exact hS.1 (hv i).1 (hv j).1 hvne ⟨hvne, hd⟩

end Erdos585.Attempt6.RainbowMatching
