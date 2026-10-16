import MatchingEquality

/-! Actual cycle partition for adding a matching on an independent set.
Geometry and exact per-edge path counts remain explicit separate interfaces. -/
namespace Erdos60.Counting
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In a union C4, at most one edge belongs to an added matching supported on
an independent set of the base graph. This includes non-induced C4s. -/
theorem matching_cycle_at_most_one (Q K : SimpleGraph V) (S : Set V)
    (hm : IsMatchingGraph K)
    (hsupport : ∀ a b, K.Adj a b → a ∈ S ∧ b ∈ S)
    (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ Q.Adj a b)
    (C : Finset (Sym2 V)) (hC : C ∈ cycles (Q ⊔ K)) :
    (C ∩ K.edgeFinset).card ≤ 1 := by
  obtain ⟨hsub,a,b,c,d,hd,rfl⟩ := (mem_cycles _ _).mp hC
  have hne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    simpa only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_or, not_false_eq_true, and_true, and_assoc] using hd
  have hab : (Q ⊔ K).Adj a b := by
    have := hsub (by simp [fourEdges] : s(a,b) ∈ fourEdges a b c d)
    simpa using this
  have hbc : (Q ⊔ K).Adj b c := by
    have := hsub (by simp [fourEdges] : s(b,c) ∈ fourEdges a b c d)
    simpa using this
  have hcd : (Q ⊔ K).Adj c d := by
    have := hsub (by simp [fourEdges] : s(c,d) ∈ fourEdges a b c d)
    simpa using this
  have hda : (Q ⊔ K).Adj d a := by
    have := hsub (by simp [fourEdges] : s(d,a) ∈ fourEdges a b c d)
    simpa using this
  have h01 : ¬ (K.Adj a b ∧ K.Adj b c) := by
    rintro ⟨h1,h2⟩
    exact hne.2.1 (hm b a c h1.symm h2)
  have h12 : ¬ (K.Adj b c ∧ K.Adj c d) := by
    rintro ⟨h1,h2⟩
    exact hne.2.2.2.2.1 (hm c b d h1.symm h2)
  have h23 : ¬ (K.Adj c d ∧ K.Adj d a) := by
    rintro ⟨h1,h2⟩
    exact hne.2.1 ((hm d c a h1.symm h2).symm)
  have h30 : ¬ (K.Adj d a ∧ K.Adj a b) := by
    rintro ⟨h1,h2⟩
    exact hne.2.2.2.2.1 ((hm a d b h1.symm h2).symm)
  have h02 : ¬ (K.Adj a b ∧ K.Adj c d) := by
    rintro ⟨h1,h2⟩
    exact no_opposite_matching_added Q K S hm hsupport hind a b c d
      hne.2.2.2.2.1 h1 h2 hbc
  have h13 : ¬ (K.Adj b c ∧ K.Adj d a) := by
    rintro ⟨h1,h2⟩
    exact no_opposite_matching_added Q K S hm hsupport hind b c d a
      (Ne.symm hne.2.1) h1 h2 hcd
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨he,hKe⟩ := Finset.mem_inter.mp he
  obtain ⟨hf,hKf⟩ := Finset.mem_inter.mp hf
  simp only [fourEdges, mem_insert, mem_singleton] at he hf
  simp only [SimpleGraph.mem_edgeFinset] at hKe hKf
  clear hm hsupport hind hC hsub hd hab hbc hcd hda hne
  rcases he with rfl | rfl | rfl | rfl <;>
    rcases hf with rfl | rfl | rfl | rfl <;>
    simp only [SimpleGraph.mem_edgeSet] at hKe hKf <;>
    first
    | rfl
    | exact False.elim (h01 ⟨hKe,hKf⟩)
    | exact False.elim (h01 ⟨hKf,hKe⟩)
    | exact False.elim (h12 ⟨hKe,hKf⟩)
    | exact False.elim (h12 ⟨hKf,hKe⟩)
    | exact False.elim (h23 ⟨hKe,hKf⟩)
    | exact False.elim (h23 ⟨hKf,hKe⟩)
    | exact False.elim (h30 ⟨hKe,hKf⟩)
    | exact False.elim (h30 ⟨hKf,hKe⟩)
    | exact False.elim (h02 ⟨hKe,hKf⟩)
    | exact False.elim (h02 ⟨hKf,hKe⟩)
    | exact False.elim (h13 ⟨hKe,hKf⟩)
    | exact False.elim (h13 ⟨hKf,hKe⟩)

/-- If the base has no ordinary C4, the unique-added-edge partition is exact. -/
theorem matching_cycle_exactly_one (Q K : SimpleGraph V) (S : Set V)
    (hfree : cycles Q = ∅)
    (hm : IsMatchingGraph K)
    (hsupport : ∀ a b, K.Adj a b → a ∈ S ∧ b ∈ S)
    (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ Q.Adj a b)
    (C : Finset (Sym2 V)) (hC : C ∈ cycles (Q ⊔ K)) :
    (C ∩ K.edgeFinset).card = 1 := by
  have hle := matching_cycle_at_most_one Q K S hm hsupport hind C hC
  have hnon : (C ∩ K.edgeFinset).Nonempty := by
    by_contra hn
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
    have hbase : C ∈ cycles Q := by
      obtain ⟨hsub,hshape⟩ := (mem_cycles _ _).mp hC
      apply (mem_cycles Q C).mpr
      refine ⟨?_,hshape⟩
      intro e he
      have hG := hsub he
      have hnot : e ∉ K.edgeFinset := by
        intro hk
        have : e ∈ C ∩ K.edgeFinset := Finset.mem_inter.mpr ⟨he,hk⟩
        simp [hempty] at this
      simp only [SimpleGraph.mem_edgeFinset] at hG hnot ⊢
      rw [SimpleGraph.edgeSet_sup, Set.mem_union] at hG
      exact hG.resolve_right hnot
    simp [hfree] at hbase
  have hpos := Finset.card_pos.mpr hnon
  omega

/-- Actual cycles containing a specified marked added edge. -/
noncomputable def markedCycles (G : SimpleGraph V) (e : Sym2 V) :
    Finset (Finset (Sym2 V)) := (cycles G).filter fun C => e ∈ C

/-- Exact count partition by the unique actual added edge. No path-family
completeness or cardinality is hidden in this theorem. -/
theorem matching_cycle_partition_count (Q K : SimpleGraph V) (S : Set V)
    (hfree : cycles Q = ∅)
    (hm : IsMatchingGraph K)
    (hsupport : ∀ a b, K.Adj a b → a ∈ S ∧ b ∈ S)
    (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ Q.Adj a b) :
    cycleCount (Q ⊔ K) = ∑ e ∈ K.edgeFinset, (markedCycles (Q ⊔ K) e).card := by
  classical
  have hunion : K.edgeFinset.biUnion (markedCycles (Q ⊔ K)) = cycles (Q ⊔ K) := by
    ext C
    constructor
    · intro h
      obtain ⟨e,he,hC⟩ := Finset.mem_biUnion.mp h
      exact (Finset.mem_filter.mp hC).1
    · intro hC
      have hone := matching_cycle_exactly_one Q K S hfree hm hsupport hind C hC
      have hpos : (C ∩ K.edgeFinset).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨e,he⟩ := hpos
      exact Finset.mem_biUnion.mpr ⟨e,(Finset.mem_inter.mp he).2,
        Finset.mem_filter.mpr ⟨hC,(Finset.mem_inter.mp he).1⟩⟩
  have hdis : ∀ e ∈ K.edgeFinset, ∀ f ∈ K.edgeFinset, e ≠ f →
      Disjoint (markedCycles (Q ⊔ K) e) (markedCycles (Q ⊔ K) f) := by
    intro e he f hf hne
    apply Finset.disjoint_left.mpr
    intro C hCe hCf
    obtain ⟨hC,heC⟩ := Finset.mem_filter.mp hCe
    have hfC := (Finset.mem_filter.mp hCf).2
    have hle := matching_cycle_at_most_one Q K S hm hsupport hind C hC
    exact hne (Finset.card_le_one.mp hle e (Finset.mem_inter.mpr ⟨heC,he⟩)
      f (Finset.mem_inter.mpr ⟨hfC,hf⟩))
  change (cycles (Q ⊔ K)).card = _
  rw [← hunion]
  exact Finset.card_biUnion hdis

end Erdos60.Counting
