import C4Counting

/-! Combinatorial equality helpers for #60, under explicit geometry interfaces.
No projective-plane or polarity existence theorem is asserted here. -/
namespace Erdos60.Counting
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph-theoretic matching interface: every vertex has at most one neighbor. -/
def IsMatchingGraph (K : SimpleGraph V) : Prop :=
  ∀ a b c, K.Adj a b → K.Adj a c → b = c

omit [Fintype V] [DecidableEq V] in
/-- Two adjacent added matching edges cannot occur on four distinct vertices. -/
theorem no_adjacent_matching_added (K : SimpleGraph V) (hm : IsMatchingGraph K)
    (a b c : V) (hne : b ≠ c) : ¬ (K.Adj a b ∧ K.Adj a c) := by
  rintro ⟨hab,hac⟩
  exact hne (hm a b c hab hac)

omit [Fintype V] [DecidableEq V] in
/-- Two opposite matching edges supported on an independent base set cannot
lie on a C4 of the union: even its connecting edge is impossible. -/
theorem no_opposite_matching_added (Q K : SimpleGraph V) (S : Set V)
    (hm : IsMatchingGraph K)
    (hsupport : ∀ a b, K.Adj a b → a ∈ S ∧ b ∈ S)
    (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ Q.Adj a b)
    (a b c d : V) (hbd : b ≠ d)
    (hab : K.Adj a b) (hcd : K.Adj c d) :
    ¬ ((Q ⊔ K).Adj b c) := by
  intro hbc
  change Q.Adj b c ∨ K.Adj b c at hbc
  rcases hbc with hbc | hbc
  · exact hind b (hsupport a b hab).2 c (hsupport c d hcd).1 hbc
  · exact hbd (hm c b d hbc.symm hcd)

/-- Distinct added edges sharing a vertex, and a common base neighbor of their
other endpoints, create an actual extra C4 carrying both added edges. -/
theorem nucleus_extra_cycle (G Q : SimpleGraph V) (a b c w : V)
    (hd : [b,a,c,w].Nodup)
    (hab : s(a,b) ∈ G.edgeFinset) (hac : s(a,c) ∈ G.edgeFinset)
    (hcw : s(c,w) ∈ G.edgeFinset) (hwb : s(w,b) ∈ G.edgeFinset)
    (habQ : s(a,b) ∉ Q.edgeFinset) (hacQ : s(a,c) ∉ Q.edgeFinset) :
    fourEdges b a c w ∈ cycles G ∧
    2 ≤ (fourEdges b a c w \ Q.edgeFinset).card := by
  have hba : s(b,a) = s(a,b) := Sym2.eq_swap
  constructor
  · apply (mem_cycles G _).mpr
    constructor
    · intro e he
      simp only [fourEdges, mem_insert, mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl
      · simpa only [hba] using hab
      · exact hac
      · exact hcw
      · exact hwb
    · exact ⟨b,a,c,w,hd,rfl⟩
  · have hne : s(a,b) ≠ s(a,c) := by
      have hbc : b ≠ c := by
        have hb := (List.nodup_cons.mp hd).1
        intro h
        apply hb
        simp [h]
      intro he
      simp only [Sym2.eq_iff] at he
      rcases he with h | h
      · exact hbc h.2
      · exact hbc (h.2.trans h.1)
    have hs : ({s(a,b),s(a,c)} : Finset (Sym2 V)) ⊆
        fourEdges b a c w \ Q.edgeFinset := by
      intro e he
      simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl
      · exact mem_sdiff.mpr ⟨by simp [fourEdges, ← hba],habQ⟩
      · exact mem_sdiff.mpr ⟨by simp [fourEdges],hacQ⟩
    have hh := Finset.card_le_card hs
    simpa [hne] using hh

/-- Any actual cycle with two non-base edges is outside every family of cycles
having exactly one non-base edge, so it increases the count by at least one. -/
theorem extra_cycle_strict_count (G Q : SimpleGraph V)
    (F : Finset (Finset (Sym2 V))) (C : Finset (Sym2 V))
    (hF : F ⊆ cycles G)
    (hOne : ∀ D ∈ F, (D \ Q.edgeFinset).card = 1)
    (hC : C ∈ cycles G) (hTwo : 2 ≤ (C \ Q.edgeFinset).card) :
    F.card + 1 ≤ cycleCount G := by
  have hn : C ∉ F := by
    intro h
    have := hOne C h
    omega
  have hs : insert C F ⊆ cycles G := Finset.insert_subset hC hF
  have := Finset.card_le_card hs
  simpa [cycleCount, hn] using this

/-- The nucleus obstruction strictly exceeds any already counted one-added-edge
family. This is the actual-cycle contradiction used by the forward equality
argument, with adjacency and distinctness supplied explicitly. -/
theorem shared_added_edges_strict_count (G Q : SimpleGraph V)
    (F : Finset (Finset (Sym2 V)))
    (hF : F ⊆ cycles G)
    (hOne : ∀ D ∈ F, (D \ Q.edgeFinset).card = 1)
    (a b c w : V) (hd : [b,a,c,w].Nodup)
    (hab : s(a,b) ∈ G.edgeFinset) (hac : s(a,c) ∈ G.edgeFinset)
    (hcw : s(c,w) ∈ G.edgeFinset) (hwb : s(w,b) ∈ G.edgeFinset)
    (habQ : s(a,b) ∉ Q.edgeFinset) (hacQ : s(a,c) ∉ Q.edgeFinset) :
    F.card + 1 ≤ cycleCount G := by
  obtain ⟨hC,hTwo⟩ := nucleus_extra_cycle G Q a b c w hd hab hac hcw hwb habQ hacQ
  exact extra_cycle_strict_count G Q F (fourEdges b a c w) hF hOne hC hTwo

end Erdos60.Counting
