import GraphTransfer

namespace Erdos60.Transfer
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Choose an actual spanning subgraph with exactly the prescribed edge count. -/
theorem exists_spanning_edge_count (G : SimpleGraph V) (n : ℕ)
    (hn : n ≤ G.edgeFinset.card) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.edgeFinset.card = n := by
  classical
  obtain ⟨E,hE,hcard⟩ := Finset.exists_subset_card_eq hn
  let H := SimpleGraph.fromEdgeSet (E : Set (Sym2 V))
  have hHG : H ≤ G := by
    intro a b hab
    have hmem : s(a,b) ∈ E := hab.1
    simpa using hE hmem
  have hHE : H.edgeFinset = E := by
    ext e
    induction e using Sym2.inductionOn with
    | hf a b =>
      simp only [SimpleGraph.mem_edgeFinset, H]
      constructor
      · exact And.left
      · intro he
        have hab : G.Adj a b := by simpa using hE he
        exact ⟨he,hab.ne⟩
  refine ⟨H,hHG,?_⟩
  convert (congrArg Finset.card hHE).trans hcard using 1
  congr 1
  ext e
  simp

/-- The first-excess host lives on the same vertices and loses exactly t-1 edges. -/
theorem first_excess_subgraph (G : SimpleGraph V) (M t : ℕ)
    (ht : 1 ≤ t) (he : G.edgeFinset.card = M+t) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.edgeFinset.card = M+1 ∧
      (G.edgeFinset \ H.edgeFinset).card = t-1 ∧
      Counting.cycleCount H ≤ Counting.cycleCount G := by
  classical
  obtain ⟨H,hHG,hH⟩ := exists_spanning_edge_count G (M+1) (by omega)
  refine ⟨H,hHG,hH,?_,Counting.cycleCount_mono hHG⟩
  rw [Finset.card_sdiff_of_subset (SimpleGraph.edgeFinset_mono hHG), he,hH]
  omega

/-- Passing from the first-excess subgraph to the host spends at most t-1 additions. -/
theorem lift_added_edge_count (G H Q : SimpleGraph V) (M t : ℕ)
    (hHG : H ≤ G) (hG : G.edgeFinset.card = M+t)
    (hH : H.edgeFinset.card = M+1) :
    (G.edgeFinset \ Q.edgeFinset).card ≤
      (H.edgeFinset \ Q.edgeFinset).card + (t-1) := by
  classical
  have hsub : G.edgeFinset \ Q.edgeFinset ⊆
      (H.edgeFinset \ Q.edgeFinset) ∪ (G.edgeFinset \ H.edgeFinset) := by
    intro e he
    simp only [Finset.mem_sdiff,Finset.mem_union] at *
    by_cases hh : e ∈ H.edgeFinset
    · exact Or.inl ⟨hh,he.2⟩
    · exact Or.inr ⟨he.1,hh⟩
  have hc := (Finset.card_le_card hsub).trans
    (Finset.card_union_le (H.edgeFinset \ Q.edgeFinset) (G.edgeFinset \ H.edgeFinset))
  rw [Finset.card_sdiff_of_subset (SimpleGraph.edgeFinset_mono hHG), hG,hH] at hc
  have ha : M+t-(M+1) = t-1 := by omega
  simpa [ha] using hc

end Erdos60.Transfer
