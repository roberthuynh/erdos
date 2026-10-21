import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralHost
import Openmath.Erdos642.Proofs.CloudT9_20261021.PendantCycle

                                                                                        
                                                                                             
                                                
namespace Erdos642.CloudT9_20261021.PendantRich

open SimpleGraph Erdos642.CampaignFe72210b

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V)

/-- Chords of a walk of a subgraph are chords of the same walk in the supergraph. -/
theorem chordEdges_subset_mapLe {H : SimpleGraph V} (hle : H ≤ G) {u : V} (c : H.Walk u u) :
    chordEdges c ⊆ chordEdges (c.mapLe hle) := by
  classical
  intro e he
  simp only [chordEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [Walk.isChord_sym2Mk] at he ⊢
    rw [Walk.edges_mapLe_eq_edges, Walk.support_mapLe_eq_support]
    exact ⟨hle he.1, he.2.1, he.2.2.1, he.2.2.2⟩

                                                                  
theorem hasRichCycle_of_le {H : SimpleGraph V} (hle : H ≤ G) (h : HasRichCycle H) :
    HasRichCycle G := by
  obtain ⟨v, c, hc, hcard⟩ := h
  refine ⟨v, c.mapLe hle, Walk.IsCycle.mapLe hle hc, ?_⟩
  rw [Walk.length_mapLe]
  exact hcard.trans (Finset.card_le_card (chordEdges_subset_mapLe G hle c))

omit [Fintype V] in
/-- A walk avoiding `x` uses no edge incident to `x`. -/
theorem edges_subset_deleteIncidenceSet {u x : V} (c : G.Walk u u) (hx : x ∉ c.support) :
    ∀ e ∈ c.edges, e ∈ (G.deleteIncidenceSet x).edgeSet := by
  intro e he
  rw [deleteIncidenceSet, edgeSet_deleteEdges, Set.mem_sdiff]
  refine ⟨c.edges_subset_edgeSet he, ?_⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [mk'_mem_incidenceSet_iff]
    rintro ⟨-, rfl | rfl⟩
    · exact hx (c.fst_mem_support_of_mem_edges he)
    · exact hx (c.snd_mem_support_of_mem_edges he)

/-- Chords of a cycle avoiding `x` survive the deletion of the edges at `x`. -/
theorem chordEdges_subset_transfer {u x : V} (c : G.Walk u u) (hx : x ∉ c.support)
    (hsub : ∀ e ∈ c.edges, e ∈ (G.deleteIncidenceSet x).edgeSet) :
    chordEdges c ⊆ chordEdges (c.transfer (G.deleteIncidenceSet x) hsub) := by
  classical
  intro e he
  simp only [chordEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [Walk.isChord_sym2Mk] at he ⊢
    rw [Walk.edges_transfer, Walk.support_transfer]
    refine ⟨?_, he.2.1, he.2.2.1, he.2.2.2⟩
    rw [deleteIncidenceSet_adj]
    refine ⟨he.1, ?_, ?_⟩
    · rintro rfl; exact hx he.2.2.1
    · rintro rfl; exact hx he.2.2.2

/-- Deleting the edges at a vertex of degree ≤ 1 keeps every rich cycle. -/
theorem hasRichCycle_deleteIncidenceSet_of_degree_le_one [DecidableRel G.Adj] {x : V}
    (hx : G.degree x ≤ 1) (h : HasRichCycle G) : HasRichCycle (G.deleteIncidenceSet x) := by
  obtain ⟨v, c, hc, hcard⟩ := h
  have hxs : x ∉ c.support := PendantCycle.notMem_cycle_support_of_degree_le_one G c hc hx
  have hsub := edges_subset_deleteIncidenceSet G c hxs
  refine ⟨v, c.transfer _ hsub, hc.transfer hsub, ?_⟩
  rw [Walk.length_transfer]
  exact hcard.trans (Finset.card_le_card (chordEdges_subset_transfer G c hxs hsub))

                                                                                
theorem hasRichCycle_deleteIncidenceSet_iff [DecidableRel G.Adj] {x : V} (hx : G.degree x ≤ 1) :
    HasRichCycle (G.deleteIncidenceSet x) ↔ HasRichCycle G :=
  ⟨hasRichCycle_of_le G (deleteEdges_le _), hasRichCycle_deleteIncidenceSet_of_degree_le_one G hx⟩

end Erdos642.CloudT9_20261021.PendantRich
