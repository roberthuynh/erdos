import Openmath.Erdos642.Proofs.CampaignFe72210b.FinitePruning
import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralHost

/-! Original induced edges on a covered mask pay the full ambient cycle length. -/
namespace Erdos642.DenseMask20261019.GraphPayment

open SimpleGraph Erdos642.CampaignFe72210b

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The mask edges are literal original edges on the actual cycle support. -/
theorem mask_edges_subset_support {v : V} (c : G.Walk v v) (Q : Finset V)
    (hQ : ∀ x ∈ Q, x ∈ c.support) :
    (mask G Q).edgeFinset ⊆ supportEdges c := by
  classical
  intro e he
  induction e using Sym2.inductionOn with
  | _ a b =>
    have he' : s(a, b) ∈ (mask G Q).edgeSet :=
      (SimpleGraph.mem_edgeFinset (G := mask G Q)).mp he
    have hab : G.Adj a b ∧ a ∈ Q ∧ b ∈ Q := he'
    exact (mem_supportEdges c a b).mpr ⟨hab.1, hQ a hab.2.1, hQ b hab.2.2⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A simple cycle cannot use more vertices than the ambient finite graph. -/
theorem cycle_length_le_order {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    c.length ≤ Fintype.card V := by
  have h := hc.nodup_dropLast_support.length_le_card
  simpa only [List.length_dropLast, Walk.length_support, Nat.add_sub_cancel] using h

/-- Every edge credited comes from the original graph; only actual cycle edges are removed. -/
theorem rich_of_cycle_covers_dense_mask {v : V} (c : G.Walk v v) (hc : c.IsCycle)
    (Q : Finset V) (hQ : ∀ x ∈ Q, x ∈ c.support)
    (hdense : 2 * Fintype.card V ≤ inducedEdges G Q) :
    HasRichCycle G := by
  classical
  refine ⟨v, c, hc, many_chords_of_support_edges c hc ?_⟩
  have hs := Finset.card_le_card (mask_edges_subset_support G c Q hQ)
  change inducedEdges G Q ≤ (supportEdges c).card at hs
  exact (Nat.mul_le_mul_left 2 (cycle_length_le_order G c hc)).trans (hdense.trans hs)

end Erdos642.DenseMask20261019.GraphPayment
