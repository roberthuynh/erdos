import Openmath.Erdos642.Proofs.CampaignFe72210b.IntervalCycle
import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralHost

namespace Erdos642.CampaignFe72210b
open SimpleGraph
variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} {u v w : V}

/-- Literal host edges supported on retained indices belong to the cycle's induced edges. -/
theorem supported_edges_subset (p : G.Walk u v) (c : G.Walk w w)
    (i j : ℕ) (F : Finset (Sym2 V))
    (hF : ∀ a b, s(a,b) ∈ F → G.Adj a b ∧
      (∃ k, i ≤ k ∧ k ≤ j ∧ p.getVert k = a) ∧
      (∃ k, i ≤ k ∧ k ≤ j ∧ p.getVert k = b))
    (hret : ∀ k, i ≤ k → k ≤ j → p.getVert k ∈ c.support) :
    F ⊆ supportEdges c := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf a b =>
    obtain ⟨hab, ⟨ka, hia, haj, ha⟩, ⟨kb, hib, hbj, hb⟩⟩ := hF a b he
    apply (mem_supportEdges c a b).mpr
    exact ⟨hab, ha ▸ hret ka hia haj, hb ▸ hret kb hib hbj⟩

/-- Sufficiently many retained host edges yield a rich cycle. -/
theorem rich_cycle_of_supported_edges (p : G.Walk u v) (hp : p.IsPath)
    (i j : ℕ) (hsep : i+2 ≤ j) (hj : j ≤ p.length)
    (hclose : G.Adj (p.getVert i) (p.getVert j)) (F : Finset (Sym2 V))
    (hF : ∀ a b, s(a,b) ∈ F → G.Adj a b ∧
      (∃ k, i ≤ k ∧ k ≤ j ∧ p.getVert k = a) ∧
      (∃ k, i ≤ k ∧ k ≤ j ∧ p.getVert k = b))
    (hcard : 2*(j-i+1) ≤ F.card) : HasRichCycle G := by
  obtain ⟨c, hc, hlen, _, hret⟩ := interval_cycle p hp i j hsep hj hclose
  refine ⟨p.getVert j, c, hc, many_chords_of_support_edges c hc ?_⟩
  rw [hlen]
  exact hcard.trans (Finset.card_le_card (supported_edges_subset p c i j F hF hret))

/-- The full-walk order threshold implies the shorter cycle's threshold. -/
theorem rich_cycle_of_supported_edges_full_length (p : G.Walk u v) (hp : p.IsPath)
    (i j : ℕ) (hsep : i+2 ≤ j) (hj : j ≤ p.length)
    (hclose : G.Adj (p.getVert i) (p.getVert j)) (F : Finset (Sym2 V))
    (hF : ∀ a b, s(a,b) ∈ F → G.Adj a b ∧
      (∃ k, i ≤ k ∧ k ≤ j ∧ p.getVert k = a) ∧
      (∃ k, i ≤ k ∧ k ≤ j ∧ p.getVert k = b))
    (hcard : 2*(p.length+1) ≤ F.card) : HasRichCycle G := by
  apply rich_cycle_of_supported_edges p hp i j hsep hj hclose F hF
  omega
end Erdos642.CampaignFe72210b
