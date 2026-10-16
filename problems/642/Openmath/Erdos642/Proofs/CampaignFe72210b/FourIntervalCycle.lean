import Openmath.Erdos642.Proofs.CampaignFe72210b.RichWalkCycle
import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestEdges

/-! Deterministic retention of middle host edges between actual first/fourth closing vertices. -/
namespace Erdos642.CampaignFe72210b
open SimpleGraph
variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} {u v : V}

/-- Literal middle support and an actual first/fourth adjacency produce a rich cycle. -/
theorem four_interval_rich_cycle (p : G.Walk u v) (hp : p.IsPath)
    (t : ℕ) (ht : 2 ≤ t) (hfit : 7 * t ≤ p.length + 1) (_hT : 2 ≤ p.length)
    (hclose : ∃ i j : ℕ, i < t ∧ 6 * t ≤ j ∧ j < 7 * t ∧ G.Adj (p.getVert i) (p.getVert j))
    (F : Finset (Sym2 V))
    (hF : ∀ a b, s(a,b) ∈ F → G.Adj a b ∧
      (∃ k : ℕ, 2 * t ≤ k ∧ k ≤ 4 * t - 1 ∧ p.getVert k = a) ∧
      (∃ k : ℕ, 2 * t ≤ k ∧ k ≤ 4 * t - 1 ∧ p.getVert k = b))
    (hcard : 3 * p.length ≤ F.card) : HasRichCycle G := by
  obtain ⟨i, j, hi, hj0, hj1, hadj⟩ := hclose
  apply rich_cycle_of_supported_edges_full_length p hp i j (by omega) (by omega) hadj F
  · intro a b hab
    obtain ⟨hab', ⟨ka, hka0, hka1, hka⟩, ⟨kb, hkb0, hkb1, hkb⟩⟩ := hF a b hab
    exact ⟨hab', ⟨ka, by omega, by omega, hka⟩, ⟨kb, by omega, by omega, hkb⟩⟩
  · omega

namespace ForestBundle
variable [DecidableEq V] {A B : Finset V} {q m b : ℕ}
variable (F : ForestBundle G A B q m b)

omit [Fintype V] in
/-- An actual selected first/fourth root-leaf edge supplies the closing indices. -/
theorem closing_edge_of_selectedEdges (p : G.Walk u v) (t : ℕ)
    (L R : Finset V) (hne : (F.selectedEdges L R).Nonempty)
    (hL : ∀ a ∈ L, ∃ i : ℕ, i < t ∧ p.getVert i = a)
    (hR : ∀ a ∈ R, ∃ j : ℕ, 6 * t ≤ j ∧ j < 7 * t ∧ p.getVert j = a) :
    ∃ i j : ℕ, i < t ∧ 6 * t ≤ j ∧ j < 7 * t ∧ G.Adj (p.getVert i) (p.getVert j) := by
  obtain ⟨e, he⟩ := hne
  obtain ⟨z, hz, _⟩ := Finset.mem_image.mp he
  have hz' := Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2
  obtain ⟨i, hi, hia⟩ := hL z.2 hz'.2.2
  obtain ⟨j, hj0, hj1, hjb⟩ := hR (F.root z.1) hz'.2.1
  refine ⟨i, j, hi, hj0, hj1, ?_⟩
  rw [hia, hjb]
  exact (F.adjacent z.1 z.2 hz'.1).symm

end ForestBundle
end Erdos642.CampaignFe72210b
