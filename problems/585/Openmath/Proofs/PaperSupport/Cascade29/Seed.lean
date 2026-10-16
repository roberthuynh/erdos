import Openmath.Proofs.PaperSupport.Cascade29.Invariants
import Openmath.Proofs.PaperSupport.Cascade29.SeedSubgraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Cascade29

theorem seedLeft_card : seedLeft.card = 12 := by
  rw [seedLeft, card_image_of_injective _ Sum.inl_injective, card_univ, Fintype.card_fin]
theorem seedRight_card : seedRight.card = 13 := by
  rw [seedRight, card_image_of_injective _ Sum.inr_injective, card_univ, Fintype.card_fin]
theorem seed_disjoint : Disjoint seedLeft seedRight := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  cases x <;> simp_all [seedLeft, seedRight]
theorem seed_cover : seedLeft ∪ seedRight = univ := by
  ext x
  cases x <;> simp [seedLeft, seedRight]
theorem seed_bipartite : seedGraph.IsBipartiteWith ↑seedLeft ↑seedRight := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_coe]
    exact seed_disjoint
  · intro x y hxy
    cases x <;> cases y <;> simp_all [seedGraph, seedAdj, seedLeft, seedRight]

/-- Tiny literal incidence counts; no factor decision is used. -/
theorem seed_row (i : Fin 12) : seedGraph.degree (.inl i) = if i.val < 4 then 10 else if i.val < 9 then 12 else 7 := by
  rw [degree_left_matrix seedGraph le_rfl i]
  have h : ∀ i : Fin 12, (univ.filter fun j => seedRel i j).card =
      if i.val < 4 then 10 else if i.val < 9 then 12 else 7 := by decide
  exact h i

theorem seed_column (j : Fin 13) : seedGraph.degree (.inr j) = if j.val < 6 then 10 else if j.val < 12 then 9 else 7 := by
  rw [degree_right_matrix seedGraph le_rfl j]
  have h : ∀ j : Fin 13, (univ.filter fun i => seedRel i j).card = if j.val < 6 then 10 else if j.val < 12 then 9 else 7 := by decide
  exact h j

theorem seed_degrees : ∀ v, 6 ≤ seedGraph.degree v ∧ seedGraph.degree v ≤ 12 := by
  intro v
  cases v with
  | inl i => rw [seed_row]; split_ifs <;> omega
  | inr j => rw [seed_column]; split_ifs <;> omega

theorem seed_edges : seedGraph.edgeFinset.card = 121 := by
  rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges seed_bipartite]
  rw [seedLeft, sum_image (by intro x _ y _ h; exact Sum.inl_injective h)]
  simp_rw [seed_row]
  decide

theorem seed_good : DataGood seedData := by
  exact ⟨seed_disjoint, seed_cover, seed_bipartite, seed_degrees,
    by change seedGraph.edgeFinset.card + 29 = 6 * Fintype.card SeedVertex
       rw [seed_edges]
       decide, seed_no_regular_subgraph⟩

theorem seed_seven (v : SeedVertex) : 7 ≤ seedGraph.degree v := by
  cases v with
  | inl i => rw [seed_row]; split_ifs <;> omega
  | inr j => rw [seed_column]; split_ifs <;> omega

end Erdos585.Cascade29
