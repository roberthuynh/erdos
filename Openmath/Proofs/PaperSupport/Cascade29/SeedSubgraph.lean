import Openmath.Proofs.PaperSupport.Cascade29.SeedCascade
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Cascade29

/-- Literal arbitrary 7-regular Subgraph absence for the actual all-7 seed. -/
theorem seed_no_regular_subgraph :
    ¬ ∃ H : (seedGraph).Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 7 := by
  classical
  rintro ⟨H, hne, hregular⟩
  let F := univ.filter fun x : Fin 12 × Fin 13 => H.Adj (Sum.inl x.1) (Sum.inr x.2)
  have hleft (i : Fin 12) : matrixRowDegree F i = H.degree (Sum.inl i) := by
    dsimp [F]
    rw [row_card_matrix (fun i j => H.Adj (Sum.inl i) (Sum.inr j)) i]
    exact (degree_left_matrix H.spanningCoe H.spanningCoe_le i).symm.trans
      (SimpleGraph.Subgraph.degree_spanningCoe _)
  have hright (j : Fin 13) : matrixColumnDegree F j = H.degree (Sum.inr j) := by
    dsimp [F]
    rw [column_card_matrix (fun i j => H.Adj (Sum.inl i) (Sum.inr j)) j]
    exact (degree_right_matrix H.spanningCoe H.spanningCoe_le j).symm.trans
      (SimpleGraph.Subgraph.degree_spanningCoe _)
  have hdegrees (v : Fin 12 ⊕ Fin 13) : H.degree v = 0 ∨ H.degree v = 7 := by
    by_cases hv : v ∈ H.verts
    · right
      exact (SimpleGraph.Subgraph.coe_degree H ⟨v, hv⟩).symm.trans (hregular.degree_eq _)
    · left
      exact SimpleGraph.Subgraph.degree_of_notMem_verts hv
  have hFne : F.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    have hd : H.degree v = 7 :=
      (SimpleGraph.Subgraph.coe_degree H ⟨v, hv⟩).symm.trans (hregular.degree_eq _)
    obtain ⟨w, hvw⟩ := (SimpleGraph.Subgraph.degree_pos_iff_exists_adj).mp (by omega : 0 < H.degree v)
    have hg := H.adj_sub hvw
    cases v with
    | inl i =>
      cases w with
      | inl i' => exact hg.elim
      | inr j => exact ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hvw⟩⟩
    | inr j =>
      cases w with
      | inl i => exact ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hvw.symm⟩⟩
      | inr j' => exact hg.elim
  apply seed_no_regular_matrix F hFne
  · intro x hx
    exact H.adj_sub (mem_filter.mp hx).2
  · intro i
    rw [hleft]
    exact hdegrees _
  · intro j
    rw [hright]
    exact hdegrees _


#print axioms seed_no_regular_matrix
#print axioms seed_no_regular_subgraph


end Erdos585.Cascade29
