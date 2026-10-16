import Openmath.Proofs.PaperSupport.Counter90.Original

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.Counter90

def leftShore : Set (Fin 22) := {v | v.val < 10}
def rightShore : Set (Fin 22) := {v | 10 ≤ v.val}

theorem label_left_value (i : Fin 10) : (labelEquiv (Sum.inl i)).val = i.val := rfl
theorem label_right_value (j : Fin 12) : (labelEquiv (Sum.inr j)).val = 10+j.val := rfl

/-- Literal original incidence, including the original column offset. -/
theorem original_incidence (i : Fin 10) (j : Fin 12) :
    graph.Adj (labelEquiv (Sum.inl i)) (labelEquiv (Sum.inr j)) ↔ rel i j := by
  simp only [graph,SimpleGraph.comap_adj,Equiv.symm_apply_apply]
  rfl

theorem original_cover : leftShore ∪ rightShore = Set.univ := by
  ext v
  change (v.val < 10 ∨ 10 ≤ v.val) ↔ True
  exact ⟨fun _ => True.intro,fun _ => lt_or_ge _ _⟩

theorem original_bipartite : graph.IsBipartiteWith leftShore rightShore := by
  refine ⟨?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro v hv hv'
    change v.val < 10 at hv
    change 10 ≤ v.val at hv'
    omega
  · have h : ∀ v w : Fin 22, graph.Adj v w →
        (v.val < 10 ∧ 10 ≤ w.val) ∨ (10 ≤ v.val ∧ w.val < 10) := by decide
    intro v w hvw
    exact h v w hvw

/-- All entries are degrees of this same original Fin22 graph. -/
theorem original_degree_table (v : Fin 22) :
    graph.degree v = [8,7,9,10,10,10,10,10,10,6,9,8,8,8,8,8,7,8,7,7,6,6][v.val]! := by
  have h : ∀ v : Fin 22,
      graph.degree v = [8,7,9,10,10,10,10,10,10,6,9,8,8,8,8,8,7,8,7,7,6,6][v.val]! := by decide
  exact h v

theorem original_degrees (v : Fin 22) : 6 ≤ graph.degree v ∧ graph.degree v ≤ 10 := by
  rw [original_degree_table]
  have h : ∀ v : Fin 22,
      6 ≤ [8,7,9,10,10,10,10,10,10,6,9,8,8,8,8,8,7,8,7,7,6,6][v.val]! ∧
      [8,7,9,10,10,10,10,10,10,6,9,8,8,8,8,8,7,8,7,7,6,6][v.val]! ≤ 10 := by decide
  exact h v

theorem original_edge_count : graph.edgeFinset.card = 90 := by
  have hd : (∑ v : Fin 22, graph.degree v) = 180 := by
    simp_rw [original_degree_table]
    decide
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges graph
  omega

/-- Bare standalone literal graph properties; no No6 or certificate premise. -/
theorem counter90_properties :
    Fintype.card (Fin 22) = 22 ∧ graph.IsBipartite ∧
      (∀ v, 6 ≤ graph.degree v) ∧ graph.maxDegree ≤ 10 ∧ graph.edgeFinset.card = 90 ∧
      ¬ (∃ H : graph.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 6) := by
  refine ⟨by simp,original_bipartite.isBipartite,fun v => (original_degrees v).1,?_,
    original_edge_count,seed_no_regular_subgraph⟩
  exact graph.maxDegree_le_of_forall_degree_le 10 (fun v => (original_degrees v).2)

end Erdos585.Counter90
