import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

                                                                                               
                                                                                           
                                                                                             
                                                                                          
                                                                                              
                   
namespace Erdos642.CloudT9_20261021.TreeBranch

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A walk avoiding `w` uses no edge at `w`. -/
theorem edges_subset_deleteIncidenceSet {a b w : V} (p : G.Walk a b) (hw : w ∉ p.support) :
    ∀ e ∈ p.edges, e ∈ (G.deleteIncidenceSet w).edgeSet := by
  intro e he
  rw [deleteIncidenceSet, edgeSet_deleteEdges, Set.mem_sdiff]
  refine ⟨p.edges_subset_edgeSet he, ?_⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    rw [mk'_mem_incidenceSet_iff]
    rintro ⟨-, rfl | rfl⟩
    · exact hw (p.fst_mem_support_of_mem_edges he)
    · exact hw (p.snd_mem_support_of_mem_edges he)

                                                                                              
theorem mem_support_of_not_reachable {a b w : V} (p : G.Walk a b)
    (hab : ¬ (G.deleteIncidenceSet w).Reachable a b) : w ∈ p.support := by
  by_contra hw
  exact hab ⟨p.transfer _ (edges_subset_deleteIncidenceSet G p hw)⟩

/-- A walk of `G − w` starting away from `w` never visits `w`. -/
theorem notMem_support_of_walk_delete {a b w : V} (q : (G.deleteIncidenceSet w).Walk a b)
    (ha : a ≠ w) : w ∉ q.support := by
  induction q with
  | nil => simpa using ha.symm
  | cons h q ih =>
    rw [Walk.support_cons, List.mem_cons, not_or]
    exact ⟨ha.symm, ih (deleteIncidenceSet_adj.mp h).2.2⟩

                                                                                           
                                                       
theorem not_reachable_of_mem_support [DecidableEq V] (hG : G.IsAcyclic) {a b w : V}
    (p : G.Walk a b) (hp : p.IsPath) (hw : w ∈ p.support) (ha : a ≠ w) :
    ¬ (G.deleteIncidenceSet w).Reachable a b := by
  rintro ⟨q⟩
  have hle : G.deleteIncidenceSet w ≤ G := deleteEdges_le _
  let r : G.Walk a b := q.toPath.1.mapLe hle
  have hr : r.IsPath := Walk.IsPath.mapLe hle q.toPath.2
  have hpr : (⟨p, hp⟩ : G.Path a b) = ⟨r, hr⟩ := hG.path_unique ⟨p, hp⟩ ⟨r, hr⟩
  have hval : p = r := congrArg Subtype.val hpr
  have hwr : w ∈ r.support := by
    rw [← hval]
    exact hw
  rw [Walk.support_mapLe_eq_support] at hwr
  exact notMem_support_of_walk_delete G q.toPath.1 ha hwr

                                                                                           
                                                                                              
                                  
theorem shared_internal_vertex_of_three_branches {a b c w : V} (p : G.Walk a b) (q : G.Walk b c)
    (hab : ¬ (G.deleteIncidenceSet w).Reachable a b)
    (hbc : ¬ (G.deleteIncidenceSet w).Reachable b c)
    (ha : a ≠ w) (hb : b ≠ w) (hc : c ≠ w) :
    ∃ x, x ∈ p.support ∧ x ∈ q.support ∧ x ≠ a ∧ x ≠ b ∧ x ≠ c :=
  ⟨w, mem_support_of_not_reachable G p hab, mem_support_of_not_reachable G q hbc,
    ha.symm, hb.symm, hc.symm⟩

end Erdos642.CloudT9_20261021.TreeBranch
