import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! An actual finite maximum cut retains half the edges and half each vertex's degree. -/
namespace Erdos642.CampaignFe72210bContinuation3.ActualMaxCut

open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev cutGraph (S : Finset V) : SimpleGraph V :=
  G.between (S : Set V) (S : Set V)ᶜ

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem cutGraph_adj (S : Finset V) (v w : V) :
    (cutGraph G S).Adj v w ↔
      G.Adj v w ∧ (v ∈ S ∧ w ∉ S ∨ v ∉ S ∧ w ∈ S) := Iff.rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem cutGraph_le (S : Finset V) : cutGraph G S ≤ G :=
  SimpleGraph.between_le

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem cutGraph_bipartiteWith (S : Finset V) :
    (cutGraph G S).IsBipartiteWith (S : Set V) (S : Set V)ᶜ :=
  SimpleGraph.between_isBipartiteWith disjoint_compl_right

/-- Toggle exactly the selected vertex's side. -/
def flipVertex (S : Finset V) (v : V) : Finset V :=
  if v ∈ S then S.erase v else insert v S

omit [Fintype V] in
@[simp] theorem mem_flipVertex_self (S : Finset V) (v : V) :
    v ∈ flipVertex S v ↔ v ∉ S := by
  by_cases hv : v ∈ S <;> simp [flipVertex, hv]

omit [Fintype V] in
theorem mem_flipVertex_of_ne (S : Finset V) (v w : V) (hw : w ≠ v) :
    w ∈ flipVertex S v ↔ w ∈ S := by
  by_cases hv : v ∈ S <;> simp [flipVertex, hv, hw]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Away from the flipped vertex all literal cut edges are unchanged. -/
theorem flip_deleteIncidenceSet (S : Finset V) (v : V) :
    (cutGraph G (flipVertex S v)).deleteIncidenceSet v =
      (cutGraph G S).deleteIncidenceSet v := by
  ext x y
  by_cases hx : x = v
  · subst x
    simp [SimpleGraph.deleteIncidenceSet_adj]
  · by_cases hy : y = v
    · subst y
      simp [SimpleGraph.deleteIncidenceSet_adj]
    · simp only [SimpleGraph.deleteIncidenceSet_adj, cutGraph_adj,
        mem_flipVertex_of_ne S v x hx, mem_flipVertex_of_ne S v y hy]

/-- Flipping swaps crossing and noncrossing original neighbors at that vertex. -/
theorem flip_neighborFinset (S : Finset V) (v : V) :
    (cutGraph G (flipVertex S v)).neighborFinset v =
      G.neighborFinset v \ (cutGraph G S).neighborFinset v := by
  ext w
  by_cases hw : w = v
  · subst w
    simp
  · simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, cutGraph_adj,
      mem_flipVertex_self, mem_flipVertex_of_ne S v w hw]
    tauto

theorem degree_add_flip_degree (S : Finset V) (v : V) :
    (cutGraph G S).degree v + (cutGraph G (flipVertex S v)).degree v = G.degree v := by
  have hsub : (cutGraph G S).neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    have ha : (cutGraph G S).Adj v w := by simpa using hw
    simpa using cutGraph_le G S ha
  have hc := Finset.card_sdiff_of_subset hsub
  rw [← flip_neighborFinset G S v] at hc
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc
  have hle : (cutGraph G S).degree v ≤ G.degree v :=
    SimpleGraph.degree_le_of_le (cutGraph_le G S)
  omega

omit [Fintype V] [DecidableEq V] in
private theorem edgeCard_of_graph_eq {K L : SimpleGraph V}
    [Fintype K.edgeSet] [Fintype L.edgeSet] (h : K = L) :
    K.edgeFinset.card = L.edgeFinset.card := by
  rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
  exact @Fintype.card_congr _ _ _ _
    (Equiv.cast (congrArg (fun H : SimpleGraph V => ↥H.edgeSet) h))

/-- Exact additive edge-count change under an actual single-vertex cut flip. -/
theorem flip_edgeCard_add_degree (S : Finset V) (v : V) :
    (cutGraph G (flipVertex S v)).edgeFinset.card + (cutGraph G S).degree v =
      (cutGraph G S).edgeFinset.card + (cutGraph G (flipVertex S v)).degree v := by
  have h₁ := Nat.sub_add_cancel ((cutGraph G S).degree_le_card_edgeFinset (v := v))
  have h₂ := Nat.sub_add_cancel
    ((cutGraph G (flipVertex S v)).degree_le_card_edgeFinset (v := v))
  rw [← (cutGraph G S).card_edgeFinset_deleteIncidenceSet v] at h₁
  rw [← (cutGraph G (flipVertex S v)).card_edgeFinset_deleteIncidenceSet v] at h₂
  have heq := edgeCard_of_graph_eq (flip_deleteIncidenceSet G S v)
  omega

/-- A genuine finite argmax supplies an actual cut retaining half every vertex's degree. -/
theorem exists_cut_half_degree_and_edges :
    ∃ S : Finset V,
      cutGraph G S ≤ G ∧
      (cutGraph G S).IsBipartiteWith (S : Set V) (S : Set V)ᶜ ∧
      (∀ v : V, G.degree v ≤ 2 * (cutGraph G S).degree v) ∧
      G.edgeFinset.card ≤ 2 * (cutGraph G S).edgeFinset.card := by
  classical
  obtain ⟨S, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset V).powerset
    (fun T => (cutGraph G T).edgeFinset.card)
    (Finset.powerset_nonempty (Finset.univ : Finset V))
  have hdegree : ∀ v : V, G.degree v ≤ 2 * (cutGraph G S).degree v := by
    intro v
    have hflip := hmax (flipVertex S v)
      (Finset.mem_powerset.mpr (Finset.subset_univ _))
    have hedge := flip_edgeCard_add_degree G S v
    have hsum := degree_add_flip_degree G S v
    omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => hdegree v)
  rw [← Finset.mul_sum, G.sum_degrees_eq_twice_card_edges,
    (cutGraph G S).sum_degrees_eq_twice_card_edges] at hsum
  refine ⟨S, cutGraph_le G S, cutGraph_bipartiteWith G S, hdegree, ?_⟩
  omega

/-- The retained graph is an actual bipartite edge subgraph on the original vertex type. -/
theorem exists_bipartite_half_edges :
    ∃ S : Finset V,
      cutGraph G S ≤ G ∧ (cutGraph G S).IsBipartite ∧
      (∀ v : V, G.degree v ≤ 2 * (cutGraph G S).degree v) ∧
      G.edgeFinset.card ≤ 2 * (cutGraph G S).edgeFinset.card := by
  classical
  obtain ⟨S, hle, hbip, hdeg, he⟩ := exists_cut_half_degree_and_edges G
  exact ⟨S, hle, hbip.isBipartite, hdeg, he⟩

end Erdos642.CampaignFe72210bContinuation3.ActualMaxCut
