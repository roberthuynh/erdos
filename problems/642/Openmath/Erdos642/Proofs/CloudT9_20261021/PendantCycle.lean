import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

                                                                                               
                                                                                                
namespace Erdos642.CloudT9_20261021.PendantCycle

open SimpleGraph

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every vertex on the support of a simple cycle has at least two neighbours in `G`. -/
theorem two_le_degree_of_mem_cycle_support {v x : V} (c : G.Walk v v) (hc : c.IsCycle)
    (hx : x ∈ c.support) : 2 ≤ G.degree x := by
  have h2 : (c.toSubgraph.neighborSet x).ncard = 2 := hc.ncard_neighborSet_toSubgraph_eq_two hx
  have hsub : c.toSubgraph.neighborSet x ⊆ G.neighborSet x := c.toSubgraph.neighborSet_subset x
  have hle : (c.toSubgraph.neighborSet x).ncard ≤ (G.neighborSet x).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have hdeg : (G.neighborSet x).ncard = G.degree x := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, card_neighborSet_eq_degree]
  omega

/-- A vertex of degree at most one lies on no simple cycle. -/
theorem notMem_cycle_support_of_degree_le_one {v x : V} (c : G.Walk v v) (hc : c.IsCycle)
    (hx : G.degree x ≤ 1) : x ∉ c.support := by
  intro hmem
  have := two_le_degree_of_mem_cycle_support G c hc hmem
  omega

end Erdos642.CloudT9_20261021.PendantCycle
