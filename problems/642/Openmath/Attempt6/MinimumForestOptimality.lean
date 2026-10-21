import Openmath.Attempt6.MinimumForest

/-! Minimum-forest optimality in the original graph. No density conclusion. -/
namespace Erdos585.Attempt6

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V}

namespace SpanningLinearForest

variable [Fintype V]

/-- Joining two endpoints in different components is an actual valid spanning
linear forest operation, using the supplied original-graph edge. -/
def joinEndpoints (F : SpanningLinearForest G) {x y : V}
    (hxy : G.Adj x y) (hcomp : ¬ F.graph.Reachable x y)
    (hx : Nat.card (F.graph.neighborSet x) ≤ 1)
    (hy : Nat.card (F.graph.neighborSet y) ≤ 1) : SpanningLinearForest G where
  graph := F.graph ⊔ edge x y
  le_original := by
    apply sup_le F.le_original
    rw [edge_le_iff]
    exact Or.inr hxy
  acyclic := F.acyclic.sup_edge_of_not_reachable hcomp
  degree_le_two := by
    intro v
    change ((F.graph ⊔ edge x y).neighborSet v).ncard ≤ 2
    rw [neighborSet_sup]
    by_cases hvx : v = x
    · subst v
      have he : (edge x y).neighborSet x = {y} := by
        ext w
        simp [mem_neighborSet, edge_adj, hxy.ne, eq_comm]
        rintro rfl
        exact hxy.ne
      rw [he]
      have h := Set.ncard_union_le (F.graph.neighborSet x) {y}
      simpa using (h.trans (by simpa using Nat.add_le_add_right hx 1))
    by_cases hvy : v = y
    · subst v
      have he : (edge x y).neighborSet y = {x} := by
        ext w
        simp [mem_neighborSet, edge_adj, hxy.ne, eq_comm]
        rintro rfl
        exact hxy.ne.symm
      rw [he]
      have h := Set.ncard_union_le (F.graph.neighborSet y) {x}
      simpa using (h.trans (by simpa using Nat.add_le_add_right hy 1))
    · have he : (edge x y).neighborSet v = ∅ := by
        ext w
        simp [mem_neighborSet, edge_adj, hvx, hvy]
      rw [he, Set.union_empty]
      exact F.degree_le_two v

/-- Adding an original edge between two distinct endpoint components strictly
reduces the number of actual connected components. This follows from the
surjective component map identifying the two formerly distinct components. -/
theorem joinEndpoints_componentCount_lt (F : SpanningLinearForest G) {x y : V}
    (hxy : G.Adj x y) (hcomp : ¬ F.graph.Reachable x y)
    (hx : Nat.card (F.graph.neighborSet x) ≤ 1)
    (hy : Nat.card (F.graph.neighborSet y) ≤ 1) :
    (F.joinEndpoints hxy hcomp hx hy).componentCount < F.componentCount := by
  classical
  by_contra hlt
  let H := F.joinEndpoints hxy hcomp hx hy
  have hcard : F.componentCount ≤ H.componentCount := Nat.le_of_not_gt hlt
  have hle : F.graph ≤ H.graph := le_sup_left
  let f : F.graph.ConnectedComponent → H.graph.ConnectedComponent :=
    ConnectedComponent.map (Hom.ofLE hle)
  have hf : Function.Surjective f := ConnectedComponent.surjective_map_ofLE hle
  have hinj : Function.Injective f := (hf.bijective_of_nat_card_le hcard).injective
  apply hcomp
  apply ConnectedComponent.exact
  apply hinj
  change H.graph.connectedComponentMk x = H.graph.connectedComponentMk y
  apply ConnectedComponent.connectedComponentMk_eq_of_adj
  exact Or.inr ((edge_adj x y x y).mpr ⟨Or.inl ⟨rfl, rfl⟩, hxy.ne⟩)

/-- Minimum component count forces every original edge between forest
endpoints to stay inside a single forest component. -/
theorem IsMinimum.endpoints_reachable {F : SpanningLinearForest G} (hmin : F.IsMinimum)
    {x y : V} (hxy : G.Adj x y)
    (hx : Nat.card (F.graph.neighborSet x) ≤ 1)
    (hy : Nat.card (F.graph.neighborSet y) ≤ 1) : F.graph.Reachable x y := by
  by_contra hcomp
  exact (Nat.not_lt_of_ge (hmin _)) (F.joinEndpoints_componentCount_lt hxy hcomp hx hy)

/-- A degree-at-most-one vertex has no original edge to any degree-at-most-one
vertex in another actual forest component. -/
theorem IsMinimum.endpoints_not_adj_of_not_reachable {F : SpanningLinearForest G}
    (hmin : F.IsMinimum) {x y : V} (hcomp : ¬ F.graph.Reachable x y)
    (hx : Nat.card (F.graph.neighborSet x) ≤ 1)
    (hy : Nat.card (F.graph.neighborSet y) ≤ 1) : ¬ G.Adj x y :=
  fun hxy => hcomp (hmin.endpoints_reachable hxy hx hy)

                                                                            
                                                                     
theorem IsMinimum.external_endpointNeighbor_degree_eq_two
    {F : SpanningLinearForest G} (hmin : F.IsMinimum) {x y : V}
    (hx : Nat.card (F.graph.neighborSet x) ≤ 1) (hxy : G.Adj x y)
    (hcomp : ¬ F.graph.Reachable x y) : Nat.card (F.graph.neighborSet y) = 2 := by
  have hy : ¬ Nat.card (F.graph.neighborSet y) ≤ 1 := by
    intro hy
    exact hcomp (hmin.endpoints_reachable hxy hx hy)
  have htwo := F.degree_le_two y
  omega

/-- In a minimum forest, endpoint tokens from distinct components cannot
be adjacent in the original graph. Isolate tokens are included. -/
theorem IsMinimum.endpointTokens_not_adj {F : SpanningLinearForest G} (hmin : F.IsMinimum)
    {s t : F.EndpointToken} (hst : s.1 ≠ t.1) :
    ¬ G.Adj (F.endpointVertex s) (F.endpointVertex t) := by
  intro hadj
  have hr := hmin.endpoints_reachable hadj
    (F.endpointVertex_degree_le_one s) (F.endpointVertex_degree_le_one t)
  have hs := F.endpointVertex_mem_component s
  have ht := F.endpointVertex_mem_component t
  apply hst
  rw [← hs, ← ht]
  exact ConnectedComponent.sound hr

/-- The endpoint-token form retains isolated vertices and both endpoint
incidences of every component. -/
theorem IsMinimum.endpointToken_external_neighbor_degree_eq_two
    {F : SpanningLinearForest G} (hmin : F.IsMinimum)
    (t : F.EndpointToken) {y : V} (hxy : G.Adj (F.endpointVertex t) y)
    (houtside : y ∉ t.1.supp) : Nat.card (F.graph.neighborSet y) = 2 := by
  apply hmin.external_endpointNeighbor_degree_eq_two
    (F.endpointVertex_degree_le_one t) hxy
  intro hr
  apply houtside
  have hs := F.endpointVertex_mem_component t
  have he := ConnectedComponent.sound hr
  exact he.symm.trans hs

                                                                           
                                                 
theorem IsMinimum.endpointToken_neighborSet_subset
    {F : SpanningLinearForest G} (hmin : F.IsMinimum) (t : F.EndpointToken) :
    G.neighborSet (F.endpointVertex t) ⊆
      t.1.supp ∪ {y | Nat.card (F.graph.neighborSet y) = 2} := by
  intro y hy
  by_cases hmem : y ∈ t.1.supp
  · exact Or.inl hmem
  · exact Or.inr (hmin.endpointToken_external_neighbor_degree_eq_two t hy hmem)

end SpanningLinearForest

end Erdos585.Attempt6
