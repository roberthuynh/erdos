import Openmath.Attempt6.RotationFamily
import Openmath.Attempt6.MinimumForestOptimality

/-!
# Actual forest incidence bounds for reachable endpoint pools

The incidence identities below count actual original-vertex neighbors in the
stored forest graph. They do not assume a pool cardinality bound or a numerical
double-counting identity. The full rotation-pool expansion and exclusion lemmas
remain separate obligations.
-/
namespace Erdos585.Attempt6

open SimpleGraph
open scoped BigOperators

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Number of actual neighbors of a vertex in a specified finite set. -/
noncomputable def graphDegreeInto (H : SimpleGraph V) (S : Finset V) (v : V) : ℕ := by
  classical
  exact (S.filter (H.Adj v)).card

omit [Fintype V] [DecidableEq V] in
/-- Both sides count the same actual ordered cross incidences, using symmetry
of adjacency. No bipartite or regularity hypothesis is needed. -/
theorem graphDegreeInto_sum_comm (H : SimpleGraph V) (A B : Finset V) :
    (∑ v ∈ A, graphDegreeInto H B v) = ∑ w ∈ B, graphDegreeInto H A w := by
  classical
  simp only [graphDegreeInto, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro v hv
  rw [H.adj_comm]

omit [DecidableEq V] in
theorem graphDegreeInto_le_neighborCard (H : SimpleGraph V) (S : Finset V) (v : V) :
    graphDegreeInto H S v ≤ Nat.card (H.neighborSet v) := by
  classical
  rw [Nat.card_eq_fintype_card, H.card_neighborSet_eq_degree]
  change (S.filter (H.Adj v)).card ≤ (H.neighborFinset v).card
  apply Finset.card_le_card
  intro w hw
  exact (H.mem_neighborFinset v w).mpr (Finset.mem_filter.mp hw).2

namespace SpanningLinearForest

variable {F : SpanningLinearForest G}

theorem graphDegreeInto_le_two (F : SpanningLinearForest G) (S : Finset V) (v : V) :
    graphDegreeInto F.graph S v ≤ 2 :=
  (graphDegreeInto_le_neighborCard F.graph S v).trans (F.degree_le_two v)

/-- The actual vertices in A with precisely i forest neighbors in B. -/
noncomputable def incidenceClass (F : SpanningLinearForest G)
    (A B : Finset V) (i : ℕ) : Finset V := by
  classical
  exact A.filter (fun v => graphDegreeInto F.graph B v = i)

/-- A linear forest has only the actual incidence classes zero, one and two. -/
theorem incidenceClass_partition (F : SpanningLinearForest G) (A B : Finset V) :
    A.card = (F.incidenceClass A B 0).card +
      (F.incidenceClass A B 1).card + (F.incidenceClass A B 2).card := by
  classical
  simp only [incidenceClass, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  have h := F.graphDegreeInto_le_two B v
  split_ifs <;> omega

/-- The incidence sum is derived from the actual classes, with multiplicity
two at a degree-two vertex. -/
theorem graphDegreeInto_sum_eq_classes (F : SpanningLinearForest G) (A B : Finset V) :
    (∑ v ∈ A, graphDegreeInto F.graph B v) =
      (F.incidenceClass A B 1).card + 2 * (F.incidenceClass A B 2).card := by
  classical
  simp only [incidenceClass, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  have h := F.graphDegreeInto_le_two B v
  split_ifs <;> omega

/-- Exact actual forest-edge double counting between any two finite sets. -/
theorem incidenceClass_double_count (F : SpanningLinearForest G) (A B : Finset V) :
    (F.incidenceClass A B 1).card + 2 * (F.incidenceClass A B 2).card =
      (F.incidenceClass B A 1).card + 2 * (F.incidenceClass B A 2).card := by
  rw [← F.graphDegreeInto_sum_eq_classes A B, graphDegreeInto_sum_comm,
    F.graphDegreeInto_sum_eq_classes B A]

/-- The endpoint-defect correction in the half-column argument follows from
actual incidence counting and the actual degree-class partition. -/
theorem incidenceClass_half_column_identity (F : SpanningLinearForest G)
    (C B : Finset V) :
    2 * C.card = (F.incidenceClass B C 1).card +
      2 * (F.incidenceClass B C 2).card +
      (F.incidenceClass C B 1).card + 2 * (F.incidenceClass C B 0).card := by
  have hp := F.incidenceClass_partition C B
  have he := F.incidenceClass_double_count C B
  omega

/-- In particular the actual two-neighbor boundary class is no larger than
the pool. This is a conclusion, with no assumed pool cardinality inequality. -/
theorem incidenceClass_two_card_le (F : SpanningLinearForest G) (C B : Finset V) :
    (F.incidenceClass B C 2).card ≤ C.card := by
  have h := F.incidenceClass_half_column_identity C B
  omega

end SpanningLinearForest

omit [Fintype V] in
/-- The full fixed-token reachable pool is independent whenever its free
tokens lie on one bipartition shore. -/
theorem rotationComponent_no_adj {F : List (RotationPath G)} {X : Multiset V}
    {S T : Set V} (hG : G.IsBipartiteWith S T)
    (hfixed : X ≤ rotationForestEndpoints F)
    (hshore : ∀ z ∈ rotationForestEndpoints F - X, z ∈ S)
    {v w : V} (hv : v ∈ rotationComponent F X) (hw : w ∈ rotationComponent F X) :
    ¬ G.Adj v w := by
  intro hadj
  have hs := rotationComponent_shore hG hfixed hshore
  have hvS := hs hv
  have hwS := hs hw
  have hwT := hG.mem_of_mem_adj hvS hadj
  exact Set.disjoint_left.mp hG.disjoint hwS hwT

/-- Actual external graph boundary, including all original neighbors of C
outside C and no other vertices. -/
noncomputable def graphBoundaryFinset (H : SimpleGraph V) (C : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => u ∉ C ∧ ∃ v ∈ C, H.Adj v u)

theorem mem_graphBoundaryFinset {H : SimpleGraph V} {C : Finset V} {u : V} :
    u ∈ graphBoundaryFinset H C ↔ u ∉ C ∧ ∃ v ∈ C, H.Adj v u := by
  classical
  simp [graphBoundaryFinset]

/-- For an independent pool, every neighbor in the stored original subgraph
lies in the actual original-graph boundary. Thus the counted incidence is
the full forest degree, rather than an assumed numerical value. -/
theorem forestDegreeInto_boundary_eq (F : SpanningLinearForest G) (C : Finset V)
    (hind : ∀ v ∈ C, ∀ w ∈ C, ¬ G.Adj v w) {v : V} (hv : v ∈ C) :
    graphDegreeInto F.graph (graphBoundaryFinset G C) v =
      Nat.card (F.graph.neighborSet v) := by
  classical
  rw [Nat.card_eq_fintype_card, F.graph.card_neighborSet_eq_degree]
  change ((graphBoundaryFinset G C).filter (F.graph.Adj v)).card =
    (F.graph.neighborFinset v).card
  congr 1
  ext w
  simp only [Finset.mem_filter, mem_graphBoundaryFinset, mem_neighborFinset]
  constructor
  · exact fun h => h.2
  · intro hvw
    exact ⟨⟨fun hw => hind v hv w hw (F.le_original hvw),
      ⟨v, hv, F.le_original hvw⟩⟩, hvw⟩

namespace SpanningLinearForest

/-- The pool is the full fixed-token family of this actual starting forest. -/
noncomputable def reachableEndpointPool (F : SpanningLinearForest G) (X : Multiset V) :
    Finset V := by
  classical
  exact (rotationComponent F.pathList X).toFinset

theorem mem_reachableEndpointPool {F : SpanningLinearForest G} {X : Multiset V} {v : V} :
    v ∈ F.reachableEndpointPool X ↔ v ∈ rotationComponent F.pathList X := by
  simp [reachableEndpointPool]

theorem reachableEndpointPool_independent (F : SpanningLinearForest G) (X : Multiset V)
    {S T : Set V} (hG : G.IsBipartiteWith S T)
    (hfixed : X ≤ rotationForestEndpoints F.pathList)
    (hshore : ∀ z ∈ rotationForestEndpoints F.pathList - X, z ∈ S) :
    ∀ v ∈ F.reachableEndpointPool X, ∀ w ∈ F.reachableEndpointPool X, ¬ G.Adj v w := by
  intro v hv w hw
  exact rotationComponent_no_adj hG hfixed hshore
    (mem_reachableEndpointPool.mp hv) (mem_reachableEndpointPool.mp hw)

/-- This specializes the actual degree identity to the original graph's full
reachable endpoint pool, retaining the actual starting forest. -/
theorem reachableEndpointPool_degree_boundary (F : SpanningLinearForest G) (X : Multiset V)
    {S T : Set V} (hG : G.IsBipartiteWith S T)
    (hfixed : X ≤ rotationForestEndpoints F.pathList)
    (hshore : ∀ z ∈ rotationForestEndpoints F.pathList - X, z ∈ S)
    {v : V} (hv : v ∈ F.reachableEndpointPool X) :
    graphDegreeInto F.graph (graphBoundaryFinset G (F.reachableEndpointPool X)) v =
      Nat.card (F.graph.neighborSet v) :=
  forestDegreeInto_boundary_eq F _ (F.reachableEndpointPool_independent X hG hfixed hshore) hv

/-- The half-column identity for the actual full reachable pool and its actual
original-graph boundary. No pool cardinality or incidence identity is assumed. -/
theorem reachableEndpointPool_half_column (F : SpanningLinearForest G) (X : Multiset V) :
    let C := F.reachableEndpointPool X
    let B := graphBoundaryFinset G C
    2 * C.card = (F.incidenceClass B C 1).card + 2 * (F.incidenceClass B C 2).card +
      (F.incidenceClass C B 1).card + 2 * (F.incidenceClass C B 0).card :=
  F.incidenceClass_half_column_identity _ _

theorem reachableEndpointPool_two_boundary_le (F : SpanningLinearForest G) (X : Multiset V) :
    (F.incidenceClass (graphBoundaryFinset G (F.reachableEndpointPool X))
      (F.reachableEndpointPool X) 2).card ≤ (F.reachableEndpointPool X).card :=
  F.incidenceClass_two_card_le _ _

/-- Minimality already rules out an actual forest isolate among original
neighbors of any actual forest endpoint. This is weaker than the rotation
boundary B0 exclusion, which asks for a forest neighbor inside the full pool. -/
theorem IsMinimum.endpoint_neighbor_forest_degree_pos {F : SpanningLinearForest G}
    (hmin : F.IsMinimum) {x y : V} (hx : Nat.card (F.graph.neighborSet x) ≤ 1)
    (hxy : G.Adj x y) : 0 < Nat.card (F.graph.neighborSet y) := by
  classical
  by_contra hzero
  have hy : Nat.card (F.graph.neighborSet y) = 0 := by omega
  have hr := hmin.endpoints_reachable hxy hx (by omega : Nat.card (F.graph.neighborSet y) ≤ 1)
  have hpos := SimpleGraph.Reachable.degree_pos_right hxy.ne hr
  have hc : Nat.card (F.graph.neighborSet y) = F.graph.degree y := by
    rw [Nat.card_eq_fintype_card, F.graph.card_neighborSet_eq_degree]
  omega

end SpanningLinearForest

/-- The same full-degree statement for the original graph itself. -/
theorem graphDegreeInto_boundary_eq (H : SimpleGraph V) (C : Finset V)
    (hind : ∀ v ∈ C, ∀ w ∈ C, ¬ H.Adj v w) {v : V} (hv : v ∈ C) :
    graphDegreeInto H (graphBoundaryFinset H C) v = Nat.card (H.neighborSet v) := by
  classical
  rw [Nat.card_eq_fintype_card, H.card_neighborSet_eq_degree]
  change ((graphBoundaryFinset H C).filter (H.Adj v)).card =
    (H.neighborFinset v).card
  congr 1
  ext w
  simp only [Finset.mem_filter, mem_graphBoundaryFinset, mem_neighborFinset]
  constructor
  · exact fun h => h.2
  · intro hvw
    exact ⟨⟨fun hw => hind v hv w hw hvw, ⟨v, hv, hvw⟩⟩, hvw⟩

namespace SpanningLinearForest

/-- Any vertex weight partitions over the three actual forest incidence
classes. In particular this can weight vertices by their original-graph degree. -/
theorem incidenceClass_weight_partition (F : SpanningLinearForest G)
    (C B : Finset V) (f : V → ℕ) :
    (∑ u ∈ B, f u) = (∑ u ∈ F.incidenceClass B C 0, f u) +
      (∑ u ∈ F.incidenceClass B C 1, f u) +
      (∑ u ∈ F.incidenceClass B C 2, f u) := by
  classical
  simp only [incidenceClass, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  have h := F.graphDegreeInto_le_two C v
  split_ifs <;> omega

/-- Original-graph incidences into a boundary class are bounded by the actual
maximum-degree premise, not by an assumed numerical incidence inequality. -/
theorem graphDegreeInto_sum_le_degreeBound (H : SimpleGraph V) (A B : Finset V)
    (D : ℕ) (hD : ∀ u, Nat.card (H.neighborSet u) ≤ D) :
    (∑ u ∈ B, graphDegreeInto H A u) ≤ D * B.card := by
  classical
  calc
    (∑ u ∈ B, graphDegreeInto H A u) ≤ ∑ _u ∈ B, D := by
      apply Finset.sum_le_sum
      intro u hu
      exact (graphDegreeInto_le_neighborCard H A u).trans (hD u)
    _ = D * B.card := by simp [Nat.mul_comm]

                                                                       
                                                                             
theorem actual_boundary_density_with_zero_class (F : SpanningLinearForest G)
    (C : Finset V) (d s : ℕ)
    (hind : ∀ v ∈ C, ∀ w ∈ C, ¬ G.Adj v w)
    (hlower : ∀ v ∈ C, d ≤ Nat.card (G.neighborSet v))
    (hupper : ∀ v, Nat.card (G.neighborSet v) ≤ d + s) :
    let B := graphBoundaryFinset G C
    d * C.card ≤
      (∑ u ∈ F.incidenceClass B C 1, graphDegreeInto G C u) +
        (d + s) * ((F.incidenceClass B C 0).card + (F.incidenceClass B C 2).card) := by
  classical
  dsimp
  let B := graphBoundaryFinset G C
  have hlow : d * C.card ≤ ∑ v ∈ C, graphDegreeInto G B v := by
    calc
      d * C.card = ∑ _v ∈ C, d := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ C, graphDegreeInto G B v := by
        apply Finset.sum_le_sum
        intro v hv
        rw [show B = graphBoundaryFinset G C from rfl, graphDegreeInto_boundary_eq G C hind hv]
        exact hlower v hv
  have hzero := graphDegreeInto_sum_le_degreeBound G C (F.incidenceClass B C 0)
    (d + s) hupper
  have htwo := graphDegreeInto_sum_le_degreeBound G C (F.incidenceClass B C 2)
    (d + s) hupper
  rw [graphDegreeInto_sum_comm G C B,
    F.incidenceClass_weight_partition C B (graphDegreeInto G C)] at hlow
  change d * C.card ≤
    (∑ u ∈ F.incidenceClass B C 1, graphDegreeInto G C u) +
      (d + s) * ((F.incidenceClass B C 0).card + (F.incidenceClass B C 2).card)
  nlinarith

/-- The near-regular half-column incidence bound follows from actual graph
degrees and actual forest counting. Exactly the missing B0 exclusion remains
as a debt term; no desired pool-size or half-column numerical bound is assumed. -/
theorem actual_half_column_with_zero_class (F : SpanningLinearForest G)
    (C : Finset V) (d s : ℕ)
    (hind : ∀ v ∈ C, ∀ w ∈ C, ¬ G.Adj v w)
    (hlower : ∀ v ∈ C, d ≤ Nat.card (G.neighborSet v))
    (hupper : ∀ v, Nat.card (G.neighborSet v) ≤ d + s) :
    let B := graphBoundaryFinset G C
    d * (F.incidenceClass B C 1).card +
      d * (F.incidenceClass C B 1).card + 2 * d * (F.incidenceClass C B 0).card ≤
      2 * (∑ u ∈ F.incidenceClass B C 1, graphDegreeInto G C u) +
        2 * s * C.card + 2 * (d + s) * (F.incidenceClass B C 0).card := by
  dsimp
  let B := graphBoundaryFinset G C
  have hdensity := F.actual_boundary_density_with_zero_class C d s hind hlower hupper
  have hid := congrArg (fun z : ℕ => d * z) (F.incidenceClass_half_column_identity C B)
  have htwo := Nat.mul_le_mul_left (2 * s) (F.incidenceClass_two_card_le C B)
  change d * (F.incidenceClass B C 1).card +
    d * (F.incidenceClass C B 1).card + 2 * d * (F.incidenceClass C B 0).card ≤
    2 * (∑ u ∈ F.incidenceClass B C 1, graphDegreeInto G C u) +
      2 * s * C.card + 2 * (d + s) * (F.incidenceClass B C 0).card
  nlinarith

end SpanningLinearForest

/-- An arbitrary noninitial vertex on an actual walk has a displayed
predecessor edge. The path split required by a rotation is derived here. -/
theorem walk_predecessor_decomposition {x y : V} (r : G.Walk x y)
    (u : V) (hu : u ∈ r.support) (hne : u ≠ x) :
    ∃ (w : V) (p : G.Walk x w) (q : G.Walk u y) (hwu : G.Adj w u),
      r = rotationOriginal p q hwu := by
  revert u
  induction r with
  | nil =>
    intro u hu hne
    simp only [Walk.support_nil, List.mem_singleton] at hu
    exact False.elim (hne hu)
  | @cons x z y hxz r ih =>
    intro u hu hne
    simp only [Walk.support_cons, List.mem_cons] at hu
    rcases hu with h | hu
    · exact False.elim (hne h)
    · by_cases huz : u = z
      · subst u
        exact ⟨x, .nil, r, hxz, rfl⟩
      · obtain ⟨w, p, q, hwu, hr⟩ := ih u hu huz
        refine ⟨w, .cons hxz p, q, hwu, ?_⟩
        exact congrArg (Walk.cons hxz) hr
        
/-- A genuine neighbor-pivot incidence on the same actual component produces
a legal fixed-token rotation with a simple resulting path and a free new
endpoint. The predecessor/decomposition is not an input assumption. -/
theorem samePath_pivot_supplies_free_endpoint {x y u : V} (r : G.Walk x y) (pre post : List (RotationPath G))
    (hp : r.IsPath) (hu : u ∈ r.support) (hxu : G.Adj x u)
    (X : Multiset V) (hfixed : X ≤ rotationForestEndpoints (pre ++ ⟨x, y, r⟩ :: post))
    (hfree : x ∈ rotationForestEndpoints (pre ++ ⟨x, y, r⟩ :: post) - X) :
    ∃ (w : V) (rnew : G.Walk w y), rnew.IsPath ∧ r.toSubgraph.Adj w u ∧
      FixedForestRotationReachable X (pre ++ ⟨x, y, r⟩ :: post) (pre ++ ⟨w, y, rnew⟩ :: post) ∧
      w ∈ rotationForestEndpoints (pre ++ ⟨w, y, rnew⟩ :: post) - X := by
  obtain ⟨w, p, q, hwu, hr⟩ := walk_predecessor_decomposition r u hu hxu.ne.symm
  subst r
  let rnew := rotatePathStep p q hxu
  have hex := ForestRotation.within_endpoints pre post p q hwu hxu
  have hwfree : w ∈ rotationForestEndpoints (pre ++ ⟨w, y, rnew⟩ :: post) - X := by
    exact endpoint_exchange_new_free hex hfree hfixed
  refine ⟨w, rnew, rotatePathStep_isPath p q hwu hxu hp, ?_, ?_, hwfree⟩
  · rw [Walk.adj_toSubgraph_iff_mem_edges, rotationOriginal_edges]
    simp
  · exact .single (.within pre post p q hwu hxu hfree)

/-- Every original neighbor of the free endpoint lying on its actual path has
an actual path neighbor in the full fixed-token reachable pool. -/
theorem samePath_pivot_neighbor_in_rotationComponent {x y u : V}
    (r : G.Walk x y) (pre post : List (RotationPath G)) (hp : r.IsPath) (hu : u ∈ r.support) (hxu : G.Adj x u)
    (X : Multiset V) (hfixed : X ≤ rotationForestEndpoints (pre ++ ⟨x, y, r⟩ :: post))
    (hfree : x ∈ rotationForestEndpoints (pre ++ ⟨x, y, r⟩ :: post) - X) :
    ∃ w, r.toSubgraph.Adj w u ∧ w ∈ rotationComponent (pre ++ ⟨x, y, r⟩ :: post) X := by
  obtain ⟨w, rnew, _, hwu, hrot, hfreeNew⟩ :=
    samePath_pivot_supplies_free_endpoint r pre post hp hu hxu X hfixed hfree
  exact ⟨w, hwu, (pre ++ ⟨w, y, rnew⟩ :: post), hrot, hfreeNew⟩

/-- A pivot on a different actual component produces a free endpoint at one
of its actual path neighbors. Again the displayed path split is derived from
pivot membership, rather than assumed. -/
theorem differentPath_pivot_neighbor_in_rotationComponent_of_ne_start
    {x y z t u : V} (r : G.Walk x y) (a : G.Walk z t)
    (pre post : List (RotationPath G)) (hu : u ∈ a.support) (hne : u ≠ z)
    (hxu : G.Adj x u) (X : Multiset V)
    (hfixed : X ≤ rotationForestEndpoints (pre ++ ⟨x, y, r⟩ :: ⟨z, t, a⟩ :: post))
    (hfree : x ∈ rotationForestEndpoints (pre ++ ⟨x, y, r⟩ :: ⟨z, t, a⟩ :: post) - X) :
    ∃ w, a.toSubgraph.Adj w u ∧
      w ∈ rotationComponent (pre ++ ⟨x, y, r⟩ :: ⟨z, t, a⟩ :: post) X := by
  obtain ⟨w, p, q, hwu, ha⟩ := walk_predecessor_decomposition a u hu hne
  subst a
  have hex := ForestRotation.between_endpoints pre post r p q hwu hxu
  have hwfree := endpoint_exchange_new_free hex hfree hfixed
  refine ⟨w, ?_, ?_⟩
  · rw [Walk.adj_toSubgraph_iff_mem_edges, rotationOriginal_edges]
    simp
  · exact ⟨pre ++ ⟨y, t, r.reverse.append (.cons hxu q)⟩ :: ⟨z, w, p⟩ :: post,
      .single (.between pre post r p q hwu hxu hfree), hwfree⟩

                                                                        
                                                                             
                                                                
theorem differentPath_pivot_neighbor_in_rotationComponent
    {x y z t u : V} (r : G.Walk x y) (a : G.Walk z t)
    (pre post : List (RotationPath G)) (hu : u ∈ a.support) (hnepath : z ≠ t)
    (hxu : G.Adj x u) (X : Multiset V)
    (hfixed : X ≤ rotationForestEndpoints (pre ++ ⟨x, y, r⟩ :: ⟨z, t, a⟩ :: post))
    (hfree : x ∈ rotationForestEndpoints (pre ++ ⟨x, y, r⟩ :: ⟨z, t, a⟩ :: post) - X) :
    ∃ w, a.toSubgraph.Adj w u ∧
      w ∈ rotationComponent (pre ++ ⟨x, y, r⟩ :: ⟨z, t, a⟩ :: post) X := by
  by_cases hne : u ≠ z
  · exact differentPath_pivot_neighbor_in_rotationComponent_of_ne_start
      r a pre post hu hne hxu X hfixed hfree
  · have huz : u = z := not_ne_iff.mp hne
    subst u
    let Fold : List (RotationPath G) := pre ++ ⟨x, y, r⟩ :: ⟨z, t, a⟩ :: post
    let Frev : List (RotationPath G) := pre ++ ⟨x, y, r⟩ :: ⟨t, z, a.reverse⟩ :: post
    have hrev : FixedForestRotationReachable X Fold Frev := by
      have hstep := Relation.ReflTransGen.single
        (FixedForestRotation.reverse (X := X) (pre ++ [⟨x, y, r⟩]) post a)
      convert hstep using 1 <;> simp [Fold, Frev, List.append_assoc]
    have he : rotationForestEndpoints Frev = rotationForestEndpoints Fold := by
      simp only [Fold, Frev, rotationForestEndpoints_append, rotationForestEndpoints]
      ac_rfl
    have hfixedrev : X ≤ rotationForestEndpoints Frev := by rwa [he]
    have hfreerev : x ∈ rotationForestEndpoints Frev - X := by rwa [he]
    obtain ⟨w, hwu, hwpool⟩ :=
      differentPath_pivot_neighbor_in_rotationComponent_of_ne_start
        r a.reverse pre post (by simpa using hu) hnepath hxu X hfixedrev hfreerev
    refine ⟨w, by simpa using hwu, ?_⟩
    have heq := rotationComponent_eq hrev hfixed
    exact heq ▸ hwpool

end Erdos585.Attempt6
