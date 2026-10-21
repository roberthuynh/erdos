import Openmath.Proofs.ForestPathInput

/-!
# Minimum spanning linear forests in the original graph

A forest here is an actual spanning subgraph of `G`, with no cycles and
maximum degree at most two. Its components are extracted as simple walks in
`G`, including zero-length walks for isolated vertices. Minimum means minimum
number of connected components among precisely these spanning subgraphs.
No small-component bound or rotation/sampling conclusion is asserted.
-/

namespace Erdos585.Attempt6

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- An actual spanning linear forest. The graph has the original vertex type,
so isolated original vertices are retained. `Nat.card` avoids adding an
arbitrary decidability instance to the structure's mathematical meaning. -/
structure SpanningLinearForest (G : SimpleGraph V) where
  graph : SimpleGraph V
  le_original : graph ≤ G
  acyclic : graph.IsAcyclic
  degree_le_two : ∀ v, Nat.card (graph.neighborSet v) ≤ 2

namespace SpanningLinearForest

/-- All isolated vertices, available even when the original vertex type is empty. -/
def isolates (G : SimpleGraph V) : SpanningLinearForest G where
  graph := ⊥
  le_original := bot_le
  acyclic := isAcyclic_bot
  degree_le_two := by intro v; simp

/-- Number of actual connected components, with isolates counted separately. -/
noncomputable def componentCount (F : SpanningLinearForest G) : ℕ :=
  Nat.card F.graph.ConnectedComponent

/-- Minimum among actual spanning linear subgraphs of the original graph. -/
def IsMinimum (F : SpanningLinearForest G) : Prop :=
  ∀ F' : SpanningLinearForest G, F.componentCount ≤ F'.componentCount

/-- Well-ordering supplies a minimum without any extra graph hypothesis. -/
theorem exists_minimum (G : SimpleGraph V) [Finite V] :
    ∃ F : SpanningLinearForest G, F.IsMinimum := by
  classical
  have hex : ∃ n : ℕ, ∃ F : SpanningLinearForest G, F.componentCount = n :=
    ⟨(isolates G).componentCount, isolates G, rfl⟩
  obtain ⟨F, hF⟩ := Nat.find_spec hex
  refine ⟨F, fun F' => ?_⟩
  rw [hF]
  exact Nat.find_min' hex ⟨F', rfl⟩

/-- A selected minimum forest, using only classical choice. -/
noncomputable def minimum (G : SimpleGraph V) [Finite V] : SpanningLinearForest G :=
  Classical.choose (exists_minimum G)

theorem minimum_isMinimum (G : SimpleGraph V) [Finite V] : (minimum G).IsMinimum :=
  Classical.choose_spec (exists_minimum G)

/-- Every vertex lies in exactly one actual forest component. -/
theorem unique_component (F : SpanningLinearForest G) (v : V) :
    ∃! C : F.graph.ConnectedComponent, v ∈ C.supp := by
  refine ⟨F.graph.connectedComponentMk v, rfl, ?_⟩
  intro C hC
  exact hC.symm

/-- Distinct actual components have disjoint vertex sets. -/
theorem component_disjoint (F : SpanningLinearForest G)
    {C D : F.graph.ConnectedComponent} (hCD : C ≠ D) : Disjoint C.supp D.supp := by
  rw [Set.disjoint_left]
  intro v hvC hvD
  exact hCD (ConnectedComponent.eq_of_common_vertex hvC hvD)

variable [Fintype V]

/-- The stored degree condition is the usual finite graph degree bound. -/
theorem degree_bound (F : SpanningLinearForest G) [DecidableRel F.graph.Adj] :
    ∀ v, F.graph.degree v ≤ 2 := by
  intro v
  simpa only [Nat.card_eq_fintype_card, F.graph.card_neighborSet_eq_degree] using
    F.degree_le_two v

/-- Components partition the original vertices, so their count cannot exceed
the order of the original graph. -/
theorem componentCount_le_card (F : SpanningLinearForest G) :
    F.componentCount ≤ Fintype.card V := by
  simpa only [componentCount, Nat.card_eq_fintype_card] using
    Nat.card_le_card_of_surjective F.graph.connectedComponentMk Quot.mk_surjective

theorem componentCount_pos (F : SpanningLinearForest G) [Nonempty V] :
    0 < F.componentCount := Nat.card_pos

/-- The all-isolate forest counts every original vertex, including isolated
vertices of the ambient graph. -/
theorem isolates_componentCount (G : SimpleGraph V) :
    (isolates G).componentCount = Fintype.card V := by
  classical
  have hinj : Function.Injective (⊥ : SimpleGraph V).connectedComponentMk := by
    intro v w h
    exact reachable_bot.mp (ConnectedComponent.exact h)
  simpa only [componentCount, isolates, Nat.card_eq_fintype_card] using
    (Nat.card_congr (Equiv.ofBijective (⊥ : SimpleGraph V).connectedComponentMk
      ⟨hinj, Quot.mk_surjective⟩)).symm

/-- Extract a path in the original graph, with exactly the component's
vertices and exactly its forest edges. No simplicity or decomposition
conclusion is assumed by this interface. -/
theorem component_path (F : SpanningLinearForest G) (C : F.graph.ConnectedComponent) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧
      (∀ v, v ∈ p.support ↔ v ∈ C.supp) ∧
      (∀ v w, p.toSubgraph.Adj v w ↔ F.graph.Adj v w ∧ v ∈ C.supp) ∧
      Nat.card C = p.length + 1 := by
  classical
  obtain ⟨a, b, p, hp, hs, he, hc⟩ :=
    Erdos585.ForestPathInput.component_path F.degree_bound F.acyclic C
  refine ⟨a, b, p.mapLe F.le_original, hp.mapLe _, ?_, ?_, ?_⟩
  · simpa only [Walk.support_mapLe_eq_support] using hs
  · intro v w
    rw [Walk.adj_toSubgraph_mapLe]
    constructor
    · intro hvw
      exact ⟨hvw.adj_sub, (hs v).mp (by simpa using hvw.fst_mem)⟩
    · rintro ⟨hvw, hv⟩
      exact he v w hv hvw
  · simpa only [Walk.length_mapLe] using hc

/-- Chosen component data retain the exact original-graph meaning needed by
rotation and assembly interfaces. -/
structure ComponentPath (F : SpanningLinearForest G) (C : F.graph.ConnectedComponent) where
  start : V
  finish : V
  walk : G.Walk start finish
  simple : walk.IsPath
  support_exact : ∀ v, v ∈ walk.support ↔ v ∈ C.supp
  edges_exact : ∀ v w, walk.toSubgraph.Adj v w ↔ F.graph.Adj v w ∧ v ∈ C.supp
  card_eq_length_add_one : Nat.card C = walk.length + 1

theorem componentPath_nonempty (F : SpanningLinearForest G)
    (C : F.graph.ConnectedComponent) : Nonempty (F.ComponentPath C) := by
  obtain ⟨a, b, p, hp, hs, he, hc⟩ := F.component_path C
  exact ⟨⟨a, b, p, hp, hs, he, hc⟩⟩

/-- One coherent choice of a genuine path for every actual forest component. -/
noncomputable def componentPath (F : SpanningLinearForest G)
    (C : F.graph.ConnectedComponent) : F.ComponentPath C :=
  Classical.choice (F.componentPath_nonempty C)

/-- The chosen component paths cover every original vertex exactly once. -/
theorem componentPath_unique_cover (F : SpanningLinearForest G) (v : V) :
    ∃! C : F.graph.ConnectedComponent, v ∈ (F.componentPath C).walk.support := by
  simpa only [ComponentPath.support_exact] using F.unique_component v

/-- Supports of different chosen component paths are disjoint. -/
theorem componentPath_disjoint (F : SpanningLinearForest G)
    {C D : F.graph.ConnectedComponent} (hCD : C ≠ D) :
    List.Disjoint (F.componentPath C).walk.support (F.componentPath D).walk.support := by
  rw [List.disjoint_left]
  intro v hvC hvD
  exact Set.disjoint_left.mp (F.component_disjoint hCD)
    ((F.componentPath C).support_exact v |>.mp hvC)
    ((F.componentPath D).support_exact v |>.mp hvD)

/-- The chosen paths account for all forest edges and introduce no new
forest edge. The forest remains a subgraph of the original graph. -/
theorem componentPath_adj_union (F : SpanningLinearForest G) (v w : V) :
    F.graph.Adj v w ↔
      ∃ C : F.graph.ConnectedComponent, (F.componentPath C).walk.toSubgraph.Adj v w := by
  constructor
  · intro h
    exact ⟨F.graph.connectedComponentMk v,
      ((F.componentPath _).edges_exact v w).mpr ⟨h, rfl⟩⟩
  · rintro ⟨C, h⟩
    exact (((F.componentPath C).edges_exact v w).mp h).1

namespace ComponentPath

variable {F : SpanningLinearForest G} {C : F.graph.ConnectedComponent}

/-- The first endpoint is a genuine forest endpoint (or an isolate). -/
theorem start_degree_le_one (p : F.ComponentPath C) :
    Nat.card (F.graph.neighborSet p.start) ≤ 1 := by
  have hs : p.start ∈ C.supp := (p.support_exact _).mp p.walk.start_mem_support
  have hsub : F.graph.neighborSet p.start ⊆ {p.walk.snd} := by
    intro v hv
    exact (p.simple.snd_of_toSubgraph_adj ((p.edges_exact _ _).mpr ⟨hv, hs⟩)).symm
  have h := Set.ncard_le_ncard hsub (Set.finite_singleton _)
  simpa using h

/-- The opposite endpoint is also an endpoint in the actual forest. -/
theorem finish_degree_le_one (p : F.ComponentPath C) :
    Nat.card (F.graph.neighborSet p.finish) ≤ 1 := by
  have hs : p.finish ∈ C.supp := (p.support_exact _).mp p.walk.end_mem_support
  have hsub : F.graph.neighborSet p.finish ⊆ {p.walk.reverse.snd} := by
    intro v hv
    have ha : p.walk.toSubgraph.Adj p.finish v := (p.edges_exact _ _).mpr ⟨hv, hs⟩
    have hr : p.walk.reverse.toSubgraph.Adj p.finish v := by simpa using ha
    exact (p.simple.reverse.snd_of_toSubgraph_adj hr).symm
  have h := Set.ncard_le_ncard hsub (Set.finite_singleton _)
  simpa using h

end ComponentPath

/-- Two endpoint incidences per component. At an isolate the two distinct
tokens refer to the same physical original vertex. -/
abbrev EndpointToken (F : SpanningLinearForest G) := F.graph.ConnectedComponent × Bool

noncomputable def endpointVertex (F : SpanningLinearForest G) (t : F.EndpointToken) : V :=
  if t.2 then (F.componentPath t.1).finish else (F.componentPath t.1).start

theorem endpointVertex_mem_component (F : SpanningLinearForest G) (t : F.EndpointToken) :
    F.endpointVertex t ∈ t.1.supp := by
  rcases t with ⟨C, b⟩
  cases b
  · exact ((F.componentPath C).support_exact _).mp (F.componentPath C).walk.start_mem_support
  · exact ((F.componentPath C).support_exact _).mp (F.componentPath C).walk.end_mem_support

/-- The endpoint tokens refer only to actual endpoints or isolates. -/
theorem endpointVertex_degree_le_one (F : SpanningLinearForest G) (t : F.EndpointToken) :
    Nat.card (F.graph.neighborSet (F.endpointVertex t)) ≤ 1 := by
  rcases t with ⟨C, b⟩
  cases b
  · exact (F.componentPath C).start_degree_le_one
  · exact (F.componentPath C).finish_degree_le_one

omit [Fintype V] in
/-- Exactly two endpoint incidences per actual forest component. -/
theorem endpointToken_card (F : SpanningLinearForest G) :
    Nat.card F.EndpointToken = 2 * F.componentCount := by
  simp [EndpointToken, componentCount, Nat.card_prod, Nat.mul_comm]

/-- Number of endpoint incidences whose original vertices lie on a shore. -/
noncomputable def shoreEndpointCount (F : SpanningLinearForest G) (S : Set V) : ℕ :=
  Nat.card {t : F.EndpointToken // F.endpointVertex t ∈ S}

/-- Partitioning the original vertices partitions the endpoint incidences.
No bipartiteness or positivity is needed for this bookkeeping identity. -/
theorem shoreEndpointCount_add_compl (F : SpanningLinearForest G) (S : Set V) :
    F.shoreEndpointCount S + F.shoreEndpointCount Sᶜ = 2 * F.componentCount := by
  classical
  have h := Nat.card_congr (Equiv.sumCompl (fun t : F.EndpointToken => F.endpointVertex t ∈ S))
  rw [Nat.card_sum] at h
  exact h.trans F.endpointToken_card

/-- A physical endpoint cannot belong to two different components. -/
theorem endpointVertex_eq_component (F : SpanningLinearForest G)
    {s t : F.EndpointToken} (h : F.endpointVertex s = F.endpointVertex t) :
    s.1 = t.1 := by
  apply ConnectedComponent.eq_of_common_vertex (F.endpointVertex_mem_component s)
  rw [h]
  exact F.endpointVertex_mem_component t

/-- Each physical original vertex carries at most two endpoint incidences.
This bound retains the two copies at an isolate rather than discarding one. -/
theorem shoreEndpointCount_le_twice_card (F : SpanningLinearForest G) (S : Set V) :
    F.shoreEndpointCount S ≤ 2 * Nat.card S := by
  classical
  let f : {t : F.EndpointToken // F.endpointVertex t ∈ S} → S × Bool :=
    fun t => (⟨F.endpointVertex t.val, t.prop⟩, t.val.2)
  have hi : Function.Injective f := by
    intro s t h
    have hv : F.endpointVertex s.val = F.endpointVertex t.val :=
      congrArg (fun x : S × Bool => x.1.val) h
    have hb : s.val.2 = t.val.2 := congrArg (fun x : S × Bool => x.2) h
    apply Subtype.ext
    exact Prod.ext (F.endpointVertex_eq_component hv) hb
  have h := Nat.card_le_card_of_injective f hi
  simpa [shoreEndpointCount, Nat.card_prod, Nat.card_eq_fintype_card, Nat.mul_comm] using h

end SpanningLinearForest

end Erdos585.Attempt6
