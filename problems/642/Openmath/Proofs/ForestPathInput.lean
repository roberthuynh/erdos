import Openmath.Proofs.CommonHostCompletion
import Mathlib.Combinatorics.SimpleGraph.Acyclic

   
                                                             

                                                                               
                                                                             
  

namespace Erdos585.ForestPathInput

open SimpleGraph SimpleGraph.Walk

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Degree at most two forbids three distinct neighbors. -/
theorem no_three_neighbors (hdeg : ∀ v, G.degree v ≤ 2) {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  classical
  have hs : ({a, b, c} : Finset V) ⊆ G.neighborFinset v := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact (G.mem_neighborFinset v _).mpr ha
    · exact (G.mem_neighborFinset v _).mpr hb
    · exact (G.mem_neighborFinset v _).mpr hc
  have hh := Finset.card_le_card hs
  have hn : ({a, b, c} : Finset V).card = 3 := by simp [hab, hac, hbc]
  rw [hn, G.card_neighborFinset_eq_degree] at hh
  have := hdeg v
  omega

/-- A connected finite graph of maximum degree two has a spanning simple path. -/
theorem exists_spanning_path (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ ∀ w, w ∈ p.support := by
  classical
  let : Nonempty V := hconn.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ := exists_isPath_forall_isPath_length_le_length G
  have hclosed : ∀ {a b}, a ∈ p.support → G.Adj a b → b ∈ p.support := by
    intro a b ha hab
    by_contra hb
    obtain ⟨k, hk, hkle⟩ := Walk.mem_support_iff_exists_getVert.mp ha
    by_cases hk0 : k = 0
    · subst k
      have hab' : G.Adj u b := by simpa only [← hk, getVert_zero] using hab
      have hh := hmax b v (p.cons hab'.symm) (hp.cons hb)
      simp only [Walk.length_cons] at hh
      omega
    by_cases hkl : k = p.length
    · subst k
      have hab' : G.Adj v b := by simpa only [← hk, getVert_length] using hab
      have hh := hmax u b (p.concat hab') (hp.concat hb hab')
      simp only [Walk.length_concat] at hh
      omega
    have hkm : k - 1 + 1 = k := by omega
    have hleft : G.Adj a (p.getVert (k - 1)) := by
      have hh := (p.adj_getVert_succ (by omega : k - 1 < p.length)).symm
      simpa only [hkm, hk] using hh
    have hright : G.Adj a (p.getVert (k + 1)) := by
      simpa only [hk] using p.adj_getVert_succ (by omega : k < p.length)
    have hne : p.getVert (k - 1) ≠ p.getVert (k + 1) := by
      intro hh
      have := hp.getVert_injOn (by change k - 1 ≤ p.length; omega)
        (by change k + 1 ≤ p.length; omega) hh
      omega
    exact no_three_neighbors hdeg hleft hright hab hne
      (fun h => hb (h ▸ p.getVert_mem_support (k - 1)))
      (fun h => hb (h ▸ p.getVert_mem_support (k + 1)))
  have hwalk : ∀ {a b} (q : G.Walk a b), a ∈ p.support → b ∈ p.support := by
    intro a b q
    induction q with
    | nil => exact id
    | cons hadj q ih => exact fun ha => ih (hclosed ha hadj)
  exact ⟨u, v, p, hp, fun w => hwalk (hconn u w).some p.start_mem_support⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- In a tree, every edge of the graph lies on any spanning simple path. -/
theorem spanning_path_edges (hconn : G.Connected) (hacyc : G.IsAcyclic)
    {u v : V} (p : G.Walk u v) (hs : ∀ w, w ∈ p.support) :
    ∀ a b, G.Adj a b → p.toSubgraph.Adj a b := by
  let f : p.toSubgraph.coe →g p.toSubgraph.spanningCoe :=
    ⟨Subtype.val, fun h => h⟩
  have hf : Function.Surjective f := fun w => ⟨⟨w, by simpa using hs w⟩, rfl⟩
  have hpc : p.toSubgraph.spanningCoe.Connected := p.toSubgraph_connected.coe.map f hf
  have hle : G ≤ p.toSubgraph.spanningCoe :=
    (isTree_iff_minimal_connected.mp ⟨hconn, hacyc⟩).2 hpc p.toSubgraph.spanningCoe_le
  exact fun _ _ h => hle h

/-- A spanning simple path accounts for every vertex exactly once. -/
theorem spanning_path_card {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hs : ∀ w, w ∈ p.support) : Fintype.card V = p.length + 1 := by
  classical
  have hall : p.support.toFinset = Finset.univ := by ext w; simp [hs w]
  have hc := List.toFinset_card_of_nodup hp.support_nodup
  rw [hall, Finset.card_univ, length_support] at hc
  exact hc

/-- Extract an actual original-graph path traversing exactly a connected component. -/
theorem component_path (hdeg : ∀ v, G.degree v ≤ 2) (hacyc : G.IsAcyclic)
    (C : G.ConnectedComponent) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧
      (∀ w, w ∈ p.support ↔ w ∈ C.supp) ∧
      (∀ a b, a ∈ C.supp → G.Adj a b → p.toSubgraph.Adj a b) ∧
      Nat.card C = p.length + 1 := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  have hd : ∀ w : C, C.toSimpleGraph.degree w ≤ 2 := by
    intro w
    have hf : Function.Injective (fun x : C.toSimpleGraph.neighborSet w =>
        (⟨x.val.val, x.prop⟩ : G.neighborSet w.val)) := by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      have hv : a.val.val = b.val.val :=
        congrArg (fun z : G.neighborSet w.val => z.val) h
      exact hv
    calc
      C.toSimpleGraph.degree w = Fintype.card (C.toSimpleGraph.neighborSet w) :=
        (C.toSimpleGraph.card_neighborSet_eq_degree w).symm
      _ ≤ Fintype.card (G.neighborSet w.val) := Fintype.card_le_of_injective _ hf
      _ = G.degree w.val := G.card_neighborSet_eq_degree w.val
      _ ≤ 2 := hdeg _
  obtain ⟨u, v, p, hp, hs⟩ := exists_spanning_path C.connected_toSimpleGraph hd
  let q := p.map C.toSimpleGraph_hom
  have hq : q.IsPath := hp.map (by intro a b h; exact Subtype.ext h)
  have hqs : ∀ w, w ∈ q.support ↔ w ∈ C.supp := by
    intro w
    simp only [q, Walk.support_map, List.mem_map]
    constructor
    · rintro ⟨z, _, rfl⟩
      exact z.prop
    · intro hw
      exact ⟨⟨w, hw⟩, hs _, rfl⟩
  have he := spanning_path_edges C.connected_toSimpleGraph
    (hacyc.isTree_connectedComponent C).isAcyclic p hs
  have hqe : ∀ a b, a ∈ C.supp → G.Adj a b → q.toSubgraph.Adj a b := by
    intro a b ha hab
    have hb := C.mem_supp_of_adj_mem_supp ha hab
    have hed := he ⟨a, ha⟩ ⟨b, hb⟩ hab
    obtain ⟨i, hi, hil⟩ := p.toSubgraph_adj_iff.mp hed
    apply q.toSubgraph_adj_iff.mpr
    refine ⟨i, ?_, by simpa [q] using hil⟩
    have hh := congrArg (Sym2.map (fun z : C => z.val)) hi
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
      q, Walk.getVert_map]
    change (↑(p.getVert i) = a ∧ ↑(p.getVert (i + 1)) = b) ∨
      (↑(p.getVert i) = b ∧ ↑(p.getVert (i + 1)) = a)
    simpa [Sym2.map_mk, Sym2.eq, Sym2.rel_iff'] using hh
  refine ⟨u.val, v.val, q, hq, hqs, hqe, ?_⟩
  rw [Nat.card_eq_fintype_card]
  change Fintype.card C = (p.map C.toSimpleGraph_hom).length + 1
  simpa only [Walk.length_map] using spanning_path_card p hp hs

end Erdos585.ForestPathInput
