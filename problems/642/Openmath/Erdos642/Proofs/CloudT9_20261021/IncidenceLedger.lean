import Openmath.Erdos642.Proofs.CampaignFe72210b.FinitePruning
import Openmath.Erdos642.Proofs.CampaignFe72210b.CycleSupport
import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralHost
import Mathlib.Combinatorics.SimpleGraph.Bipartite

                                                                                          
                                                                                                 
                                                                                                
                                                                                
namespace Erdos642.CloudT9_20261021.IncidenceLedger

open SimpleGraph Finset Erdos642.CampaignFe72210b

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem degree_eq_ncard_neighborSet (H : SimpleGraph V) [DecidableRel H.Adj] (x : V) :
    H.degree x = (H.neighborSet x).ncard := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, card_neighborSet_eq_degree]

omit [Fintype V] [DecidableRel G.Adj] in
theorem card_edges_toFinset {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
    #c.edges.toFinset = c.length := by
  rw [List.toFinset_card_of_nodup hc.isTrail.edges_nodup, Walk.length_edges]

/-- The cycle as a spanning simple graph on `V`. -/
abbrev cycleGraph {u : V} (c : G.Walk u u) : SimpleGraph V := c.toSubgraph.spanningCoe

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem cycleGraph_le {u : V} (c : G.Walk u u) : cycleGraph G c ≤ G :=
  c.toSubgraph.spanningCoe_le

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem cycleGraph_isBipartiteWith {P B : Finset V}
    (h : G.IsBipartiteWith (P : Set V) (B : Set V)) {u : V} (c : G.Walk u u) :
    (cycleGraph G c).IsBipartiteWith (P : Set V) (B : Set V) :=
  ⟨h.disjoint, fun _ _ hab => h.mem_of_adj (cycleGraph_le G c hab)⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every vertex of a simple cycle has exactly two cycle neighbours; others have none. -/
theorem ncard_neighborSet_cycleGraph {u : V} (c : G.Walk u u) (hc : c.IsCycle) (x : V) :
    ((cycleGraph G c).neighborSet x).ncard = if x ∈ c.support then 2 else 0 := by
  split_ifs with hx
  · exact hc.ncard_neighborSet_toSubgraph_eq_two hx
  · have hempty : (cycleGraph G c).neighborSet x = ∅ := by
      ext y
      simp only [mem_neighborSet, Set.mem_empty_iff_false, iff_false]
      intro hxy
      exact hx ((c.mem_verts_toSubgraph).mp (Subgraph.Adj.fst_mem hxy))
    rw [hempty, Set.ncard_empty]

omit [DecidableRel G.Adj] in
theorem sum_degree_cycleGraph {u : V} (c : G.Walk u u) (hc : c.IsCycle) (T : Finset V)
    [DecidableRel (cycleGraph G c).Adj] :
    ∑ x ∈ T, (cycleGraph G c).degree x = 2 * #(c.support.toFinset ∩ T) := by
  have hzero : ∀ x ∈ T, x ∉ c.support.toFinset ∩ T → (cycleGraph G c).degree x = 0 := by
    intro x hxT hx
    rw [degree_eq_ncard_neighborSet, ncard_neighborSet_cycleGraph G c hc, if_neg]
    intro hs
    exact hx (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hs, hxT⟩)
  have htwo : ∀ x ∈ c.support.toFinset ∩ T, (cycleGraph G c).degree x = 2 := by
    intro x hx
    rw [degree_eq_ncard_neighborSet, ncard_neighborSet_cycleGraph G c hc,
      if_pos (List.mem_toFinset.mp (Finset.mem_inter.mp hx).1)]
  rw [← Finset.sum_subset Finset.inter_subset_right hzero, Finset.sum_congr rfl htwo,
    Finset.sum_const, smul_eq_mul, mul_comm]

omit [DecidableRel G.Adj] in
/-- An incidence cycle alternates: its length is twice its number of blocks and twice its
number of points. -/
theorem length_eq_two_mul_card_inter {P B : Finset V}
    (h : G.IsBipartiteWith (P : Set V) (B : Set V)) {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
    c.length = 2 * #(c.support.toFinset ∩ B) ∧ c.length = 2 * #(c.support.toFinset ∩ P) := by
  classical
  have hbip := cycleGraph_isBipartiteWith G h c
  have hE : #(cycleGraph G c).edgeFinset = c.length := by
    rw [← card_edges_toFinset G c hc]
    congr 1
    ext e
    rw [mem_edgeFinset, List.mem_toFinset]
    change e ∈ c.toSubgraph.spanningCoe.edgeSet ↔ _
    rw [Subgraph.edgeSet_spanningCoe, c.mem_edges_toSubgraph]
  have hB := isBipartiteWith_sum_degrees_eq_card_edges' hbip
  have hP := isBipartiteWith_sum_degrees_eq_card_edges hbip
  rw [sum_degree_cycleGraph G c hc, hE] at hB hP
  exact ⟨hB.symm, hP.symm⟩

/-- The host edges on the cycle's vertex set are the edges of the repo's `mask`. -/
theorem supportEdges_eq_mask_edgeFinset {u : V} (c : G.Walk u u) :
    supportEdges c = (mask G c.support.toFinset).edgeFinset := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [mem_supportEdges, mem_edgeFinset, mem_edgeSet]
    change _ ↔ G.Adj a b ∧ a ∈ c.support.toFinset ∧ b ∈ c.support.toFinset
    simp only [List.mem_toFinset]

/-- Block-side count of the host edges on the cycle's vertex set `S`:
`e(G[S]) = Σ_{b ∈ S ∩ B} |N(b) ∩ S|`. -/
theorem card_supportEdges {P B : Finset V} (h : G.IsBipartiteWith (P : Set V) (B : Set V))
    {u : V} (c : G.Walk u u) :
    #(supportEdges c) =
      ∑ b ∈ c.support.toFinset ∩ B, #(G.neighborFinset b ∩ c.support.toFinset) := by
  set S := c.support.toFinset with hS
  have hbip : (mask G S).IsBipartiteWith (P : Set V) (B : Set V) :=
    ⟨h.disjoint, fun _ _ hab => h.mem_of_adj (mask_le G S hab)⟩
  rw [supportEdges_eq_mask_edgeFinset, ← hS, ← isBipartiteWith_sum_degrees_eq_card_edges' hbip]
  have hdeg : ∀ b, (mask G S).degree b = if b ∈ S then #(G.neighborFinset b ∩ S) else 0 := by
    intro b
    rw [← card_neighborFinset_eq_degree]
    split_ifs with hb
    · congr 1
      ext y
      simp only [mem_neighborFinset, Finset.mem_inter]
      change (G.Adj b y ∧ b ∈ S ∧ y ∈ S) ↔ _
      tauto
    · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro y hy
      rw [mem_neighborFinset] at hy
      exact hb hy.2.1
  have hzero : ∀ b ∈ B, b ∉ S ∩ B → (mask G S).degree b = 0 := by
    intro b hbB hb
    rw [hdeg, if_neg]
    intro hbS
    exact hb (Finset.mem_inter.mpr ⟨hbS, hbB⟩)
  rw [← Finset.sum_subset Finset.inter_subset_right hzero]
  refine Finset.sum_congr rfl ?_
  intro b hb
  rw [hdeg, if_pos (Finset.mem_inter.mp hb).1]

                                                                                      
theorem card_chordEdges_eq {P B : Finset V} (h : G.IsBipartiteWith (P : Set V) (B : Set V))
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
    (#(chordEdges c) : ℤ) =
      ∑ b ∈ c.support.toFinset ∩ B, ((#(G.neighborFinset b ∩ c.support.toFinset) : ℤ) - 2) := by
  have hsub : c.edges.toFinset ⊆ supportEdges c := by
    intro e he
    rw [List.mem_toFinset] at he
    induction e using Sym2.inductionOn with
    | _ a b =>
      exact (mem_supportEdges c a b).mpr
        ⟨c.adj_of_mem_edges he, c.fst_mem_support_of_mem_edges he, c.snd_mem_support_of_mem_edges he⟩
  have hle : c.length ≤ #(supportEdges c) := by
    rw [← card_edges_toFinset G c hc]
    exact Finset.card_le_card hsub
  have hcard : #(chordEdges c) = #(supportEdges c) - c.length := by
    rw [chordEdges_eq_sdiff, Finset.card_sdiff_of_subset hsub, card_edges_toFinset G c hc]
  have hlen : (c.length : ℤ) = 2 * #(c.support.toFinset ∩ B) := by
    exact_mod_cast (length_eq_two_mul_card_inter G h c hc).1
  have hcardZ : (#(chordEdges c) : ℤ) = (#(supportEdges c) : ℤ) - c.length := by
    rw [hcard, Nat.cast_sub hle]
  rw [hcardZ, card_supportEdges G h c, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    hlen]
  push_cast
  ring

/-- The exact richness condition: `|c| ≤ #chords` iff `Σ_{b ∈ S ∩ B} (|N(b) ∩ S| − 4) ≥ 0`. -/
theorem rich_iff_ledger {P B : Finset V} (h : G.IsBipartiteWith (P : Set V) (B : Set V))
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
    c.length ≤ #(chordEdges c) ↔
      0 ≤ ∑ b ∈ c.support.toFinset ∩ B, ((#(G.neighborFinset b ∩ c.support.toFinset) : ℤ) - 4) := by
  have h1 := card_chordEdges_eq G h c hc
  have h2 : (c.length : ℤ) = 2 * #(c.support.toFinset ∩ B) := by
    exact_mod_cast (length_eq_two_mul_card_inter G h c hc).1
  have h3 : ∑ b ∈ c.support.toFinset ∩ B, ((#(G.neighborFinset b ∩ c.support.toFinset) : ℤ) - 4) =
      (∑ b ∈ c.support.toFinset ∩ B, ((#(G.neighborFinset b ∩ c.support.toFinset) : ℤ) - 2)) -
        2 * #(c.support.toFinset ∩ B) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul]
    ring
  rw [h3, ← h1, ← h2]
  omega

/-- A nonnegative ledger on some cycle gives the repo's `HasRichCycle`. -/
theorem hasRichCycle_of_ledger {P B : Finset V} (h : G.IsBipartiteWith (P : Set V) (B : Set V))
    {u : V} (c : G.Walk u u) (hc : c.IsCycle)
    (hsum : 0 ≤ ∑ b ∈ c.support.toFinset ∩ B,
      ((#(G.neighborFinset b ∩ c.support.toFinset) : ℤ) - 4)) : HasRichCycle G :=
  ⟨u, c, hc, (rich_iff_ledger G h c hc).mpr hsum⟩

end Erdos642.CloudT9_20261021.IncidenceLedger
