import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Erdos642.CampaignFe72210b
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- L5 component: close a simple path by an actual endpoint edge. -/
theorem close_path_isCycle (p : G.Walk v u) (hp : p.IsPath)
    (hl : 2 ≤ p.length) (h : G.Adj u v) : (Walk.cons h p).IsCycle := by
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · simpa using hp
  · simp only [Walk.length_cons]
    omega

/-- Closing the path retains exactly its vertex support. -/
theorem close_path_support (p : G.Walk v u) (h : G.Adj u v) (x : V) :
    x ∈ (Walk.cons h p).support ↔ x ∈ p.support := by
  simp only [Walk.support_cons, List.mem_cons]
  constructor
  · rintro (rfl | hx)
    · exact p.end_mem_support
    · exact hx
  · exact Or.inr

theorem close_path_length (p : G.Walk v u) (h : G.Adj u v) :
    (Walk.cons h p).length = p.length + 1 := by simp

/-- Actual host edges induced by the vertices visited by a walk. -/
noncomputable def supportEdges [Fintype V] (p : G.Walk u v) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter fun e => e ∈ G.edgeSet ∧
    e.lift ⟨fun a b => a ∈ p.support ∧ b ∈ p.support, by grind⟩

/-- The support edge finset counts literal host edges with both endpoints retained. -/
theorem mem_supportEdges [Fintype V] (p : G.Walk u v) (a b : V) :
    s(a, b) ∈ supportEdges p ↔ G.Adj a b ∧ a ∈ p.support ∧ b ∈ p.support := by
  classical
  simp [supportEdges]

/-- Distinct actual chords using mathlib's predicate. -/
noncomputable def chordEdges [Fintype V] (p : G.Walk u v) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter p.IsChord

theorem chordEdges_eq_sdiff [Fintype V] [DecidableEq V] (p : G.Walk u v) :
    chordEdges p = supportEdges p \ p.edges.toFinset := by
  classical
  ext e
  simp only [chordEdges, supportEdges, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_sdiff, List.mem_toFinset, Walk.IsChord]
  tauto

/-- L5 component: subtract cycle edges to count actual chords. -/
theorem many_chords_of_support_edges [Fintype V] (c : G.Walk u u)
    (hc : c.IsCycle) (he : 2 * c.length ≤ (supportEdges c).card) :
    c.length ≤ (chordEdges c).card := by
  classical
  have hcard : c.edges.toFinset.card = c.length := by
    rw [List.toFinset_card_of_nodup hc.isTrail.edges_nodup, Walk.length_edges]
  have h := Finset.card_le_card_sdiff_add_card (s := supportEdges c)
    (t := c.edges.toFinset)
  rw [← chordEdges_eq_sdiff, hcard] at h
  omega
end Erdos642.CampaignFe72210b
