import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

                                                                                     
                                                                                                     
                                                                           
namespace Erdos642.CloudT9_20261021.ThreeLedger

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
                                                                          
theorem three_ledger_points (P B : Finset V) (h : G.IsBipartiteWith (P : Set V) (B : Set V)) :
    (#G.edgeFinset : ℤ) - 3 * ((#P : ℤ) + #B) = (∑ p ∈ P, ((G.degree p : ℤ) - 3)) - 3 * #B := by
  have hsum : ∑ p ∈ P, G.degree p = #G.edgeFinset := isBipartiteWith_sum_degrees_eq_card_edges h
  have hsumZ : (∑ p ∈ P, (G.degree p : ℤ)) = (#G.edgeFinset : ℤ) := by exact_mod_cast hsum
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hsumZ]
  ring

omit [DecidableEq V] in
                                                                                 
theorem three_ledger_blocks (P B : Finset V) (h : G.IsBipartiteWith (P : Set V) (B : Set V)) :
    (#G.edgeFinset : ℤ) - 3 * ((#P : ℤ) + #B) = (∑ b ∈ B, ((G.degree b : ℤ) - 3)) - 3 * #P := by
  have hsum : ∑ b ∈ B, G.degree b = #G.edgeFinset := isBipartiteWith_sum_degrees_eq_card_edges' h
  have hsumZ : (∑ b ∈ B, (G.degree b : ℤ)) = (#G.edgeFinset : ℤ) := by exact_mod_cast hsum
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hsumZ]
  ring

omit [DecidableRel G.Adj] in
/-- When the two parts cover every vertex, `n = |P| + |B|` is the order of the graph. -/
theorem card_parts_eq_order (P B : Finset V) (h : G.IsBipartiteWith (P : Set V) (B : Set V))
    (hcover : P ∪ B = univ) : #P + #B = Fintype.card V := by
  have hdisj : Disjoint P B := Finset.disjoint_coe.mp h.disjoint
  rw [← Finset.card_union_of_disjoint hdisj, hcover, Finset.card_univ]

                                                                                 
theorem three_ledger (P B : Finset V) (h : G.IsBipartiteWith (P : Set V) (B : Set V))
    (hcover : P ∪ B = univ) :
    (#G.edgeFinset : ℤ) - 3 * Fintype.card V = (∑ p ∈ P, ((G.degree p : ℤ) - 3)) - 3 * #B := by
  have hn : ((#P : ℤ) + #B) = Fintype.card V := by
    exact_mod_cast card_parts_eq_order G P B h hcover
  rw [← hn]
  exact three_ledger_points G P B h

end Erdos642.CloudT9_20261021.ThreeLedger
