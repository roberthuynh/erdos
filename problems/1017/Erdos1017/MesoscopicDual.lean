import Erdos1017.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-! Signed edge certificates for exact partitions. Negative weights require
exact loads; these statements do not assert bounds for fractional covers. -/
namespace Erdos1017.Mesoscopic
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def cell (w : V → V → ℝ) (S : Finset V) : ℝ :=
  (∑ u ∈ S, ∑ v ∈ S, w u v) / 2

noncomputable def total (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → V → ℝ) : ℝ :=
  (∑ u, ∑ v, if G.Adj u v then w u v else 0) / 2

/-- Weak duality proved directly by interchanging the finite exact-load sums. -/
theorem signed_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → V → ℝ) (hdiag : ∀ u, w u u = 0)
    (hclique : ∀ S : Finset V, G.IsClique (S : Set V) → cell w S ≤ 1)
    (P : FractionalPartition G) : total G w ≤ P.cost := by
  have local_sum (S : Finset V) :
      (∑ u ∈ S, ∑ v ∈ S, w u v) =
        ∑ u, ∑ v, if u ∈ S ∧ v ∈ S then w u v else 0 := by
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hload (u v : V) :
      w u v * (∑ S : Finset V, if u ∈ S ∧ v ∈ S then P.mass S else 0) =
        if G.Adj u v then w u v else 0 := by
    by_cases huv : G.Adj u v
    · rw [P.edge_load u v huv]; simp [huv]
    · by_cases heq : u = v
      · subst v; simp [hdiag]
      · rw [P.nonedge_load heq huv]; simp [huv]
  have he : (∑ S, P.mass S * cell w S) = total G w := by
    unfold cell total
    simp_rw [local_sum, ← mul_div_assoc]
    rw [← Finset.sum_div]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [← hload u v, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> ring
  rw [← he]
  apply Finset.sum_le_sum
  intro S _
  by_cases h : P.mass S = 0
  · simp [h]
  · exact mul_le_of_le_one_right (P.nonneg S) (hclique S (P.supported S h).1)

/-- Integral partitions use actual cliques, with exactly one member containing
each original edge. This simultaneously states edge disjointness and coverage. -/
structure IntegralPartition (G : SimpleGraph V) where
  pieces : Finset (Finset V)
  supported : ∀ S ∈ pieces, G.IsClique (S : Set V) ∧ 2 ≤ S.card
  unique_edge : ∀ u v, G.Adj u v → ∃! S, S ∈ pieces ∧ u ∈ S ∧ v ∈ S

noncomputable def IntegralPartition.fractional {G : SimpleGraph V}
    (P : IntegralPartition G) : FractionalPartition G where
  mass S := if S ∈ P.pieces then 1 else 0
  nonneg S := by split_ifs <;> norm_num
  supported S h := P.supported S (by by_contra hn; simp [hn] at h)
  edge_load u v huv := by
    obtain ⟨T, hT, huniq⟩ := P.unique_edge u v huv
    have he (S : Finset V) :
        (if u ∈ S ∧ v ∈ S then (if S ∈ P.pieces then (1:ℝ) else 0) else 0) =
          if S = T then 1 else 0 := by
      by_cases hST : S = T
      · subst S; simp [hT.1, hT.2.1, hT.2.2]
      · have hn : ¬ (S ∈ P.pieces ∧ u ∈ S ∧ v ∈ S) :=
          fun h => hST (huniq S h)
        simp only [hST, if_false]
        split_ifs <;> simp_all
    simp_rw [he]
    simp

theorem IntegralPartition.fractional_cost {G : SimpleGraph V}
    (P : IntegralPartition G) : P.fractional.cost = (P.pieces.card : ℝ) := by
  simp [FractionalPartition.cost, IntegralPartition.fractional]

theorem integral_signed_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → V → ℝ) (hdiag : ∀ u, w u u = 0)
    (hclique : ∀ S : Finset V, G.IsClique (S : Set V) → cell w S ≤ 1)
    (P : IntegralPartition G) : total G w ≤ (P.pieces.card : ℝ) := by
  simpa only [P.fractional_cost] using signed_lower G w hdiag hclique P.fractional

/-- The integral definition is nonvacuous for every finite simple graph:
the collection of its individual original edges is a partition. -/
noncomputable def edgePartition (G : SimpleGraph V) [DecidableRel G.Adj] :
    IntegralPartition G where
  pieces := G.cliqueFinset 2
  supported S hS := by
    obtain ⟨hc, hn⟩ := G.mem_cliqueFinset_iff.mp hS
    exact ⟨hc, hn.ge⟩
  unique_edge u v huv := by
    have hcard : ({u,v} : Finset V).card=2 := by simp [huv.ne]
    have hcl : G.IsClique (({u,v} : Finset V) : Set V) := by
      simpa only [Finset.coe_pair, SimpleGraph.isClique_pair] using (fun _ => huv)
    refine ⟨{u,v}, ⟨G.mem_cliqueFinset_iff.mpr ⟨hcl,hcard⟩, by simp, by simp⟩, ?_⟩
    intro S hS
    have hc := (G.mem_cliqueFinset_iff.mp hS.1).2
    have hsub : ({u,v} : Finset V) ⊆ S := by
      simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using hS.2
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- All eight independent-part cases, with arbitrary core-clique order. -/
theorem four_part_cell (a b d r : ℕ) (ha : a ≤ 1) (hb : b ≤ 1) (hd : d ≤ 1) :
    (a:ℝ)*b + (2:ℝ)/3*a*r - (2:ℝ)/3*b*r - (1:ℝ)/6*r*(r-1) +
      d*a - d*b - (2:ℝ)/3*d*r ≤ 1 := by
  have hr : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hrr : (0:ℝ) ≤ (r:ℝ)*(r-1) := by
    by_cases hz : r = 0
    · simp [hz]
    · have : (1:ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
      exact mul_nonneg hr (by linarith)
  have hp : (0:ℝ) ≤ ((r:ℝ)-2)*((r:ℝ)-3) := by
    by_cases h : r ≤ 2
    · have : (r:ℝ) ≤ 2 := by exact_mod_cast h
      nlinarith
    · have : (3:ℝ) ≤ r := by exact_mod_cast (show 3 ≤ r by omega)
      exact mul_nonneg (by linarith) (by linarith)
  interval_cases a <;> interval_cases b <;> interval_cases d <;>
    norm_num <;> nlinarith

end Erdos1017.Mesoscopic
