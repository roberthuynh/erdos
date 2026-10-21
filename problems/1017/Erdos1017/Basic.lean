import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Exact original-edge fractional clique partitions. No graph bound is assumed. -/
namespace Erdos1017
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite nonnegative measure on cliques, with exactly unit load on every original edge. -/
structure FractionalPartition (G : SimpleGraph V) where
  mass : Finset V → ℝ
  nonneg : ∀ s, 0 ≤ mass s
  supported : ∀ s, mass s ≠ 0 → G.IsClique (s : Set V) ∧ 2 ≤ s.card
  edge_load : ∀ u v, G.Adj u v → ∑ s : Finset V, (if u ∈ s ∧ v ∈ s then mass s else 0) = 1

noncomputable def FractionalPartition.cost {G : SimpleGraph V} (P : FractionalPartition G) : ℝ :=
  ∑ s, P.mass s

/-- The proposition proved by sharp_affine_statement. -/
noncomputable def SharpAffineStatement : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj], ∃ P : FractionalPartition G,
    P.cost + (Real.sqrt 7 / 3) * (G.edgeFinset.card : ℝ) ≤
      (1 + Real.sqrt 7 / 3) * (Fintype.card V : ℝ) ^ 2 / 4

theorem FractionalPartition.cost_nonneg {G : SimpleGraph V} (P : FractionalPartition G) :
    0 ≤ P.cost := Finset.sum_nonneg (fun s _ => P.nonneg s)

theorem FractionalPartition.nonedge_load {G : SimpleGraph V} (P : FractionalPartition G)
    {u v : V} (hne : u ≠ v) (h : ¬ G.Adj u v) :
    ∑ s : Finset V, (if u ∈ s ∧ v ∈ s then P.mass s else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  split_ifs with hs
  · by_contra hm
    exact h ((P.supported s hm).1 hs.1 hs.2 hne)
  · rfl

/-- Convex combinations preserve every original-edge equality, not merely total edge mass. -/
noncomputable def FractionalPartition.mix {G : SimpleGraph V}
    (P Q : FractionalPartition G) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    FractionalPartition G where
  mass s := t * P.mass s + (1-t) * Q.mass s
  nonneg s := add_nonneg (mul_nonneg ht (P.nonneg s))
    (mul_nonneg (sub_nonneg.mpr ht1) (Q.nonneg s))
  supported s hs := by
    by_cases hp : P.mass s = 0
    · have hq : Q.mass s ≠ 0 := by intro hq; simp [hp, hq] at hs
      exact Q.supported s hq
    · exact P.supported s hp
  edge_load u v huv := by
    have hid (s : Finset V) :
        (if u ∈ s ∧ v ∈ s then t * P.mass s + (1-t) * Q.mass s else 0) =
        t * (if u ∈ s ∧ v ∈ s then P.mass s else 0) +
        (1-t) * (if u ∈ s ∧ v ∈ s then Q.mass s else 0) := by split_ifs <;> ring
    simp_rw [hid]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      P.edge_load u v huv, Q.edge_load u v huv]
    ring

theorem FractionalPartition.mix_cost {G : SimpleGraph V}
    (P Q : FractionalPartition G) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (P.mix Q t ht ht1).cost = t * P.cost + (1-t) * Q.cost := by
  simp [FractionalPartition.cost, FractionalPartition.mix, Finset.sum_add_distrib,
    Finset.mul_sum]

end Erdos1017
