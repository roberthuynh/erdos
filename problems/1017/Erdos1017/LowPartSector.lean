import Erdos1017.GraphSelector
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Erdos1017
open scoped BigOperators
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- Counting ordered edges leaves at least the square of any one independent part. -/
theorem multipartite_edge_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (part : V → ι) (hG : ∀ u v, G.Adj u v ↔ part u ≠ part v) (r : ι) :
    2 * G.edgeFinset.card + (partSize part r)^2 ≤ (Fintype.card V)^2 := by
  have hd (v : V) : G.degree v + partSize part (part v) = Fintype.card V := by
    have hn : G.neighborFinset v = Finset.univ.filter (fun u => part u ≠ part v) := by
      ext u
      simp [hG, ne_comm]
    rw [← G.card_neighborFinset_eq_degree, hn]
    dsimp [partSize]
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (fun u => part u = part v)
    simpa [add_comm] using hc
  have hs : 2 * G.edgeFinset.card + ∑ v, partSize part (part v) = (Fintype.card V)^2 := by
    rw [← G.sum_degrees_eq_twice_card_edges, ← Finset.sum_add_distrib]
    simp [hd, pow_two]
  have hl : (partSize part r)^2 ≤ ∑ v, partSize part (part v) := by
    calc
      _ = ∑ v : V, if part v = r then partSize part r else 0 := by
        simp [Finset.sum_ite, partSize, pow_two]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v _
        by_cases h : part v = r <;> simp [h]
  omega

/-- The low-largest-part branch of the sharp affine bound, for actual graphs. -/
theorem low_part_sharp_affine (G : SimpleGraph V) [DecidableRel G.Adj]
    (part : V → ι) (hG : ∀ u v, G.Adj u v ↔ part u ≠ part v) (r : ι)
    (hr : 0 < partSize part r) (hmax : ∀ i, partSize part i ≤ partSize part r)
    (hsmall : 9 * partSize part r ≤ 2 * Fintype.card V) :
    ∃ P : FractionalPartition G,
      P.cost + (Real.sqrt 7 / 3) * (G.edgeFinset.card : ℝ) ≤
        (1 + Real.sqrt 7 / 3) * (Fintype.card V : ℝ)^2 / 4 := by
  have ha : (0 : ℝ) < partSize part r := by exact_mod_cast hr
  obtain ⟨P, hP⟩ := multipartite_partition_le_square ha G part hG
    (fun i => by exact_mod_cast hmax i)
  refine ⟨P, ?_⟩
  have he : (2 : ℝ) * G.edgeFinset.card + (partSize part r : ℝ)^2 ≤
      (Fintype.card V : ℝ)^2 := by exact_mod_cast multipartite_edge_bound G part hG r
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hs : (9 : ℝ) * partSize part r ≤ 2 * Fintype.card V := by exact_mod_cast hsmall
  have hs2 : (81 : ℝ) * (partSize part r : ℝ)^2 ≤ 4 * (Fintype.card V : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ (2 : ℝ) * Fintype.card V + 9 * partSize part r by positivity)]
  have hsq : (Real.sqrt 7)^2 = 7 := Real.sq_sqrt (by norm_num)
  have hroot : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg _
  have hroot_upper : Real.sqrt 7 ≤ (195 : ℝ)/73 := by nlinarith
  have hc : 0 ≤ 1 - Real.sqrt 7 / 6 := by nlinarith
  have hweighted := mul_le_mul_of_nonneg_left he (show 0 ≤ Real.sqrt 7 / 6 by positivity)
  have hsize := mul_le_mul_of_nonneg_left hs2 hc
  have hmargin := mul_nonneg (show 0 ≤ (195 : ℝ) - 73 * Real.sqrt 7 by linarith)
    (sq_nonneg (Fintype.card V : ℝ))
  nlinarith

end Erdos1017
