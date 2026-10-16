import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphMarkov

/-! Exact degree normalization for the genuine graph random walk. -/
namespace Erdos642.CampaignFe72210b
open SimpleGraph Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem degree_sqrt_pos (hdeg : ∀ x : V, 0 < G.degree x) (x : V) :
    0 < Real.sqrt (G.degree x : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hdeg x)

theorem graphTransition_normalized (hdeg : ∀ x : V, 0 < G.degree x) (x y : V) :
    graphTransition G x y =
      (Real.sqrt (G.degree y : ℝ) / Real.sqrt (G.degree x : ℝ)) *
        normalizedAdjacency G x y := by
  have hx := ne_of_gt (degree_sqrt_pos G hdeg x)
  have hy := ne_of_gt (degree_sqrt_pos G hdeg y)
  have hsq : Real.sqrt (G.degree x : ℝ)^2 = (G.degree x : ℝ) :=
    Real.sq_sqrt (by positivity)
  unfold graphTransition normalizedAdjacency
  have hd : (G.degree x : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hdeg x)
  field_simp
  rw [hsq]

/-- Exact entrywise similarity, for every power including time zero. -/
theorem graphTransition_pow_normalized (hdeg : ∀ x : V, 0 < G.degree x)
    (n : ℕ) (x y : V) :
    (graphTransition G ^ n) x y =
      (Real.sqrt (G.degree y : ℝ) / Real.sqrt (G.degree x : ℝ)) *
        (normalizedAdjacency G ^ n) x y := by
  induction n generalizing x y with
  | zero =>
    by_cases hxy : x = y
    · subst y
      simp [ne_of_gt (degree_sqrt_pos G hdeg x)]
    · simp [Matrix.one_apply, hxy]
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [ih, graphTransition_normalized G hdeg]
    have hx := ne_of_gt (degree_sqrt_pos G hdeg x)
    have hz := ne_of_gt (degree_sqrt_pos G hdeg z)
    field_simp
    <;> ring

theorem normalizedAdjacency_isHermitian : (normalizedAdjacency G).IsHermitian := by
  ext x y
  simp [Matrix.conjTranspose_apply, normalizedAdjacency, SimpleGraph.adjMatrix_apply,
    G.adj_comm, mul_comm]

end Erdos642.CampaignFe72210b
