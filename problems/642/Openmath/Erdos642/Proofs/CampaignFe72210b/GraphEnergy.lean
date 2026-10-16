import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphNormalization

/-! The elementary degree bound for the genuine two-step graph transition
and the squared normalized-adjacency diagonal. -/

namespace Erdos642.CampaignFe72210b

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- A positive lower degree bound controls every ordinary transition entry. -/
theorem transition_entry_le (d : ℝ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ)) (x y : V) :
    graphTransition G x y ≤ 1 / d := by
  unfold graphTransition
  simp only [SimpleGraph.adjMatrix_apply]
  split_ifs
  · exact one_div_le_one_div_of_le hd (hmin x)
  · simp only [zero_div]
    positivity

/-- The actual normalized-adjacency two-step diagonal is at most the reciprocal
of a positive lower bound on all graph degrees. -/
theorem normalizedAdjacency_sq_diag_le (d : ℝ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ)) (x : V) :
    (normalizedAdjacency G ^ 2) x x ≤ 1 / d := by
  classical
  have hdeg : ∀ y : V, 0 < G.degree y := by
    intro y
    exact_mod_cast lt_of_lt_of_le hd (hmin y)
  have hdiag : (graphTransition G ^ 2) x x =
      (normalizedAdjacency G ^ 2) x x := by
    simpa only [div_self (ne_of_gt (degree_sqrt_pos G hdeg x)), one_mul] using
      graphTransition_pow_normalized G hdeg 2 x x
  calc
    (normalizedAdjacency G ^ 2) x x = (graphTransition G ^ 2) x x := hdiag.symm
    _ = ∑ z, graphTransition G x z * graphTransition G z x := by
      rw [pow_two, Matrix.mul_apply]
    _ ≤ ∑ z, graphTransition G x z * (1 / d) := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left (transition_entry_le G d hd hmin z x)
        (graphTransition_nonneg G x z)
    _ = (∑ z, graphTransition G x z) * (1 / d) := (Finset.sum_mul _ _ _).symm
    _ = 1 / d := by rw [graphTransition_row_sum G hdeg x, one_mul]

end Erdos642.CampaignFe72210b
