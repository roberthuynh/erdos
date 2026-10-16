import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralHost
import Openmath.Erdos642.Proofs.CampaignFe72210b.FiniteMarkov

/-! Genuine simple-graph transition weights, not an assumed abstract walk law. -/
namespace Erdos642.CampaignFe72210b
open SimpleGraph
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem graphTransition_nonneg (x y : V) : 0 ≤ graphTransition G x y := by
  unfold graphTransition
  apply div_nonneg
  · simp only [SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  · positivity

theorem graphTransition_row_sum (hdeg : ∀ x : V, 0 < G.degree x) (x : V) :
    ∑ y, graphTransition G x y = 1 := by
  have hsum : (∑ y, G.adjMatrix ℝ x y) = (G.degree x : ℝ) := by
    simpa [Matrix.mulVec, dotProduct] using
      (G.adjMatrix_mulVec_const_apply (a := (1 : ℝ)) (v := x))
  simp only [graphTransition, ← Finset.sum_div]
  rw [hsum, div_self]
  exact_mod_cast Nat.ne_of_gt (hdeg x)

/-- The finite path-law chain of the actual ordinary graph walk. -/
noncomputable def graphChain (hdeg : ∀ x : V, 0 < G.degree x) :
    Erdos642.FiniteMarkov.Chain V where
  transition := graphTransition G
  nonneg := graphTransition_nonneg G
  row_sum := graphTransition_row_sum G hdeg

/-- Detailed balance before normalizing the degree measure to total mass one. -/
theorem graphTransition_degree_balance (hdeg : ∀ x : V, 0 < G.degree x)
    (x y : V) :
    (G.degree x : ℝ) * graphTransition G x y =
      (G.degree y : ℝ) * graphTransition G y x := by
  have hx : (G.degree x : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (hdeg x)
  have hy : (G.degree y : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (hdeg y)
  simp only [graphTransition]
  rw [mul_div_cancel₀ _ hx, mul_div_cancel₀ _ hy]
  simp only [SimpleGraph.adjMatrix_apply, G.adj_comm]

end Erdos642.CampaignFe72210b
