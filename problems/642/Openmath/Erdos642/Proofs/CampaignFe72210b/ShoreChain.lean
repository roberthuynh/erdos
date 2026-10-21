import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphMarkov

/-! The actual two-step graph chain restricted to a bipartite shore. -/
namespace Erdos642.CampaignFe72210b
open SimpleGraph Matrix
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
private theorem transition_zero_of_not_adj (x y : V) (h : ¬G.Adj x y) :
    graphTransition G x y = 0 := by
  simp [graphTransition, SimpleGraph.adjMatrix_apply, h]

/-- Nonnegativity of the genuine two-step transition matrix. -/
theorem graphTransition_sq_nonneg (x y : V) : 0 ≤ (graphTransition G ^ 2) x y := by
  rw [pow_two, Matrix.mul_apply]
  exact Finset.sum_nonneg fun z _ =>
    mul_nonneg (graphTransition_nonneg G x z) (graphTransition_nonneg G z y)

/-- A genuine two-step walk from a shore cannot end outside that shore. -/
theorem graphTransition_sq_zero_outside {s t : Set V} (hbi : G.IsBipartiteWith s t)
    (x y : V) (hx : x ∈ s) (hy : y ∉ s) : (graphTransition G ^ 2) x y = 0 := by
  rw [pow_two, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hxz : G.Adj x z
  · have hz : z ∈ t := hbi.mem_of_mem_adj hx hxz
    have hzy : ¬G.Adj z y := by
      intro hadj
      exact hy (hbi.mem_of_mem_adj' hz hadj.symm)
    rw [transition_zero_of_not_adj G z y hzy, mul_zero]
  · rw [transition_zero_of_not_adj G x z hxz, zero_mul]

/-- Full row normalization of the literal squared graph transition matrix. -/
theorem graphTransition_sq_row_sum (hdeg : ∀ x : V, 0 < G.degree x) (x : V) :
    ∑ y, (graphTransition G ^ 2) x y = 1 := by
  simp only [pow_two, Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, graphTransition_row_sum G hdeg, mul_one]
  exact graphTransition_row_sum G hdeg x

variable (s : Set V) [DecidablePred (· ∈ s)]

/-- Actual two-step entries on the finite subtype of one shore. -/
noncomputable def shoreTransition : Matrix s s ℝ := fun x y =>
  (graphTransition G ^ 2) x.val y.val

omit [DecidablePred (· ∈ s)] in
theorem shoreTransition_nonneg (x y : s) : 0 ≤ shoreTransition G s x y :=
  graphTransition_sq_nonneg G x.val y.val

theorem shoreTransition_row_sum (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) (x : s) :
    ∑ y : s, shoreTransition G s x y = 1 := by
  have hz (y : V) (hy : y ∉ s) : (graphTransition G ^ 2) x.val y = 0 :=
    graphTransition_sq_zero_outside G hbi x.val y x.property hy
  unfold shoreTransition
  rw [← graphTransition_sq_row_sum G hdeg x.val]
  exact (Finset.sum_congr_set s (fun y => (graphTransition G ^ 2) x.val y)
    (fun y : s => (graphTransition G ^ 2) x.val y.val)
    (fun _ _ => rfl) hz).symm

                                                                                  
noncomputable def shoreChain (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) : Erdos642.FiniteMarkov.Chain s where
  transition := shoreTransition G s
  nonneg := shoreTransition_nonneg G s
  row_sum := shoreTransition_row_sum G s t hbi hdeg

end Erdos642.CampaignFe72210b
