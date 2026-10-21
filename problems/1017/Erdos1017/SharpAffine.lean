import Erdos1017.WeightedSymmetrization

namespace Erdos1017
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every finite simple graph has an exact original-edge fractional clique
partition satisfying the sharp Turán-anchored affine bound. -/
theorem sharp_affine (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P : FractionalPartition G,
      P.cost+(Real.sqrt 7/3)*(G.edgeFinset.card : ℝ) ≤
        (1+Real.sqrt 7/3)*(Fintype.card V : ℝ)^2/4 := by
  obtain ⟨P,hP⟩ := weighted_graph_sharp G (fun _ => 1) (fun _ => zero_le_one)
  obtain ⟨Q,hQ⟩ := P.to_unit_graph G
  unfold graphBudget at hP
  rw [weightedEdges_one] at hP
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hP
  exact ⟨Q,by linarith⟩

theorem sharp_affine_statement : SharpAffineStatement (V := V) := by
  intro G _
  exact sharp_affine G

end Erdos1017
