import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.FourthReturnExpansion

/-! Actual local codegree incidence, before any avoidance density input. -/
namespace Erdos642.CampaignFe72210bContinuation3.LocalCodegreeIncidence
open FourthReturnExpansion
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

 theorem common_card_as_sum (v w : V) :
    (Fintype.card (G.commonNeighbors v w) : ℝ) =
      ∑ x ∈ G.neighborFinset v, if G.Adj w x then (1:ℝ) else 0 := by
  rw [← commonNeighborFinset_card]
  have he : commonNeighborFinset G v w =
      (G.neighborFinset v).filter (fun x => G.Adj w x) := by
    ext x
    simp
  rw [he, Finset.natCast_card_filter]

/-- Double count genuine length-two walks from v, retaining original degrees. -/
 theorem total_common_card (v : V) :
    (∑ w : V, (Fintype.card (G.commonNeighbors v w) : ℝ)) =
      ∑ x ∈ G.neighborFinset v, (G.degree x : ℝ) := by
  simp_rw [common_card_as_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have he : Finset.univ.filter (fun w => G.Adj w x) = G.neighborFinset x := by
    ext w
    simp [G.adj_comm]
  rw [← Finset.natCast_card_filter, he, SimpleGraph.card_neighborFinset_eq_degree]

/-- The off-diagonal local incidence mass is bounded without density or moment premises. -/
 theorem offdiag_common_mass_le (v : V) (Δ : ℕ) (hmax : ∀ x, G.degree x ≤ Δ) :
    (∑ w ∈ Finset.univ.erase v, (Fintype.card (G.commonNeighbors v w) : ℝ)) ≤
      (G.degree v : ℝ)*(Δ:ℝ) := by
  calc
    _ ≤ ∑ w : V, (Fintype.card (G.commonNeighbors v w) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (by intros; positivity)
    _ = ∑ x ∈ G.neighborFinset v, (G.degree x : ℝ) := total_common_card G v
    _ ≤ ∑ x ∈ G.neighborFinset v, (Δ:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact_mod_cast hmax x
    _ = _ := by simp

end Erdos642.CampaignFe72210bContinuation3.LocalCodegreeIncidence
