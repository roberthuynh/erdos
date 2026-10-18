import Openmath.IncidenceRepair.PlaneCostCounting
noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair.Plane
variable {K : Type*} [Field K] [Fintype K]
def reciprocalMajorant (b : Point K 2 → Hyperplane K 2 → ℝ) (a : K) : ℝ := by
  classical
  exact b V (vertical a) + b U (horizontal a) +
    if a ≠ 0 then
      b (affine 0 0) (slope a 0) +
      b (affine 1 a) (vertical 1) + b (affine 1 a) (horizontal a) +
      b (affine a⁻¹ 1) (vertical a⁻¹) + b (affine a⁻¹ 1) (horizontal 1) +
      b (affine 1 a) (slope a 0) + b (affine a⁻¹ 1) (slope a 0)
    else 0

theorem reciprocal_budget {b : Point K 2 → Hyperplane K 2 → ℝ}
    (hb : ∀ p H, 0 ≤ b p H) : avg1 (reciprocalMajorant b) ≤ cost b := by
  have h := subfamily_le_cost hb ({0, 1, 7, 9, 10, 11, 12, 13, 14} : Finset (Fin 24))
  have hh : costTerm b 0 + costTerm b 1 + costTerm b 7 + costTerm b 9 +
      costTerm b 10 + costTerm b 11 + costTerm b 12 + costTerm b 13 +
      costTerm b 14 ≤ cost b := by simpa [add_assoc] using h
  apply le_trans (le_of_eq ?_) hh
  simp [costTerm, ← avg1_add]
  apply congrArg avg1
  funext a
  unfold reciprocalMajorant
  split_ifs <;> simp_all <;> ring

theorem reciprocal_raw_budget {b : Point K 2 → Hyperplane K 2 → ℝ}
    (hb : ∀ p H, 0 ≤ b p H) :
    ∑ a, reciprocalMajorant b a ≤ cost b * Fintype.card K :=
  sum_le_of_avg1_le (reciprocal_budget hb)

end Erdos85.IncidenceRepair.Plane
