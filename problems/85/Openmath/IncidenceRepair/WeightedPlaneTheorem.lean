import Openmath.IncidenceRepair.PlaneSupportGeometry
import Openmath.IncidenceRepair.PlanePexiderBudgets
import Openmath.IncidenceRepair.PlaneCorrectionAssembly

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair.Plane
variable {K L : Type*} [Field K] [Field L] [Fintype K]

/-- The complete weighted protected-plane lemma for arbitrary maps and a
nonnegative majorant of their actual broken original flags. No injectivity or
field embedding is assumed. -/
theorem weighted_plane
    (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2)
    (hp : Protected φ ψ) (b : Point K 2 → Hyperplane K 2 → ℝ)
    (hb : ∀ p H, 0 ≤ b p H)
    (hbad : ∀ p H, Incident p H → ¬ Incident (φ p) (ψ H) → 1 ≤ b p H)
    (hsmall : cost b ≤ 1/10000000) :
    count (fun x => ¬ ProperX ψ x) ≤ 17 * cost b * Fintype.card K ∧
    count (fun y => ¬ ProperY ψ y) ≤ 17 * cost b * Fintype.card K ∧
    ∃ σ : K →+* L,
      count (fun x => coordX ψ x ≠ σ x) ≤ 288 * cost b * Fintype.card K ∧
      count (fun y => coordY ψ y ≠ σ y) ≤ 648 * cost b * Fintype.card K ∧
      count (fun z : K × K => φ (affine z.1 z.2) ≠ affine (σ z.1) (σ z.2)) ≤
        971 * cost b * (Fintype.card K : ℝ)^2 := by
  classical
  have hs := protected_support_bounds φ ψ hp b hb hbad (by linarith : cost b ≤ 1/12)
  have hx : count (fun x => ¬ ProperX ψ x) ≤ 17 * cost b * Fintype.card K := by
    rw [count_not, count_eq_filter_card]
    simpa only [goodX] using hs.1
  have hy16 : count (fun y => ¬ ProperY ψ y) ≤ 16 * cost b * Fintype.card K := by
    rw [count_not, count_eq_filter_card]
    simpa only [goodY] using hs.2
  have hy : count (fun y => ¬ ProperY ψ y) ≤ 17 * cost b * Fintype.card K := by
    have hn : 0 ≤ cost b * Fintype.card K := mul_nonneg (cost_nonneg hb) (by positivity)
    linarith
  obtain ⟨hproduct, herr, hrow, hdiag⟩ := pexider_budgets φ ψ hp b hb hbad hx hy
  have hproduct' : count (fun z : K × K =>
      φ (affine z.1 z.2) ≠ affine (coordX ψ z.1) (coordY ψ z.2)) ≤
      35 * cost b * (Fintype.card K : ℝ)^2 := by
    rw [count_prod (fun x y : K => φ (affine x y) ≠ affine (coordX ψ x) (coordY ψ y))]
    convert hproduct using 1
    apply Finset.sum_congr rfl
    intro x _
    unfold count
    apply Finset.sum_congr rfl
    intro y _
    unfold productError
    by_cases he : φ (affine x y) = affine (coordX ψ x) (coordY ψ y) <;> simp [he]
  have hflags : (∑ a : K, ∑ c : K, count (fun x =>
      ¬ Incident (φ (affine x (a*x+c))) (ψ (slope a c)))) ≤
      cost b * (Fintype.card K : ℝ)^3 := by
    have hbudget := sum_le_of_avg3_le (show avg3
        (fun a c x : K => b (affine x (a*x+c)) (slope a c)) ≤ cost b by
      simpa [costTerm] using
        costTerm_le_cost hb 23)
    apply le_trans _ hbudget
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro c _
    unfold count
    apply Finset.sum_le_sum
    intro x _
    by_cases h : Incident (φ (affine x (a*x+c))) (ψ (slope a c))
    · simpa [h] using hb (affine x (a*x+c)) (slope a c)
    · simpa [h] using hbad (affine x (a*x+c)) (slope a c) (by simp) h
  have hv := protected_values φ ψ hp
  exact ⟨hx, hy, corrected_field_embedding φ ψ (coordX ψ) (coordY ψ)
    (diagonalIntercept ψ) (cost b) (cost_nonneg hb) hsmall herr hrow hdiag
    hv.2.2.2.2.1 hv.2.2.2.2.2.1 hproduct' hflags⟩

end Erdos85.IncidenceRepair.Plane
