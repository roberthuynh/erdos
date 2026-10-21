import Openmath.Attempt6.RegularizationTransport

/-! Integration of actual fresh-mask events over finite revealed histories. -/
noncomputable section
namespace Erdos642.DenseMask20261019.AdaptiveObstruction
open MeasureTheory ProbabilityTheory Finset

variable {H R : Type*} [Fintype H] [Fintype R]
  [MeasurableSpace H] [MeasurableSpace R]
  [MeasurableSingletonClass H] [MeasurableSingletonClass R]
  (mu : Measure H) [IsProbabilityMeasure mu]
  (nu : Measure R) [IsProbabilityMeasure nu]

/-- The actual product-event probability is the finite weighted section sum. -/
theorem product_event_section_sum (E : Set (H × R)) :
    (mu.prod nu).real E =
      ∑ h : H, mu.real {h} * nu.real {r | (h,r) ∈ E} := by
  rw [Erdos585.Attempt6.RegularizationTransport.finite_product_failure,
    integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul]

/-- Varying history costs may be integrated on an arbitrary fixed bad-history
set. This assumes only actual section bounds, never a joint probability bound. -/
theorem product_event_lower_integral (E : Set (H × R)) (B : Finset H)
    (cost : H → ℝ)
    (hsection : ∀ h ∈ B, cost h ≤ nu.real {r | (h,r) ∈ E}) :
    (∫ h, (B : Set H).indicator cost h ∂mu) ≤ (mu.prod nu).real E := by
  classical
  rw [Erdos585.Attempt6.RegularizationTransport.finite_product_failure]
  apply integral_mono Integrable.of_finite Integrable.of_finite
  intro h
  by_cases hh : h ∈ B
  · simpa only [Set.indicator_of_mem (show h ∈ (B : Set H) from hh)] using hsection h hh
  · simp only [Set.indicator_of_notMem (show h ∉ (B : Set H) from hh)]
    exact measureReal_nonneg

/-- A directly usable finite weighted lower bound with history-dependent costs. -/
theorem product_event_lower_sum (E : Set (H × R)) (B : Finset H)
    (cost : H → ℝ)
    (hsection : ∀ h ∈ B, cost h ≤ nu.real {r | (h,r) ∈ E}) :
    (∑ h ∈ B, mu.real {h} * cost h) ≤ (mu.prod nu).real E := by
  classical
  have h := product_event_lower_integral mu nu E B cost hsection
  rw [integral_fintype Integrable.of_finite] at h
  simpa [smul_eq_mul, Set.indicator, mul_ite, Finset.sum_filter] using h

/-- Uniform positive-section mass on the actual bad histories supplies an
unconditional lower bound in the independent history/fresh-mask experiment. -/
theorem product_event_lower_bound (E : Set (H × R)) (B : Finset H)
    (delta : ℝ) (_hdelta : 0 ≤ delta)
    (hsection : ∀ h ∈ B, delta ≤ nu.real {r | (h,r) ∈ E}) :
    mu.real (B : Set H) * delta ≤ (mu.prod nu).real E := by
  have h := product_event_lower_integral mu nu E B (fun _ => delta) hsection
  simpa only [integral_indicator_const delta MeasurableSet.of_discrete,
    smul_eq_mul] using h

end Erdos642.DenseMask20261019.AdaptiveObstruction
