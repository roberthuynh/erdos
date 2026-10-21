import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Finite independent selectors, with all individual and joint inclusion moments. -/
namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def selectorMass (p : ι → ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, if x i then p i else 1-p i

omit [DecidableEq ι] in
theorem selectorMass_nonneg (p : ι → ℝ) (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1)
    (x : ι → Bool) : 0 ≤ selectorMass p x := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact h0 i
  · exact sub_nonneg.mpr (h1 i)

/-- Factorization for arbitrary coordinate observables, hence every joint moment. -/
theorem selector_factorization (p : ι → ℝ) (f : ι → Bool → ℝ) :
    (∑ x : ι → Bool, selectorMass p x * ∏ i, f i (x i)) =
      ∏ i, ((1-p i) * f i false + p i * f i true) := by
  simp only [selectorMass, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) => (if b then p i else 1-p i) * f i b)]
  apply Finset.prod_congr rfl
  intro i _
  simp [add_comm]

theorem selector_total (p : ι → ℝ) : ∑ x : ι → Bool, selectorMass p x = 1 := by
  simpa using selector_factorization p (fun _ _ => 1)

/-- Probability that every index in `s` is selected, without constraining the other indices. -/
noncomputable def inclusionIndicator (s : Finset ι) (x : ι → Bool) : ℝ :=
  ∏ i ∈ s, if x i then (1 : ℝ) else 0

theorem selector_inclusion (p : ι → ℝ) (s : Finset ι) :
    (∑ x : ι → Bool, selectorMass p x * inclusionIndicator s x) = ∏ i ∈ s, p i := by
  have hi (x : ι → Bool) : inclusionIndicator s x =
      ∏ i, if i ∈ s then (if x i then (1 : ℝ) else 0) else 1 := by
    simp [inclusionIndicator, Finset.prod_ite_mem]
  simp_rw [hi]
  rw [selector_factorization p (fun i (b : Bool) => if i ∈ s then (if b then 1 else 0) else 1)]
  calc
    _ = ∏ i, (if i ∈ s then p i else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : i ∈ s <;> simp [h]
    _ = _ := by simp [Finset.prod_ite_mem]

theorem selector_singleton (p : ι → ℝ) (i : ι) :
    (∑ x : ι → Bool, selectorMass p x * (if x i then 1 else 0)) = p i := by
  simpa [inclusionIndicator] using selector_inclusion p {i}

theorem selector_pair (p : ι → ℝ) (i j : ι) (h : i ≠ j) :
    (∑ x : ι → Bool, selectorMass p x *
      ((if x i then 1 else 0) * (if x j then 1 else 0))) = p i * p j := by
  simpa [inclusionIndicator, h] using selector_inclusion p {i,j}

end Erdos1017
