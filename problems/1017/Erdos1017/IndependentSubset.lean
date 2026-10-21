import Erdos1017.LayerFactors
import Erdos1017.OddsBounds
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem product_subset_moment (r : ι → ℝ) (P : ℝ) (B : Finset ι) :
    subsetMoment (fun T => P * ∏ i ∈ T, r i) B =
      P * (∏ i ∈ B, r i) * ∏ i ∈ Finset.univ \ B, (1+r i) := by
  unfold subsetMoment
  rw [← Finset.sum_filter, Finset.prod_one_add, Finset.mul_sum]
  apply Finset.sum_bij (fun T _ => T \ B)
  · intro T hT
    apply Finset.mem_powerset.mpr
    exact Finset.sdiff_subset_sdiff_left B (Finset.subset_univ T)
  · intro T hT U hU he
    have ht := (Finset.mem_filter.mp hT).2
    have hu := (Finset.mem_filter.mp hU).2
    simpa [Finset.union_sdiff_of_subset ht, Finset.union_sdiff_of_subset hu]
      using congrArg (fun V => B ∪ V) he
  · intro U hU
    have hsub := Finset.mem_powerset.mp hU
    have hd : Disjoint B U := Finset.disjoint_left.mpr (fun i hi hu => (Finset.mem_sdiff.mp (hsub hu)).2 hi)
    exact ⟨B ∪ U, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_union_left⟩,
      Finset.union_sdiff_cancel_left hd⟩
  · intro T hT
    have hBT := (Finset.mem_filter.mp hT).2
    have hd : Disjoint B (T \ B) := Finset.disjoint_left.mpr
      (fun i hi hu => (Finset.mem_sdiff.mp hu).2 hi)
    rw [mul_assoc, ← Finset.prod_union hd, Finset.union_sdiff_of_subset hBT]

noncomputable def independentSubset (p : ι → ℝ) (T : Finset ι) : ℝ :=
  (∏ i, (1-p i)) * ∏ i ∈ T, (p i/(1-p i))

/-- The odds representation has every independent inclusion moment, including total mass. -/
theorem independentSubset_moment (p : ι → ℝ) (hp : ∀ i, p i < 1) (B : Finset ι) :
    subsetMoment (independentSubset p) B = ∏ i ∈ B, p i := by
  unfold independentSubset
  rw [product_subset_moment]
  have hB : (∏ i ∈ B, (1-p i)) * (∏ i ∈ B, p i/(1-p i)) = ∏ i ∈ B, p i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hn : 1-p i ≠ 0 := ne_of_gt (sub_pos.mpr (hp i))
    field_simp
  have hC : (∏ i ∈ Finset.univ \ B, (1-p i)) *
      (∏ i ∈ Finset.univ \ B, (1+p i/(1-p i))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    have hn : 1-p i ≠ 0 := ne_of_gt (sub_pos.mpr (hp i))
    field_simp
    ring
  have hP := Finset.prod_sdiff (f := fun i => (1-p i)) (Finset.subset_univ B)
  calc
    _ = ((∏ i ∈ B, (1-p i)) * (∏ i ∈ B, p i/(1-p i))) *
        ((∏ i ∈ Finset.univ \ B, (1-p i)) *
          (∏ i ∈ Finset.univ \ B, (1+p i/(1-p i)))) := by rw [← hP]; ring
    _ = _ := by rw [hB, hC, mul_one]

theorem independentSubset_total (p : ι → ℝ) (hp : ∀ i, p i < 1) :
    (∑ T : Finset ι, independentSubset p T) = 1 := by
  simpa [subsetMoment] using independentSubset_moment p hp ∅

end Erdos1017
