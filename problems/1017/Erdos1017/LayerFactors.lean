import Erdos1017.ElementaryBounds

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

/-- Exact factorization of a fixed-cardinality family containing a prescribed cell. -/
theorem sum_layer_supersets (s B : Finset ι) (hBs : B ⊆ s) (r : ι → ℝ) (k : ℕ) :
    (∑ T ∈ (s.powersetCard (B.card+k)).filter (B ⊆ ·), ∏ i ∈ T, r i) =
      (∏ i ∈ B, r i) * elementarySum (s \ B) r k := by
  unfold elementarySum
  rw [Finset.mul_sum]
  apply Finset.sum_bij (fun T _ => T \ B)
  · intro T hT
    obtain ⟨hT, hBT⟩ := Finset.mem_filter.mp hT
    obtain ⟨hTs, hcard⟩ := Finset.mem_powersetCard.mp hT
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.sdiff_subset_sdiff_left B hTs,
      by rw [Finset.card_sdiff_of_subset hBT, hcard]; omega⟩
  · intro T hT U hU he
    have ht := (Finset.mem_filter.mp hT).2
    have hu := (Finset.mem_filter.mp hU).2
    simpa [Finset.union_sdiff_of_subset ht, Finset.union_sdiff_of_subset hu]
      using congrArg (fun V => B ∪ V) he
  · intro U hU
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hU
    have hd : Disjoint B U := Finset.disjoint_left.mpr (fun i hi hu => (Finset.mem_sdiff.mp (hsub hu)).2 hi)
    refine ⟨B ∪ U, ?_, Finset.union_sdiff_cancel_left hd⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.subset_union_left⟩
    · exact Finset.union_subset hBs (hsub.trans Finset.sdiff_subset)
    · rw [Finset.card_union_of_disjoint hd, hcard]
  · intro T hT
    have hBT := (Finset.mem_filter.mp hT).2
    have hd : Disjoint B (T \ B) := Finset.disjoint_left.mpr
      (fun i hi hu => (Finset.mem_sdiff.mp hu).2 hi)
    rw [← Finset.prod_union hd, Finset.union_sdiff_of_subset hBT]

theorem sum_layer_supersets_univ [Fintype ι] (B : Finset ι) (r : ι → ℝ) (k : ℕ) (P : ℝ) :
    (∑ T : Finset ι, if T.card = B.card+k ∧ B ⊆ T then P * ∏ i ∈ T, r i else 0) =
      P * (∏ i ∈ B, r i) * elementarySum (Finset.univ \ B) r k := by
  have hsets : (Finset.univ : Finset (Finset ι)).filter (fun T => T.card = B.card+k ∧ B ⊆ T) =
      ((Finset.univ : Finset ι).powersetCard (B.card+k)).filter (B ⊆ ·) := by
    ext T
    simp [Finset.mem_powersetCard]
  rw [← Finset.sum_filter, hsets, ← Finset.mul_sum,
    sum_layer_supersets Finset.univ B (Finset.subset_univ B) r k]
  ring

end Erdos1017
