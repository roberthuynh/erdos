import Erdos1017.ElementaryBounds

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

theorem sum_powersetCard_containing (s : Finset ι) (i : ι) (hi : i ∈ s)
    (k : ℕ) (f : Finset ι → ℝ) :
    (∑ T ∈ (s.powersetCard (k+1)).filter (fun T => i ∈ T), f (T.erase i)) =
      ∑ U ∈ (s.erase i).powersetCard k, f U := by
  apply Finset.sum_bij (fun T _ => T.erase i)
  · intro T hT
    obtain ⟨hT, hiT⟩ := Finset.mem_filter.mp hT
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.erase_subset_erase i hsub, by simp [Finset.card_erase_of_mem hiT, hcard]⟩
  · intro T hT U hU he
    have ht := (Finset.mem_filter.mp hT).2
    have hu := (Finset.mem_filter.mp hU).2
    simpa [Finset.insert_erase ht, Finset.insert_erase hu] using congrArg (insert i) he
  · intro U hU
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hU
    have hiU : i ∉ U := fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
    refine ⟨insert i U, ?_, Finset.erase_insert hiU⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
    · exact Finset.insert_subset hi (hsub.trans (Finset.erase_subset _ _))
    · simp [Finset.card_insert_of_notMem hiU, hcard]
  · intro T _
    rfl

/-- Regroup the first-order correction by its distinguished coordinate. -/
theorem sum_firstOrderTerm (s : Finset ι) (p d : ι → ℝ) (k : ℕ) :
    (∑ T ∈ s.powersetCard (k+1), firstOrderTerm T p d) =
      ∑ i ∈ s, d i * elementarySum (s.erase i) p k := by
  unfold firstOrderTerm
  have hex : (∑ T ∈ s.powersetCard (k+1), ∑ i ∈ T, d i * ∏ j ∈ T.erase i, p j) =
      ∑ T ∈ s.powersetCard (k+1), ∑ i ∈ s,
        if i ∈ T then d i * ∏ j ∈ T.erase i, p j else 0 := by
    apply Finset.sum_congr rfl
    intro T hT
    have hsub := (Finset.mem_powersetCard.mp hT).1
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hsub h, h⟩, fun h => h.2⟩
  rw [hex, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_filter]
  rw [sum_powersetCard_containing s i hi k (fun U => d i * ∏ j ∈ U, p j)]
  exact (Finset.mul_sum _ _ _).symm

theorem firstOrderTerm_self (s : Finset ι) (p : ι → ℝ) :
    firstOrderTerm s p p = (s.card : ℝ) * ∏ i ∈ s, p i := by
  unfold firstOrderTerm
  have h : (∑ i ∈ s, p i * ∏ j ∈ s.erase i, p j) = ∑ _i ∈ s, ∏ j ∈ s, p j := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.mul_prod_erase s p hi
  rw [h]
  simp

theorem elementarySum_degree_identity (s : Finset ι) (p : ι → ℝ) (k : ℕ) :
    (∑ i ∈ s, p i * elementarySum (s.erase i) p k) =
      (k+1 : ℕ) * elementarySum s p (k+1) := by
  rw [← sum_firstOrderTerm]
  unfold elementarySum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [firstOrderTerm_self, (Finset.mem_powersetCard.mp hT).2]

end Erdos1017
