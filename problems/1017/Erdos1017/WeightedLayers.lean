import Erdos1017.ElementaryIncidence
import Erdos1017.CombinedTrades

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def weightedLayer (x : ι → ℝ) (k : ℕ) (T : Finset ι) : ℝ :=
  if T.card = k then ∏ i ∈ T, x i else 0

theorem weightedLayer_total (x : ι → ℝ) (k : ℕ) :
    (∑ T : Finset ι, weightedLayer x k T) = elementarySum Finset.univ x k := by
  simp only [weightedLayer, elementarySum, Finset.powersetCard_eq_filter, Finset.sum_filter]
  simp

theorem weightedLayer_top_moment (x : ι → ℝ) (B : Finset ι) :
    subsetMoment (weightedLayer x B.card) B = ∏ i ∈ B, x i := by
  unfold subsetMoment weightedLayer
  have hh (T : Finset ι) :
      (if B ⊆ T then (if T.card = B.card then ∏ i ∈ T, x i else 0) else 0) =
        if T = B then ∏ i ∈ B, x i else 0 := by
    by_cases h : T = B
    · subst T; simp
    · by_cases hBT : B ⊆ T
      · have hc : T.card ≠ B.card := fun hc => h (Finset.eq_of_subset_of_card_le hBT hc.le).symm
        simp [h,hBT,hc]
      · simp [h,hBT]
  simp_rw [hh]
  simp

theorem weightedLayer_moment_zero (x : ι → ℝ) (B : Finset ι) (k : ℕ) (hk : k < B.card) :
    subsetMoment (weightedLayer x k) B = 0 := by
  apply Finset.sum_eq_zero
  intro T _
  dsimp [weightedLayer]
  split_ifs with hBT hc
  · have h := Finset.card_le_card hBT
    omega
  all_goals rfl

theorem weightedLayer_singleton_moment (x : ι → ℝ) (i : ι) (k : ℕ) :
    subsetMoment (weightedLayer x (k+1)) {i} =
      x i * elementarySum (Finset.univ.erase i) x k := by
  unfold subsetMoment weightedLayer
  simp only [Finset.singleton_subset_iff]
  have hsum :
      (∑ T : Finset ι, if i ∈ T then (if T.card = k+1 then ∏ j ∈ T, x j else 0) else 0) =
      ∑ T ∈ (Finset.univ.powersetCard (k+1)).filter (fun T => i ∈ T), ∏ j ∈ T, x j := by
    simp only [Finset.sum_filter, Finset.powersetCard_eq_filter, Finset.sum_filter]
    simp only [Finset.powerset_univ]
    apply Finset.sum_congr rfl
    intro T _
    split_ifs <;> rfl
  rw [hsum]
  have he :
      (∑ T ∈ (Finset.univ.powersetCard (k+1)).filter (fun T => i ∈ T), ∏ j ∈ T, x j) =
      ∑ T ∈ (Finset.univ.powersetCard (k+1)).filter (fun T => i ∈ T), x i * ∏ j ∈ T.erase i, x j := by
    apply Finset.sum_congr rfl
    intro T hT
    exact (Finset.mul_prod_erase T x (Finset.mem_filter.mp hT).2).symm
  rw [he, sum_powersetCard_containing Finset.univ i (Finset.mem_univ i) k (fun U => x i * ∏ j ∈ U, x j)]
  exact (Finset.mul_sum _ _ _).symm

theorem weighted_elementarySum_one (s : Finset ι) (x : ι → ℝ) :
    elementarySum s x 1 = ∑ i ∈ s, x i := by
  simp [elementarySum, Finset.powersetCard_one]

theorem elementarySum_two_identity (s : Finset ι) (x : ι → ℝ) :
    2*elementarySum s x 2 = (∑ i ∈ s, x i)^2 - ∑ i ∈ s, (x i)^2 := by
  induction s using Finset.induction_on with
  | empty => simp [elementarySum_empty]
  | @insert i s hi ih =>
    rw [elementarySum_insert s x i hi 1, weighted_elementarySum_one, Finset.sum_insert hi, Finset.sum_insert hi]
    nlinarith

end Erdos1017
