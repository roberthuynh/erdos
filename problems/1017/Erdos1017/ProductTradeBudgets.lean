import Erdos1017.LayerFactors
import Erdos1017.CombinedTrades

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def productTrade (r : ι → ℝ) (P θ₃ θH : ℝ) (T : Finset ι) : ℝ :=
  (if T.card = 3 then θ₃ else θH) * P * ∏ i ∈ T, r i

theorem productTrade_layer (r : ι → ℝ) (P θ₃ θH : ℝ) (S : Finset ι)
    (d : ℕ) (hs : S.card ≤ d) :
    (∑ T : Finset ι, if T.card = d ∧ S ⊆ T then productTrade r P θ₃ θH T else 0) =
      (if d = 3 then θ₃ else θH) * P * (∏ i ∈ S, r i) *
        elementarySum (Finset.univ \ S) r (d-S.card) := by
  have h := sum_layer_supersets_univ S r (d-S.card) ((if d=3 then θ₃ else θH)*P)
  rw [Nat.add_sub_of_le hs] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro T _
  by_cases ht : T.card = d ∧ S ⊆ T
  · simp [ht, productTrade, ht.1]
  · simp [ht]

theorem tripleDeposit_univ (t : Finset ι → ℝ) (S : Finset ι) :
    tripleDeposit t S = ∑ T : Finset ι, if T.card = 3 ∧ S ⊆ T then t T else 0 := by
  unfold tripleDeposit tradeSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases ht : T.card = 3
  · simp [ht]
  · simp [ht]

theorem tripleDeposit_product (r : ι → ℝ) (P θ₃ θH : ℝ) (S : Finset ι)
    (hs : S.card ≤ 3) :
    tripleDeposit (productTrade r P θ₃ θH) S =
      θ₃ * P * (∏ i ∈ S, r i) * elementarySum (Finset.univ \ S) r (3-S.card) := by
  rw [tripleDeposit_univ, productTrade_layer r P θ₃ θH S 3 hs]
  simp

theorem pairWithdrawal_layers (t : Finset ι → ℝ) (S : Finset ι) :
    pairWithdrawal t S =
      (1/3 : ℝ) * (∑ T : Finset ι, if T.card = 4 ∧ S ⊆ T then t T else 0) +
      (1/2 : ℝ) * (∑ T : Finset ι, if T.card = 5 ∧ S ⊆ T then t T else 0) +
      (3/5 : ℝ) * (∑ T : Finset ι, if T.card = 6 ∧ S ⊆ T then t T else 0) := by
  unfold pairWithdrawal tradeSupport
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hst : S ⊆ T
  · by_cases hc : 3 ≤ T.card ∧ T.card ≤ 6
    · have he : T.card = 3 ∨ T.card = 4 ∨ T.card = 5 ∨ T.card = 6 := by omega
      rcases he with he | he | he | he <;> norm_num [he, hst]
    · have h4 : T.card ≠ 4 := by omega
      have h5 : T.card ≠ 5 := by omega
      have h6 : T.card ≠ 6 := by omega
      simp [hc, hst, h4, h5, h6]
  · simp [hst]

theorem pairWithdrawal_product (r : ι → ℝ) (P θ₃ θH : ℝ) (S : Finset ι)
    (hs : S.card = 2) :
    pairWithdrawal (productTrade r P θ₃ θH) S =
      P * (∏ i ∈ S, r i) * θH *
        (elementarySum (Finset.univ \ S) r 2 / 3 +
         elementarySum (Finset.univ \ S) r 3 / 2 +
         3 * elementarySum (Finset.univ \ S) r 4 / 5) := by
  rw [pairWithdrawal_layers,
    productTrade_layer r P θ₃ θH S 4 (by omega),
    productTrade_layer r P θ₃ θH S 5 (by omega),
    productTrade_layer r P θ₃ θH S 6 (by omega)]
  norm_num [hs]
  ring

theorem emptyBonus_layers (t : Finset ι → ℝ) :
    emptyBonus t =
      (∑ T : Finset ι, if T.card = 3 ∧ ∅ ⊆ T then t T else 0) +
      (1/3 : ℝ) * (∑ T : Finset ι, if T.card = 4 ∧ ∅ ⊆ T then t T else 0) +
      (∑ T : Finset ι, if T.card = 5 ∧ ∅ ⊆ T then t T else 0) +
      2 * (∑ T : Finset ι, if T.card = 6 ∧ ∅ ⊆ T then t T else 0) := by
  unfold emptyBonus tradeSupport
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hc : 3 ≤ T.card ∧ T.card ≤ 6
  · have he : T.card = 3 ∨ T.card = 4 ∨ T.card = 5 ∨ T.card = 6 := by omega
    rcases he with he | he | he | he <;> norm_num [he]
  · have h3 : T.card ≠ 3 := by omega
    have h4 : T.card ≠ 4 := by omega
    have h5 : T.card ≠ 5 := by omega
    have h6 : T.card ≠ 6 := by omega
    simp [hc, h3, h4, h5, h6]

theorem emptyBonus_product (r : ι → ℝ) (P θ₃ θH : ℝ) :
    emptyBonus (productTrade r P θ₃ θH) = P *
      (θ₃ * elementarySum Finset.univ r 3 + θH *
        (elementarySum Finset.univ r 4 / 3 + elementarySum Finset.univ r 5 +
          2 * elementarySum Finset.univ r 6)) := by
  rw [emptyBonus_layers,
    productTrade_layer r P θ₃ θH ∅ 3 (by simp),
    productTrade_layer r P θ₃ θH ∅ 4 (by simp),
    productTrade_layer r P θ₃ θH ∅ 5 (by simp),
    productTrade_layer r P θ₃ θH ∅ 6 (by simp)]
  norm_num
  ring

end Erdos1017
