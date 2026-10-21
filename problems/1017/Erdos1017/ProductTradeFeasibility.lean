import Erdos1017.ProductTradeBudgets
import Erdos1017.ElementaryLower

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem elementarySum_subset_upper (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i)
    (U : ℝ) (hU : 0 ≤ U) (hsum : (∑ i, r i) ≤ U) (s : Finset ι) (k : ℕ) :
    elementarySum s r k ≤ U^k / k.factorial := by
  have hn : 0 ≤ ∑ i ∈ s, r i := Finset.sum_nonneg (fun i _ => hr i)
  have hs : (∑ i ∈ s, r i) ≤ U :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun i _ _ => hr i)).trans hsum
  exact (elementarySum_le_power_div_factorial s r (fun i _ => hr i) k).trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ hn hs k) (by positivity))

/-- Explicit scalar budgets suffice simultaneously, even when many trades share
one negative pair cell. No limit on the number of indices is imposed. -/
theorem productTrade_feasible (r : ι → ℝ) (P θ₃ θH U V : ℝ)
    (hr : ∀ i, 0 ≤ r i) (hP : 0 ≤ P) (hU : 0 ≤ U) (hsum : (∑ i, r i) ≤ U)
    (h3 : 0 ≤ θ₃ ∧ θ₃ ≤ 1) (hH : 0 ≤ θH ∧ θH ≤ 1)
    (hsingle : θ₃ * U^2 / 2 ≤ 1)
    (hpair : θH * (U^2/6 + U^3/12 + U^4/40) ≤ 1+θ₃*V)
    (hremain : ∀ S : Finset ι, S.card = 2 → V ≤ ∑ i ∈ Finset.univ \ S, r i) :
    (∀ S, 0 ≤ combinedTrade (fun T => P * ∏ i ∈ T, r i) (productTrade r P θ₃ θH) S) ∧
    (∀ B, B.card ≤ 2 →
      subsetMoment (combinedTrade (fun T => P * ∏ i ∈ T, r i) (productTrade r P θ₃ θH)) B =
        subsetMoment (fun T => P * ∏ i ∈ T, r i) B) ∧
    ((∑ S : Finset ι, if S.Nonempty then
        combinedTrade (fun T => P * ∏ i ∈ T, r i) (productTrade r P θ₃ θH) S else 0) =
      (∑ S : Finset ι, P * ∏ i ∈ S, r i) - P - emptyBonus (productTrade r P θ₃ θH)) := by
  have hw (S : Finset ι) : 0 ≤ P * ∏ i ∈ S, r i :=
    mul_nonneg hP (Finset.prod_nonneg (fun i _ => hr i))
  have ht (T : Finset ι) : 0 ≤ productTrade r P θ₃ θH T := by
    unfold productTrade
    have hθ : 0 ≤ if T.card=3 then θ₃ else θH := by split_ifs <;> linarith [h3.1, hH.1]
    exact mul_nonneg (mul_nonneg hθ hP) (Finset.prod_nonneg (fun i _ => hr i))
  have hcap (T : Finset ι) (_hk : 3 ≤ T.card ∧ T.card ≤ 6) :
      productTrade r P θ₃ θH T ≤ P * ∏ i ∈ T, r i := by
    have hθ : (if T.card=3 then θ₃ else θH) ≤ 1 := by split_ifs <;> linarith [h3.2, hH.2]
    simpa [productTrade, mul_assoc] using mul_le_mul_of_nonneg_right hθ (hw T)
  have hsb (S : Finset ι) (hs : S.card = 1) :
      tripleDeposit (productTrade r P θ₃ θH) S ≤ P * ∏ i ∈ S, r i := by
    rw [tripleDeposit_product r P θ₃ θH S (by omega)]
    simp only [hs, show 3-1=2 from rfl]
    have he := elementarySum_subset_upper r hr U hU hsum (Finset.univ \ S) 2
    norm_num at he
    have hb : θ₃ * elementarySum (Finset.univ \ S) r 2 ≤ 1 := by
      have hm := mul_le_mul_of_nonneg_left he h3.1
      linarith
    have hm := mul_le_mul_of_nonneg_left hb (hw S)
    nlinarith
  have hpb (S : Finset ι) (hs : S.card = 2) :
      pairWithdrawal (productTrade r P θ₃ θH) S ≤
        P * (∏ i ∈ S, r i) + tripleDeposit (productTrade r P θ₃ θH) S := by
    rw [pairWithdrawal_product r P θ₃ θH S hs,
      tripleDeposit_product r P θ₃ θH S (by omega)]
    simp only [hs, show 3-2=1 from rfl, elementarySum_one]
    have he2 := elementarySum_subset_upper r hr U hU hsum (Finset.univ \ S) 2
    have he3 := elementarySum_subset_upper r hr U hU hsum (Finset.univ \ S) 3
    have he4 := elementarySum_subset_upper r hr U hU hsum (Finset.univ \ S) 4
    norm_num [Nat.factorial] at he2 he3 he4
    have he : elementarySum (Finset.univ \ S) r 2 / 3 +
        elementarySum (Finset.univ \ S) r 3 / 2 +
        3 * elementarySum (Finset.univ \ S) r 4 / 5 ≤ U^2/6+U^3/12+U^4/40 := by linarith
    have hb := (mul_le_mul_of_nonneg_left he hH.1).trans hpair
    have hv := mul_le_mul_of_nonneg_left (hremain S hs) h3.1
    have hb' := mul_le_mul_of_nonneg_left (hb.trans (add_le_add_right hv 1)) (hw S)
    nlinarith
  simpa using combinedTrade_selector_certificate
    (fun T => P * ∏ i ∈ T, r i) (productTrade r P θ₃ θH) hw ht hcap hsb hpb

end Erdos1017
