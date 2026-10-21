import Erdos1017.ProductTradeFeasibility
import Erdos1017.IndependentSubset

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def tradeDenominator (U : ℝ) : ℝ := U^2/6+U^3/12+U^4/40
noncomputable def tradeThetaThree (U : ℝ) : ℝ := 2/U^2
noncomputable def tradeThetaHigher (U V : ℝ) : ℝ :=
  min 1 ((1+tradeThetaThree U*V)/tradeDenominator U)

theorem trade_parameter_budgets (U V : ℝ) (hU : 2 ≤ U) (hV : 0 ≤ V) :
    (0 ≤ tradeThetaThree U ∧ tradeThetaThree U ≤ 1) ∧
    (0 ≤ tradeThetaHigher U V ∧ tradeThetaHigher U V ≤ 1) ∧
    tradeThetaThree U * U^2 / 2 ≤ 1 ∧
    tradeThetaHigher U V * tradeDenominator U ≤ 1+tradeThetaThree U*V := by
  have hUpos : 0 < U := by linarith
  have hsq : 0 < U^2 := sq_pos_of_pos hUpos
  have hL : 0 < tradeDenominator U := by unfold tradeDenominator; positivity
  have h3pos : 0 ≤ tradeThetaThree U := by unfold tradeThetaThree; positivity
  have h3one : tradeThetaThree U ≤ 1 := by
    unfold tradeThetaThree
    apply (div_le_one hsq).mpr
    nlinarith
  have hHpos : 0 ≤ tradeThetaHigher U V := by
    unfold tradeThetaHigher
    apply le_min (by norm_num)
    exact div_nonneg (by positivity) hL.le
  have hHone : tradeThetaHigher U V ≤ 1 := min_le_left _ _
  refine ⟨⟨h3pos, h3one⟩, ⟨hHpos, hHone⟩, ?_, ?_⟩
  · unfold tradeThetaThree
    rw [div_mul_cancel₀ _ (ne_of_gt hsq)]
    norm_num
  · exact (le_div_iff₀ hL).mp (min_le_right _ _)

theorem odds_remaining_lower (p : ι → ℝ) (m : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hm : ∀ i, p i ≤ m) (hm1 : m < 1)
    (B : Finset ι) (hB : B.card = 2) :
    (∑ i, p i)-2*m ≤ ∑ i ∈ Finset.univ \ B, p i/(1-p i) := by
  have hcap : (∑ i ∈ B, p i) ≤ 2*m := by
    calc
      _ ≤ ∑ _i ∈ B, m := Finset.sum_le_sum (fun i _ => hm i)
      _ = _ := by simp [hB]
  have hsplit := Finset.sum_sdiff (f := p) (Finset.subset_univ B)
  have hlo : (∑ i ∈ Finset.univ \ B, p i) ≤ ∑ i ∈ Finset.univ \ B, p i/(1-p i) := by
    apply Finset.sum_le_sum
    intro i _
    rw [odds_decomposition (p i) ((hm i).trans_lt hm1)]
    have hd : 0 ≤ (p i)^2/(1-p i) := div_nonneg (sq_nonneg _) (by linarith [hm i])
    linarith
  linarith

noncomputable def analyticTradeAmounts (p : ι → ℝ) (m : ℝ) (T : Finset ι) : ℝ :=
  let S := ∑ i, p i
  let q := ∑ i, (p i)^2
  let U := S+q/(1-m)
  productTrade (fun i => p i/(1-p i)) (∏ i, (1-p i))
    (tradeThetaThree U) (tradeThetaHigher U (S-2*m)) T

noncomputable def analyticTradeLaw (p : ι → ℝ) (m : ℝ) : Finset ι → ℝ :=
  combinedTrade (independentSubset p) (analyticTradeAmounts p m)

/-- The concrete simultaneous selector is feasible for every finite coordinate set.
This discharges all singleton, pair and per-trade caps without assuming them. -/
theorem analyticTradeLaw_certificate (p : ι → ℝ) (m : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hm : ∀ i, p i ≤ m) (hm1 : m < 1)
    (hS : 2 ≤ ∑ i, p i)
    (hgap : 0 < (∑ i, p i)-(∑ i, (p i)^2)) :
    (∀ T, 0 ≤ analyticTradeLaw p m T) ∧
    (∀ B : Finset ι, B.card ≤ 2 → subsetMoment (analyticTradeLaw p m) B = ∏ i ∈ B, p i) ∧
    ((∑ T : Finset ι, if T.Nonempty then analyticTradeLaw p m T else 0) =
      1-(∏ i, (1-p i))-emptyBonus (analyticTradeAmounts p m)) := by
  let S := ∑ i, p i
  let q := ∑ i, (p i)^2
  let U := S+q/(1-m)
  let V := S-2*m
  have hlt : ∀ i, p i < 1 := fun i => (hm i).trans_lt hm1
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _ => sq_nonneg (p i))
  have hU : 2 ≤ U := by
    have h : 0 ≤ q/(1-m) := div_nonneg hq (sub_pos.mpr hm1).le
    dsimp [U, S]
    linarith
  have hV : 0 ≤ V := by dsimp [V, S]; linarith
  obtain ⟨h3, hH, hsingle, hpair⟩ := trade_parameter_budgets U V hU hV
  have hsum : (∑ i, p i/(1-p i)) ≤ U :=
    (odds_sum_certificate Finset.univ p m (fun i _ => hp i) (fun i _ => hm i) hm1 hgap).1
  have hcert := productTrade_feasible (fun i => p i/(1-p i)) (∏ i, (1-p i))
    (tradeThetaThree U) (tradeThetaHigher U V) U V
    (fun i => div_nonneg (hp i) (sub_pos.mpr (hlt i)).le)
    (Finset.prod_nonneg (fun i _ => (sub_pos.mpr (hlt i)).le)) (by linarith) hsum h3 hH
    hsingle hpair (fun B hB => odds_remaining_lower p m hp hm hm1 B hB)
  refine ⟨hcert.1, ?_, ?_⟩
  · intro B hB
    exact (hcert.2.1 B hB).trans (independentSubset_moment p hlt B)
  · have ht : (∑ T : Finset ι, (∏ i, (1-p i)) * ∏ i ∈ T, p i/(1-p i)) = 1 :=
      independentSubset_total p hlt
    rw [ht] at hcert
    exact hcert.2.2

end Erdos1017
