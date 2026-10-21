import Erdos1017.RectangleMonotonicity
import Erdos1017.ProductEnclosure

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def rectangleU (sh mh : ℝ) : ℝ := sh+mh^2/(1-mh)
noncomputable def rectangleP (sh mh : ℝ) : ℝ :=
  1/expUpper (sh+logCoefficientUpper 13 mh*mh^2)
noncomputable def rectangleB (k : ℕ) (sl sh ml mh : ℝ) : ℝ :=
  rectangleCorrectedLower k sl sh (ml^2) (mh^2) mh
noncomputable def rectangleBracket (sl sh ml mh : ℝ) : ℝ :=
  1+tradeThetaThree (rectangleU sh mh)*rectangleB 0 sl sh ml mh +
    tradeThetaHigher (rectangleU sh mh) (sl-2*mh)*
      (rectangleB 1 sl sh ml mh/3+rectangleB 2 sl sh ml mh+2*rectangleB 3 sl sh ml mh)
noncomputable def rectangleTradeAmounts (p : ι → ℝ) (sl sh mh : ℝ) : Finset ι → ℝ :=
  productTrade (fun i => p i/(1-p i)) (∏ i, (1-p i))
    (tradeThetaThree (rectangleU sh mh)) (tradeThetaHigher (rectangleU sh mh) (sl-2*mh))
noncomputable def rectangleLaw (p : ι → ℝ) (sl sh mh : ℝ) : Finset ι → ℝ :=
  combinedTrade (independentSubset p) (rectangleTradeAmounts p sl sh mh)

/-- A single cell uses its conservative endpoint coefficients for every point in it.
This avoids choosing coefficients from the unknown interior point. -/
theorem rectangle_selector_certificate (p : ι → ℝ) (sl sh ml mh : ℝ)
    (hsl : 2 ≤ sl) (hsh : sl ≤ sh) (hml : 0 ≤ ml) (hmm : ml ≤ mh) (hmh : mh < 1)
    (hqsl : mh^2 < sl) (hV : 0 ≤ sl-2*mh)
    (hX : sh+logCoefficientUpper 13 mh*mh^2 < 18)
    (hp : ∀ i, 0 ≤ p i) (hm : ∀ i, p i ≤ mh)
    (hSl : sl ≤ ∑ i, p i) (hSh : (∑ i, p i) ≤ sh)
    (hql : ml^2 ≤ ∑ i, (p i)^2) (hqh : (∑ i, (p i)^2) ≤ mh^2) :
    (∀ T, 0 ≤ rectangleLaw p sl sh mh T) ∧
    (∀ B : Finset ι, B.card ≤ 2 → subsetMoment (rectangleLaw p sl sh mh) B = ∏ i ∈ B, p i) ∧
    ((∑ T : Finset ι, if T.Nonempty then rectangleLaw p sl sh mh T else 0) ≤
      1-rectangleP sh mh*rectangleBracket sl sh ml mh) := by
  let S := ∑ i, p i
  let q := ∑ i, (p i)^2
  let r := fun i => p i/(1-p i)
  let P := ∏ i, (1-p i)
  let U := rectangleU sh mh
  let V := sl-2*mh
  have hmh0 : 0 ≤ mh := hml.trans hmm
  have hsh0 : 0 ≤ sh := by linarith
  have hSpos : 0 < S := by dsimp [S]; linarith
  have hgap : 0 < S-q := by dsimp [S,q]; linarith
  have hlt : ∀ i, p i < 1 := fun i => (hm i).trans_lt hmh
  have hr : ∀ i, 0 ≤ r i := fun i => div_nonneg (hp i) (sub_pos.mpr (hlt i)).le
  have hP : 0 ≤ P := Finset.prod_nonneg (fun i _ => (sub_pos.mpr (hlt i)).le)
  have hU : 2 ≤ U := by
    have ht : 0 ≤ mh^2/(1-mh) := div_nonneg (sq_nonneg _) (sub_pos.mpr hmh).le
    dsimp [U,rectangleU]
    linarith
  obtain ⟨h3,hH,hsingle,hpair⟩ := trade_parameter_budgets U V hU hV
  have hsum : (∑ i, r i) ≤ U := by
    have h := (odds_sum_certificate Finset.univ p mh (fun i _ => hp i) (fun i _ => hm i) hmh hgap).1
    have hq := div_le_div_of_nonneg_right hqh (sub_pos.mpr hmh).le
    dsimp [U,rectangleU]
    linarith
  have hremain (B : Finset ι) (hB : B.card = 2) : V ≤ ∑ i ∈ Finset.univ \ B, r i := by
    have h := odds_remaining_lower p mh hp hm hmh B hB
    dsimp [V]
    linarith
  have hc := productTrade_feasible r P (tradeThetaThree U) (tradeThetaHigher U V) U V
    hr hP (by linarith) hsum h3 hH hsingle hpair hremain
  refine ⟨hc.1, ?_, ?_⟩
  · intro B hB
    exact (hc.2.1 B hB).trans (independentSubset_moment p hlt B)
  · have hB (k : ℕ) : rectangleB k sl sh ml mh ≤ elementarySum Finset.univ r (k+3) := by
      have hlo := correctedLower_rectangle k S q mh sl sh (ml^2) (mh^2) mh
        (by linarith) hSl hSh (sq_nonneg _) hql hqh (by linarith) (le_refl mh) (by linarith)
      exact hlo.trans (first_order_odds_lower Finset.univ p mh
        (fun i _ => hp i) (fun i _ => hm i) hmh (by dsimp [S] at hSpos; linarith) hgap k)
    have hBnonneg (k : ℕ) : 0 ≤ rectangleB k sl sh ml mh := by
      have hsml : ml^2 ≤ mh^2 := pow_le_pow_left₀ hml hmm 2
      have hden : 0 < sh-ml^2 := by linarith
      exact add_nonneg (collisionLower_nonneg _ _ _)
        (mul_nonneg (div_nonneg (mul_nonneg hsh0 (sq_nonneg _)) hden.le)
          (collisionLower_nonneg _ _ _))
    let A := 1+tradeThetaThree U*elementarySum Finset.univ r 3 +
      tradeThetaHigher U V*(elementarySum Finset.univ r 4/3+
        elementarySum Finset.univ r 5+2*elementarySum Finset.univ r 6)
    have hbr : rectangleBracket sl sh ml mh ≤ A := by
      have h0 := mul_le_mul_of_nonneg_left (hB 0) h3.1
      have hh : rectangleB 1 sl sh ml mh/3+rectangleB 2 sl sh ml mh+
          2*rectangleB 3 sl sh ml mh ≤ elementarySum Finset.univ r 4/3+
            elementarySum Finset.univ r 5+2*elementarySum Finset.univ r 6 := by
        have h1 := hB 1
        have h2 := hB 2
        have h3 := hB 3
        norm_num at h1 h2 h3
        linarith
      have hh' := mul_le_mul_of_nonneg_left hh hH.1
      dsimp [A,rectangleBracket]
      dsimp [U,V] at h0 hh'
      linarith
    have hbr0 : 0 ≤ rectangleBracket sl sh ml mh := by
      have h0 := mul_nonneg h3.1 (hBnonneg 0)
      have hh := mul_nonneg hH.1
        (show 0 ≤ rectangleB 1 sl sh ml mh/3+rectangleB 2 sl sh ml mh+
          2*rectangleB 3 sl sh ml mh from
          add_nonneg (add_nonneg (div_nonneg (hBnonneg 1) (by norm_num)) (hBnonneg 2))
            (mul_nonneg (by norm_num) (hBnonneg 3)))
      dsimp [rectangleBracket]
      dsimp [U,V] at h0 hh
      linarith
    have hPl : rectangleP sh mh ≤ P := independent_product_rational_lower Finset.univ p mh sh (mh^2)
      (fun i _ => hp i) (fun i _ => hm i) hmh0 hmh hsh0 (sq_nonneg _) hSh hqh hX
    have hgain := mul_le_mul hPl hbr hbr0 hP
    have ht : (∑ T : Finset ι, P * ∏ i ∈ T, r i) = 1 := independentSubset_total p hlt
    have hcost := hc.2.2
    rw [ht, emptyBonus_product] at hcost
    change (∑ T : Finset ι, if T.Nonempty then
      combinedTrade (fun T => P * ∏ i ∈ T, r i)
        (productTrade r P (tradeThetaThree U) (tradeThetaHigher U V)) T else 0) ≤ _
    dsimp [A] at hgain
    nlinarith

end Erdos1017
