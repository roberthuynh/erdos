import Erdos1017.TradeParameters
import Erdos1017.OddsCorrection

namespace Erdos1017

theorem tradeDenominator_pos (U : ℝ) (hU : 0 < U) : 0 < tradeDenominator U := by
  unfold tradeDenominator
  positivity

theorem tradeDenominator_mono (U Uh : ℝ) (hU : 0 ≤ U) (h : U ≤ Uh) :
    tradeDenominator U ≤ tradeDenominator Uh := by
  have h2 := pow_le_pow_left₀ hU h 2
  have h3 := pow_le_pow_left₀ hU h 3
  have h4 := pow_le_pow_left₀ hU h 4
  unfold tradeDenominator
  linarith

theorem tradeThetaThree_antitone (U Uh : ℝ) (hU : 0 < U) (h : U ≤ Uh) :
    tradeThetaThree Uh ≤ tradeThetaThree U := by
  exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hU) (pow_le_pow_left₀ hU.le h 2)

theorem tradeThetaHigher_rectangle (U Uh V Vl : ℝ)
    (hU : 0 < U) (hUU : U ≤ Uh) (hVl : 0 ≤ Vl) (hV : Vl ≤ V) :
    tradeThetaHigher Uh Vl ≤ tradeThetaHigher U V := by
  have hUhp : 0 < Uh := hU.trans_le hUU
  have ht := tradeThetaThree_antitone U Uh hU hUU
  have h3 : 0 ≤ tradeThetaThree U := by unfold tradeThetaThree; positivity
  have hnum : 1+tradeThetaThree Uh*Vl ≤ 1+tradeThetaThree U*V :=
    add_le_add_right (mul_le_mul ht hV hVl h3) 1
  unfold tradeThetaHigher
  apply min_le_min (le_refl 1)
  calc
    _ ≤ (1+tradeThetaThree U*V)/tradeDenominator Uh :=
      div_le_div_of_nonneg_right hnum (tradeDenominator_pos Uh hUhp).le
    _ ≤ _ := div_le_div_of_nonneg_left (by nlinarith)
      (tradeDenominator_pos U hU) (tradeDenominator_mono U Uh hU.le hUU)

theorem correction_delta_rectangle (S Sh q ql : ℝ)
    (hS : 0 < S) (hSh : S ≤ Sh) (hq0 : 0 ≤ ql) (hq : ql ≤ q) (hgap : q < S) :
    Sh*ql/(Sh-ql) ≤ S*q/(S-q) := by
  have hd : 0 < Sh-ql := by linarith
  apply (div_le_div_iff₀ hd (sub_pos.mpr hgap)).mpr
  have h1 := mul_nonneg (mul_nonneg hS.le (hS.le.trans hSh)) (sub_nonneg.mpr hq)
  have h2 := mul_nonneg (mul_nonneg (hq0.trans hq) hq0) (sub_nonneg.mpr hSh)
  nlinarith

noncomputable def correctedLower (k : ℕ) (S q m : ℝ) : ℝ :=
  collisionLower (k+1) S q + (S*q/(S-q))*collisionLower k (S-m) q

noncomputable def rectangleCorrectedLower (k : ℕ) (sl sh ql qh mh : ℝ) : ℝ :=
  collisionLower (k+1) sl qh + (sh*ql/(sh-ql))*collisionLower k (sl-mh) qh

theorem correctedLower_rectangle (k : ℕ) (S q m sl sh ql qh mh : ℝ)
    (hsl : 0 < sl) (hSl : sl ≤ S) (hSh : S ≤ sh)
    (hql : 0 ≤ ql) (hqlq : ql ≤ q) (hqh : q ≤ qh) (hgap : q < S)
    (hm : m ≤ mh) (hsm : 0 ≤ sl-mh) :
    rectangleCorrectedLower k sl sh ql qh mh ≤ correctedLower k S q m := by
  have hSp : 0 < S := hsl.trans_le hSl
  have hbase : collisionLower (k+1) sl qh ≤ collisionLower (k+1) S q :=
    (collisionLower_mono_sum (k+1) sl S qh hsl.le hSl).trans
      (collisionLower_antitone_square (k+1) S q qh hSp.le hqh)
  have hsmall : collisionLower k (sl-mh) qh ≤ collisionLower k (S-m) q :=
    (collisionLower_mono_sum k (sl-mh) (S-m) qh hsm (by linarith)).trans
      (collisionLower_antitone_square k (S-m) q qh (by linarith) hqh)
  have hdelta := correction_delta_rectangle S sh q ql hSp hSh hql hqlq hgap
  have hdelta0 : 0 ≤ S*q/(S-q) := div_nonneg (mul_nonneg hSp.le (hql.trans hqlq)) (sub_pos.mpr hgap).le
  exact add_le_add hbase (mul_le_mul hdelta hsmall (collisionLower_nonneg _ _ _) hdelta0)

end Erdos1017
