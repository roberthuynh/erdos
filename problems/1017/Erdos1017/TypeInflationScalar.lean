import Erdos1017.TypeBudget

namespace Erdos1017

theorem type_inflation_scalar (a b Q : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hQ : 0 ≤ Q)
    (hsize : 8*b ≤ 17*a) :
    (2*a/b)*(b^2/6+Q/3)+(1-2*a/b)*((1-Real.sqrt 7/3)*b^2/4+(Real.sqrt 7/3)*Q/2) ≤
      (1-Real.sqrt 7/3)*(a+b)^2/4+(Real.sqrt 7/3)*(a^2+Q)/2 := by
  let r := Real.sqrt 7/3
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hsq : (Real.sqrt 7)^2=7 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg _
  have hrlo : (2:ℝ)/3 ≤ r := by dsimp [r]; nlinarith
  have hrhi : r ≤ (8:ℝ)/9 := by dsimp [r]; nlinarith
  have hbase : 0 ≤ (1+r)*a/4+((2:ℝ)/3-r)*b := by
    have hw := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 1+r by linarith)
    have hm := mul_nonneg (show 0 ≤ 8-9*r by linarith) hb.le
    nlinarith
  have hterm : 0 ≤ (r-(2:ℝ)/3)*Q/b := div_nonneg (mul_nonneg (sub_nonneg.mpr hrlo) hQ) hb.le
  have hgap : 0 ≤ a*((1+r)*a/4+((2:ℝ)/3-r)*b+(r-(2:ℝ)/3)*Q/b) :=
    mul_nonneg ha (add_nonneg hbase hterm)
  have hid :
      ((1-r)*(a+b)^2/4+r*(a^2+Q)/2) -
      ((2*a/b)*(b^2/6+Q/3)+(1-2*a/b)*((1-r)*b^2/4+r*Q/2)) =
      a*((1+r)*a/4+((2:ℝ)/3-r)*b+(r-(2:ℝ)/3)*Q/b) := by
    field_simp
    ring
  change (2*a/b)*(b^2/6+Q/3)+(1-2*a/b)*((1-r)*b^2/4+r*Q/2) ≤
    (1-r)*(a+b)^2/4+r*(a^2+Q)/2
  linarith

end Erdos1017
