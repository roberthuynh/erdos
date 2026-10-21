import Erdos1017.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Erdos1017

/-- The exact scalar comparison in the partial-triangle route. -/
theorem triangle_budget_sharp (a Q : ℝ) (ha : (1:ℝ)/3 ≤ a) (ha2 : a ≤ (1:ℝ)/2)
    (hQ : 0 ≤ Q) (hQcap : Q ≤ a*(1-a)) :
    a*(1-a)-(1+a)*((1-a)^2-Q)/(6*(1-a)) +
      (Real.sqrt 7/3)*((1-a^2-Q)/2) ≤ (1+Real.sqrt 7/3)/4 := by
  let r := Real.sqrt 7
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2=7 := Real.sq_sqrt (by norm_num)
  have hr3 : r ≤ 3 := by nlinarith
  have hb : 0 < 1-a := by linarith
  have hden : 0 < 6*(1-a) := by positivity
  let gap := (1+r/3)/4 - (a*(1-a)-(1+a)*((1-a)^2-Q)/(6*(1-a))+(r/3)*((1-a^2-Q)/2))
  have hid : 6*(1-a)*gap =
      (1-a)*(5+r)*(a-(5-r)/6)^2 + (r*(1-a)-(1+a))*Q := by
    dsimp [gap]
    field_simp
    nlinarith [sq_nonneg (a-(5-r)/6), congrArg (fun z : ℝ => z*r) hr2,
      congrArg (fun z : ℝ => z*a) hr2, congrArg (fun z : ℝ => z*a^2) hr2]
  have hg : 0 ≤ 6*(1-a)*gap := by
    by_cases hcoef : 0 ≤ r*(1-a)-(1+a)
    · rw [hid]
      exact add_nonneg (mul_nonneg (mul_nonneg hb.le (by linarith)) (sq_nonneg _)) (mul_nonneg hcoef hQ)
    · have hcomp := mul_le_mul_of_nonpos_left hQcap (le_of_not_ge hcoef)
      have hend : (1-a)*(5+r)*(a-(5-r)/6)^2+(r*(1-a)-(1+a))*(a*(1-a)) =
          (1-a)*(1-2*a)*(5-r-4*a)/2 := by
        nlinarith [congrArg (fun z : ℝ => z*r) hr2,congrArg (fun z : ℝ => z*a) hr2,
          congrArg (fun z : ℝ => z*a^2) hr2]
      have hp : 0 ≤ (1-a)*(1-2*a)*(5-r-4*a)/2 := by
        exact div_nonneg (mul_nonneg (mul_nonneg hb.le (by linarith)) (by linarith)) (by norm_num)
      rw [hid]
      linarith
  have hgap : 0 ≤ gap := (nonneg_of_mul_nonneg_right hg hden)
  dsimp [gap,r] at hgap
  linarith

end Erdos1017
