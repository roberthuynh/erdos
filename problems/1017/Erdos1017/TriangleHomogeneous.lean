import Erdos1017.TriangleScalar

namespace Erdos1017

theorem triangle_budget_homogeneous (a b Q : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hba : b ≤ 2*a) (hab : a ≤ b) (hQ : 0 ≤ Q) (hQcap : Q ≤ a*b) :
    a*b-(2*a+b)*(b^2-Q)/(6*b)+(Real.sqrt 7/3)*(((a+b)^2-a^2-Q)/2) ≤
      (1+Real.sqrt 7/3)*(a+b)^2/4 := by
  let n := a+b
  have hn : 0 < n := add_pos ha hb
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hn2 : 0 < n^2 := sq_pos_of_pos hn
  have hAl : (1:ℝ)/3 ≤ a/n := by apply (le_div_iff₀ hn).mpr; dsimp [n]; linarith
  have hAh : a/n ≤ (1:ℝ)/2 := by apply (div_le_iff₀ hn).mpr; dsimp [n]; linarith
  have hBn : 1-a/n=b/n := by dsimp [n]; field_simp; ring
  have hQn : Q/n^2 ≤ (a/n)*(1-a/n) := by
    rw [hBn]
    calc
      _ ≤ (a*b)/n^2 := (div_le_div_iff_of_pos_right hn2).mpr hQcap
      _ = _ := by field_simp
  have H := triangle_budget_sharp (a/n) (Q/n^2) hAl hAh (div_nonneg hQ hn2.le) hQn
  have Hn := mul_le_mul_of_nonneg_left H hn2.le
  have hcost : n^2*((a/n)*(1-a/n)-(1+a/n)*((1-a/n)^2-Q/n^2)/(6*(1-a/n))) =
      a*b-(2*a+b)*(b^2-Q)/(6*b) := by
    rw [hBn]
    dsimp [n]
    field_simp
    ring
  have hedge : n^2*((1-(a/n)^2-Q/n^2)/2)=((a+b)^2-a^2-Q)/2 := by
    dsimp [n]
    field_simp
  rw [mul_add] at Hn
  have hweighted := congrArg (fun z : ℝ => (Real.sqrt 7/3)*z) hedge
  dsimp [n] at hcost Hn hweighted
  nlinarith

end Erdos1017
