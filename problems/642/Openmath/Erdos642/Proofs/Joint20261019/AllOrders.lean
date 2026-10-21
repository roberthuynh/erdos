import Openmath.Erdos642.Proofs.Adaptive20261018.AllOrders

namespace Erdos642.Joint20261019.AllOrders

noncomputable def psi (n : ℕ) : ℝ := (n:ℝ)*Real.log (2*(n:ℝ))^4

@[simp] theorem psi_zero : psi 0 = 0 := by simp [psi]

theorem psi_pos (n : ℕ) (hn : 0<n) : 0<psi n := by
  have hnreal : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hl : 0<Real.log (2*(n:ℝ)) := Real.log_pos (by linarith)
  exact mul_pos hnreal (pow_pos hl _)

theorem psi_comparison (n : ℕ) (hn : 1≤n) :
    (n:ℝ)*Real.log (n:ℝ)^4/2 ≤ psi n := by
  have hnreal : (1:ℝ)≤n := by exact_mod_cast hn
  have hnpos : (0:ℝ)<n := by linarith
  have hl : 0≤Real.log (n:ℝ) := Real.log_nonneg hnreal
  have hp : Real.log (n:ℝ)^4 ≤ Real.log (2*(n:ℝ))^4 :=
    pow_le_pow_left₀ hl (Real.log_le_log hnpos (by linarith)) 4
  have hm := mul_le_mul_of_nonneg_left hp hnpos.le
  unfold psi
  nlinarith [mul_nonneg hnpos.le (pow_nonneg hl 4)]

end Erdos642.Joint20261019.AllOrders
