import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Erdos585.R898

def height (q : ℕ) : ℕ := ⌊Real.sqrt (q : ℝ) / 64⌋₊ - 1

/-- Literal three-halves real arithmetic at the quadratic cutoff. -/
theorem quantitative_numeric (q : ℕ) (hq : 2^18 ≤ q) :
    6 ≤ height q ∧ 4096*(height q+1)^2 ≤ q ∧
    Real.rpow (q:ℝ) (3/2:ℝ)/128 ≤ (height q:ℝ)*q-16*(height q:ℝ)^2 := by
  let x : ℝ := Real.sqrt (q:ℝ)
  have hq0 : (0:ℝ) ≤ q := by positivity
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x^2 = (q:ℝ) := Real.sq_sqrt hq0
  have hqbig : (512:ℝ)^2 ≤ (q:ℝ) := by exact_mod_cast hq
  have hxbig : 512 ≤ x := by nlinarith
  have hf8 : 8 ≤ ⌊x/64⌋₊ := Nat.le_floor (by linarith)
  have hheight : height q + 1 = ⌊x/64⌋₊ := by
    change ⌊x/64⌋₊ - 1 + 1 = ⌊x/64⌋₊
    omega
  have hfloor : (height q:ℝ)+1 ≤ x/64 := by
    have hf := Nat.floor_le (show 0 ≤ x/64 by positivity)
    rw [← hheight] at hf
    exact_mod_cast hf
  have hnext : x/64 < (height q:ℝ)+2 := by
    have hf := Nat.lt_floor_add_one (x/64)
    rw [← hheight] at hf
    exact_mod_cast hf
  have hh6 : 6 ≤ height q := by omega
  have hupper : (height q:ℝ) ≤ x/64 := by linarith
  have hlow : x/64-2 ≤ (height q:ℝ) := by linarith
  have hcutreal : (4096:ℝ)*((height q:ℝ)+1)^2 ≤ q := calc
    (4096:ℝ)*((height q:ℝ)+1)^2 ≤ 4096*(x/64)^2 := by gcongr
    _ = x^2 := by ring
    _ = q := hx2
  have hcut : 4096*(height q+1)^2 ≤ q := by exact_mod_cast hcutreal
  have hp3 : Real.rpow (q:ℝ) (3/2:ℝ) = x*q := by
    change (q:ℝ) ^ (3/2:ℝ) = x*q
    rw [show (3/2:ℝ) = 1/2+1 by norm_num,
      Real.rpow_add (show (0:ℝ) < q by exact_mod_cast (show 0 < q by omega)),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hsquare : 16*(height q:ℝ)^2 ≤ x^2/256 := by
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ height q) hupper 2
    nlinarith
  have hlinear : (x/64-2)*q ≤ (height q:ℝ)*q := by
    exact mul_le_mul_of_nonneg_right hlow hq0
  have hreserve : (513/256:ℝ)*x^2 ≤ x^3/128 := by
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ x-513/2 by linarith)]
  refine ⟨hh6, hcut, ?_⟩
  rw [hp3]
  nlinarith [show x*q = x^3 by rw [← hx2]; ring]

#print axioms quantitative_numeric
end Erdos585.R898
