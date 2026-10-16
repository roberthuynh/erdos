import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Erdos585.R874

/-- The internally chosen height for the real quantitative deficit. -/
def height (q : ℕ) : ℕ := ⌊Real.rpow (q:ℝ) (1/4:ℝ) / 128⌋₊

/-- All arithmetic required to call the every-height original-graph theorem. -/
theorem numeric (q : ℕ) (hq : 2^40 ≤ q) :
    6 ≤ height q ∧ 2^24*(height q+1)^4 ≤ q ∧
    Real.rpow (q:ℝ) (5/4:ℝ)/512 ≤ (height q:ℝ)*q-16*(height q:ℝ)^2 := by
  let x : ℝ := Real.rpow (q:ℝ) (1/4:ℝ)
  have hq0 : (0:ℝ) ≤ q := by positivity
  have hqpos : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hx0 : 0 ≤ x := Real.rpow_nonneg hq0 _
  have hx4 : x^4 = (q:ℝ) := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0]
    norm_num
  have hqbig : (1024:ℝ)^4 ≤ (q:ℝ) := by exact_mod_cast hq
  have hxbig : 1024 ≤ x := by
    by_contra hn
    have hlt : x < 1024 := lt_of_not_ge hn
    have hp := pow_lt_pow_left₀ hlt hx0 (by norm_num : (4:ℕ) ≠ 0)
    linarith
  have hfloor : (height q:ℝ) ≤ x/128 := Nat.floor_le (by positivity)
  have hnext : x/128 < (height q:ℝ)+1 := Nat.lt_floor_add_one _
  have hh8 : 8 ≤ height q := Nat.le_floor (by change (8:ℝ) ≤ x/128; linarith)
  have hlow : x/256 ≤ (height q:ℝ) := by linarith
  have hupper : (height q:ℝ)+1 ≤ x/64 := by linarith
  have hcutreal : (2:ℝ)^24*((height q:ℝ)+1)^4 ≤ q := calc
    (2:ℝ)^24*((height q:ℝ)+1)^4 ≤ (2:ℝ)^24*(x/64)^4 := by
      gcongr
    _ = x^4 := by ring
    _ = q := hx4
  have hcut : 2^24*(height q+1)^4 ≤ q := by exact_mod_cast hcutreal
  have hp5 : Real.rpow (q:ℝ) (5/4:ℝ) = x*q := by
    change (q:ℝ) ^ (5/4:ℝ) = x*q
    rw [show (5/4:ℝ) = 1/4+1 by norm_num, Real.rpow_add hqpos, Real.rpow_one]
    rfl
  have hxsq : 1 ≤ x^2 := by nlinarith
  have hxq : x ≤ (q:ℝ) := by nlinarith [sq_nonneg (x^2-1)]
  have hprod : x^2 ≤ x*q := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hxq)]
  have hsquare : 16*(height q:ℝ)^2 ≤ x^2/1024 := by
    have hh0 : (0:ℝ) ≤ height q := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hfloor) (add_nonneg hx0 (by positivity : (0:ℝ) ≤ 128*(height q:ℝ)))]
  have hlinear : x*q/256 ≤ (height q:ℝ)*q := by nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hlow)]
  refine ⟨by omega, hcut, ?_⟩
  rw [hp5]
  nlinarith

#print axioms numeric
end Erdos585.R874
