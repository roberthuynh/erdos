import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Erdos585.R882

def height (q : ℕ) : ℕ := ⌊Real.rpow (q:ℝ) (1/3:ℝ) / 3⌋₊

/-- Arithmetic for the literal four-thirds real deficit. -/
theorem quantitative_numeric (q : ℕ) (hq : 2^30 ≤ q) :
    6 ≤ height q ∧ 4096*(height q+1)^2 ≤ q ∧
    12*(height q:ℤ)^3-40*(height q:ℤ)^2+42*(height q:ℤ)-15 ≤ q ∧
    Real.rpow (q:ℝ) (4/3:ℝ)/8 ≤ (height q:ℝ)*q-16*(height q:ℝ)^2 := by
  let x : ℝ := Real.rpow (q:ℝ) (1/3:ℝ)
  have hq0 : (0:ℝ) ≤ q := by positivity
  have hqpos : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hx0 : 0 ≤ x := Real.rpow_nonneg hq0 _
  have hx3 : x^3 = (q:ℝ) := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0]
    norm_num
  have hqbig : (1024:ℝ)^3 ≤ (q:ℝ) := by exact_mod_cast hq
  have hxbig : 1024 ≤ x := by
    by_contra hn
    have hlt : x < 1024 := lt_of_not_ge hn
    have hp := pow_lt_pow_left₀ hlt hx0 (by norm_num : (3:ℕ) ≠ 0)
    linarith
  have hfloor : (height q:ℝ) ≤ x/3 := Nat.floor_le (by positivity)
  have hnext : x/3 < (height q:ℝ)+1 := Nat.lt_floor_add_one _
  have hh6 : 6 ≤ height q := Nat.le_floor (by change (6:ℝ) ≤ x/3; linarith)
  have hlow : x/4 ≤ (height q:ℝ) := by linarith
  have hupper : (height q:ℝ)+1 ≤ x/2 := by linarith
  have hcutreal : (4096:ℝ)*((height q:ℝ)+1)^2 ≤ q := calc
    (4096:ℝ)*((height q:ℝ)+1)^2 ≤ 4096*(x/2)^2 := by gcongr
    _ = 1024*x^2 := by ring
    _ ≤ x^3 := by nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ x-1024 by linarith)]
    _ = q := hx3
  have hcut : 4096*(height q+1)^2 ≤ q := by exact_mod_cast hcutreal
  have hhcube : 12*(height q:ℝ)^3 ≤ 4*(q:ℝ)/9 := by
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ height q) hfloor 3
    nlinarith
  have hsmall : -40*(height q:ℝ)^2+42*(height q:ℝ)-15 ≤ 0 := by
    have hh6real : (6:ℝ) ≤ height q := by exact_mod_cast hh6
    nlinarith [sq_nonneg (height q:ℝ)]
  have hcubereal : 12*(height q:ℝ)^3-40*(height q:ℝ)^2+42*(height q:ℝ)-15 ≤ q := by
    linarith
  have hcube : 12*(height q:ℤ)^3-40*(height q:ℤ)^2+42*(height q:ℤ)-15 ≤ q := by
    exact_mod_cast hcubereal
  have hp4 : Real.rpow (q:ℝ) (4/3:ℝ) = x*q := by
    change (q:ℝ) ^ (4/3:ℝ) = x*q
    rw [show (4/3:ℝ) = 1/3+1 by norm_num, Real.rpow_add hqpos, Real.rpow_one]
    rfl
  have hsquare : 16*(height q:ℝ)^2 ≤ (16/9:ℝ)*x^2 := by
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ height q) hfloor 2
    nlinarith
  have hlinear : x*q/4 ≤ (height q:ℝ)*q := by nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hlow)]
  have hxq : (128/9:ℝ)*x^2 ≤ x*q := by
    rw [← hx3]
    have hs : (128/9:ℝ) ≤ x^2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hs)]
  refine ⟨hh6,hcut,hcube,?_⟩
  rw [hp4]
  nlinarith

#print axioms quantitative_numeric
end Erdos585.R882
