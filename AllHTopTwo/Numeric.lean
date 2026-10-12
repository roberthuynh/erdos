import AllHTopTwo.Interface

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHTopTwo

lemma offset_cast (h : ℕ) : (offset h : ℤ) = (h : ℤ) ^ 2 + 5 * h + 8 := by
  simp [offset]

namespace Parameters
variable {h q j : ℕ} (p : Parameters h q j)
include p

lemma height_int : (3 : ℤ) ≤ h := by exact_mod_cast p.height

lemma large_int : 1024 * ((h : ℤ) + 1) ^ 2 ≤ q := by exact_mod_cast p.large

lemma branch_int : (j : ℤ) = (h : ℤ) - 2 ∨ (j : ℤ) = (h : ℤ) - 1 := by
  have hh := p.height
  rcases p.branch with hj | hj
  · left; omega
  · right; omega

lemma j_pos : 0 < j := by have hh := p.height; rcases p.branch with hj | hj <;> omega

lemma j_bounds : (h : ℤ) - 2 ≤ j ∧ (j : ℤ) ≤ (h : ℤ) - 1 := by
  rcases p.branch_int with hj | hj <;> omega

/-- Consequences of the literal quadratic cutoff; no stronger numerical guard is supplied. -/
lemma numeric :
    4 * (offset h : ℤ) + 100 * (h : ℤ) ^ 2 ≤ q ∧
    5 * (h : ℤ) < offset h ∧
    3 * (j : ℤ) + 2 < offset h ∧
    6 * (h : ℤ) < q ∧
    (offset h : ℤ) + 4 * h < q ∧
    40 * (h : ℤ) ^ 2 < q := by
  have hh := p.height_int
  have hq := p.large_int
  have hj := p.j_bounds
  rw [offset_cast]
  constructor
  · nlinarith [sq_nonneg (h : ℤ)]
  constructor
  · nlinarith [sq_nonneg (h : ℤ)]
  constructor
  · nlinarith [sq_nonneg (h : ℤ)]
  constructor
  · nlinarith [sq_nonneg (h : ℤ)]
  constructor
  · nlinarith [sq_nonneg (h : ℤ)]
  · nlinarith [sq_nonneg (h : ℤ)]

lemma q_pos : 0 < q := by have hn := p.numeric; have hh := p.height; omega

lemma q_ge_height : h + 3 ≤ q := by have hn := p.numeric; have hh := p.height; omega

lemma offset_le_product : offset h ≤ h * q := by
  have hn := p.numeric
  have hh := p.height_int
  have hp : (offset h : ℤ) ≤ (h : ℤ) * q := by
    nlinarith [mul_nonneg (show 0 ≤ (h : ℤ) - 1 by omega) (show 0 ≤ (q : ℤ) by omega)]
  exact_mod_cast hp

lemma constant_cast : (constant h q : ℤ) = (h : ℤ) * q - offset h := by
  unfold constant
  rw [Nat.cast_sub p.offset_le_product, Nat.cast_mul]

lemma scar_upper : (h : ℤ) * q - offset h - ((q : ℤ) - 1) * j < 2 * q := by
  have hn := p.numeric
  have hh := p.height_int
  have hq := p.q_pos
  rcases p.branch_int with hj | hj <;> rw [hj] <;> nlinarith

lemma scar_lower : (q : ℤ) - offset h ≤
    (h : ℤ) * q - offset h - ((q : ℤ) - 1) * j := by
  have hq := p.q_pos
  have hj := p.j_pos
  rcases p.branch_int with hj | hj <;> rw [hj] <;> nlinarith

lemma scar_tiny : (h : ℤ) * q - offset h - ((q : ℤ) - 1) * j <
    2 * ((q : ℤ) - h) := by
  have hn := p.numeric
  have hh := p.height_int
  have hq := p.q_pos
  rcases p.branch_int with hj | hj <;> rw [hj] <;> nlinarith

lemma scar_weak : (h : ℤ) * q - offset h - ((q : ℤ) - 1) * j <
    2 * ((q : ℤ) - j - 1) := by
  have hn := p.numeric
  have hh := p.height_int
  have hq := p.q_pos
  rcases p.branch_int with hj | hj <;> rw [hj] at * <;> nlinarith

end Parameters
end Erdos585.AllHTopTwo
