import Openmath.Proofs.PaperSupport.R400Next.Interface

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHNextH3R400
namespace Parameters
variable {h q a j : ℕ} (p : Parameters h q a j)
include p

lemma height_int : (3 : ℤ) ≤ h := by exact_mod_cast p.height

lemma large_int : 1024 * ((h : ℤ) + 1) ^ 2 ≤ q := by exact_mod_cast p.large

lemma height_eq_int : (h : ℤ) = 3 := by exact_mod_cast p.exact_height

lemma lower_int : (16 : ℤ) ≤ a := by exact_mod_cast p.lower

lemma upper_int : (a : ℤ) ≤ (h : ℤ) ^ 2 + 5 * h + 8 := by exact_mod_cast p.upper

lemma surplus_int : (j : ℤ) = (h : ℤ) - 2 := by
  have hh := p.height
  have hj := p.surplus
  omega

lemma j_pos : 0 < j := by have hh := p.height; have hj := p.surplus; omega

lemma j_bounds : (h : ℤ) - 2 ≤ j ∧ (j : ℤ) ≤ (h : ℤ) - 2 := by
  have hj := p.surplus_int
  omega

/-- Consequences over the exact height-three interval 16 ≤ a ≤ 32. -/
lemma numeric :
    4 * (a : ℤ) + 100 * (h : ℤ) ^ 2 ≤ q ∧
    5 * (h : ℤ) < a ∧
    3 * (j : ℤ) + 2 < a ∧
    6 * (h : ℤ) < q ∧
    (a : ℤ) + 4 * h < q ∧
    40 * (h : ℤ) ^ 2 < q := by
  have hh := p.height_int
  have hq := p.large_int
  have hlo := p.lower_int
  have h3 := p.height_eq_int
  have hhi := p.upper_int
  have hj := p.j_bounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (h : ℤ)]

lemma q_pos : 0 < q := by have hn := p.numeric; have hh := p.height; omega

lemma q_ge_height : h + 3 ≤ q := by have hn := p.numeric; have hh := p.height; omega

lemma offset_le_product : a ≤ h * q := by
  have hn := p.numeric
  have hh := p.height_int
  have hp : (a : ℤ) ≤ (h : ℤ) * q := by
    nlinarith [mul_nonneg (show 0 ≤ (h : ℤ) - 1 by omega) (show 0 ≤ (q : ℤ) by omega)]
  exact_mod_cast hp

lemma constant_cast : (constant h q a : ℤ) = (h : ℤ) * q - a := by
  unfold constant
  rw [Nat.cast_sub p.offset_le_product, Nat.cast_mul]

lemma scar_eq : (h : ℤ) * q - a - ((q : ℤ) - 1) * j = 2 * (q : ℤ) + j - a := by
  rw [p.surplus_int]
  ring

lemma scar_upper : (h : ℤ) * q - a - ((q : ℤ) - 1) * j < 2 * q := by
  rw [p.scar_eq]
  have hn := p.numeric
  have hj := p.j_bounds
  have hh := p.height_int
  omega

lemma scar_lower : (q : ℤ) - a ≤ (h : ℤ) * q - a - ((q : ℤ) - 1) * j := by
  rw [p.scar_eq]
  omega

lemma scar_tiny : (h : ℤ) * q - a - ((q : ℤ) - 1) * j < 2 * ((q : ℤ) - h) := by
  rw [p.scar_eq]
  have hlo := p.lower_int
  have h3 := p.height_eq_int
  have hj := p.j_bounds
  have hh := p.height_int
  omega

lemma scar_weak : (h : ℤ) * q - a - ((q : ℤ) - 1) * j < 2 * ((q : ℤ) - j - 1) := by
  rw [p.scar_eq]
  have hlo := p.lower_int
  have h3 := p.height_eq_int
  have hj := p.j_bounds
  have hh := p.height_int
  omega

end Parameters
end Erdos585.AllHNextH3R400
