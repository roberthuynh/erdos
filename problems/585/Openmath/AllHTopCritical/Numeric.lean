import Openmath.AllHTopCritical.Interface

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.AllHTopCritical
namespace Parameters
variable {h q : ℕ} (p : Parameters h q)
include p

lemma height_int : (3 : ℤ) ≤ h := by exact_mod_cast p.height
lemma large_int : 1024 * ((h : ℤ) + 1) ^ 2 ≤ q := by exact_mod_cast p.large
omit p in
lemma offset_cast : (offset h : ℤ) = (h : ℤ)^2 + 5*h + 8 := by
  simp [offset]

lemma numeric :
    4 * (offset h : ℤ) + 100 * (h : ℤ)^2 ≤ q ∧
    (offset h : ℤ) + 4*h + 4 < q ∧
    6 * (h : ℤ) + 10 < q ∧
    8 * (h : ℤ) + 1 ≤ offset h := by
  have hh := p.height_int
  have hq := p.large_int
  rw [offset_cast (h := h)]
  constructor
  · nlinarith [sq_nonneg (h : ℤ)]
  constructor
  · nlinarith [sq_nonneg (h : ℤ)]
  constructor
  · nlinarith [sq_nonneg (h : ℤ)]
  · nlinarith [sq_nonneg ((h : ℤ)-2)]

lemma q_pos : 0 < q := by have hn := p.numeric; have hh := p.height; omega
lemma q_ge : h + 4 ≤ q := by have hn := p.numeric; have hh := p.height; omega
lemma offset_le_product : offset h ≤ h*q := by
  have hn := p.numeric
  have hh := p.height_int
  have hz : (offset h : ℤ) ≤ (h : ℤ)*q := by
    nlinarith [mul_nonneg (show 0 ≤ (h : ℤ)-1 by omega) (show 0 ≤ (q : ℤ) by omega)]
  exact_mod_cast hz
lemma constant_cast : (constant h q : ℤ) = (h : ℤ)*q-offset h := by
  unfold constant
  rw [Nat.cast_sub p.offset_le_product, Nat.cast_mul]
lemma surplus_cast : ((h-1 : ℕ) : ℤ) = (h : ℤ)-1 := by have hh := p.height; omega
lemma bound_cast : ((2*q-h-1 : ℕ) : ℤ) = 2*(q : ℤ)-h-1 := by
  have hq := p.q_ge
  omega
lemma root_bound_cast : ((2*h-2 : ℕ) : ℤ) = 2*(h : ℤ)-2 := by
  have hh := p.height
  omega
lemma retained_bound_cast : ((4*q-3*h-1 : ℕ) : ℤ) = 4*(q : ℤ)-3*h-1 := by
  have hn := p.numeric
  have hh := p.height
  omega
lemma kappa : 0 < (q : ℤ)+h-offset h ∧
    (q : ℤ)+h-offset h < q-1 ∧
    (q : ℤ)+h-offset h < 2*q-h-2 := by
  have hn := p.numeric
  have hh := p.height_int
  omega
lemma selector_cast : (selectorOffset h : ℤ) = (offset h : ℤ)-1 := by
  unfold selectorOffset
  have hn := p.numeric
  have hh := p.height
  omega
lemma largest_parameters :
    AllHLargestNonstrict.Parameters h q (selectorOffset h) (h-1) := by
  refine ⟨p.height, p.large, ?_, ?_, rfl⟩
  · have hn := p.numeric; have hh := p.height
    unfold selectorOffset
    omega
  · unfold selectorOffset offset
    omega
lemma next_parameters :
    AllHNextNonstrict.Parameters h q (selectorOffset h) (h-2) := by
  refine ⟨p.height, p.large, ?_, ?_, rfl⟩
  · have hn := p.numeric; have hh := p.height
    unfold selectorOffset
    omega
  · unfold selectorOffset offset
    omega

/-- Simplicity's quadratic bound excludes the entire intermediate interval. -/
lemma quadratic_order {x : ℕ} (hx : 1 ≤ x)
    (he : (x : ℤ)*(2*q-h-1-x) ≤ (q : ℤ)+h-offset h) :
    2*q-h-1 ≤ x := by
  have hb := p.bound_cast
  have hk := p.kappa
  by_contra hn
  have hc : (x : ℤ) < 2*q-h-1 := by omega
  have hm := mul_nonneg (show 0 ≤ (x : ℤ)-1 by omega)
    (show 0 ≤ 2*(q : ℤ)-h-2-x by omega)
  nlinarith

/-- The missing original floor at every order h,...,2q-1, before any selector. -/
lemma small_floor {m e : ℕ} (hm : h ≤ m) (ht : m < 2*q)
    (he : 4*(e : ℤ) ≤ (m : ℤ)^2) :
    (constant h q : ℤ)+1 ≤ ((q : ℤ)-1)*m-e := by
  have hh := p.height_int
  have hq := p.large_int
  have hn := p.numeric
  have hc := p.constant_cast
  have ha := offset_cast (h := h)
  have hmz : (h : ℤ) ≤ m := by exact_mod_cast hm
  have htz : (m : ℤ) ≤ 2*q-1 := by omega
  have hp := mul_nonneg (show 0 ≤ (m : ℤ)-h by omega)
    (show 0 ≤ 2*(q : ℤ)-1-m by omega)
  have hl : 4*(((q : ℤ)-1)*h-((h : ℤ)*q-offset h+1))-(h : ℤ)^2 ≥ 0 := by
    nlinarith [sq_nonneg (h : ℤ)]
  have hu : 4*(((q : ℤ)-1)*(2*q-1)-((h : ℤ)*q-offset h+1))-(2*(q : ℤ)-1)^2 ≥ 0 := by
    have hz := mul_nonneg (show 0 ≤ (q : ℤ) by omega)
      (show 0 ≤ (q : ℤ)-h-2 by omega)
    nlinarith [sq_nonneg (h : ℤ)]
  have hi := mul_nonneg (show 0 ≤ (m : ℤ)-h by omega) hu
  have hj := mul_nonneg (show 0 ≤ 2*(q : ℤ)-1-m by omega) hl
  have hden : 0 < 2*(q : ℤ)-1-h := by omega
  have hpoly : 0 ≤ (2*(q : ℤ)-1-h)*
      (4*(((q : ℤ)-1)*m-((h : ℤ)*q-offset h+1))-(m : ℤ)^2) := by
    nlinarith [mul_nonneg hden.le hp]
  have hf : 0 ≤ 4*(((q : ℤ)-1)*m-((h : ℤ)*q-offset h+1))-(m : ℤ)^2 := by
    exact nonneg_of_mul_nonneg_right hpoly hden
  nlinarith

end Parameters
end Erdos585.AllHTopCritical
