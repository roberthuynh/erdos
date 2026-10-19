import Openmath.Erdos643Design.DifferenceMatrix

/-! Column restriction and the multiplication difference matrix of a field. -/
set_option autoImplicit false

namespace Erdos643Design.Foundation
namespace DifferenceMatrix

variable {I J G : Type*} [AddCommGroup G]

/-- Selecting distinct columns of a supplied difference matrix preserves its property. -/
def restrict (D : DifferenceMatrix I G) (e : J ↪ I) : DifferenceMatrix J G where
  matrix := fun r j => D.matrix r (e j)
  difference_bijective := by
    intro i j hij
    exact D.difference_bijective (e i) (e j) (fun h => hij (e.injective h))

/-- Field multiplication gives a difference matrix with one column for each field element.
This applies in particular to every supplied finite field; no field existence is assumed. -/
def field (F : Type*) [Field F] : DifferenceMatrix F F where
  matrix := fun r i => r * i
  difference_bijective := by
    intro i j hij
    have hn : i-j ≠ 0 := sub_ne_zero.mpr hij
    constructor
    · intro a b hab
      have he : a * (i-j) = b * (i-j) := by
        simpa only [mul_sub] using hab
      exact mul_right_cancel₀ hn he
    · intro x
      refine ⟨x / (i-j), ?_⟩
      change x / (i-j) * i - x / (i-j) * j = x
      rw [← mul_sub, div_mul_cancel₀ x hn]

end DifferenceMatrix
end Erdos643Design.Foundation
