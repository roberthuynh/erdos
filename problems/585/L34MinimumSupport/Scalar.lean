import L34.Main
import Openmath.Proofs.PaperSupport.BqMinSizeMain

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.L34MinimumSupport
open QB4 B5
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The actual original bipartite product ceiling pays the critical source size. -/
theorem dense_order {q : ℕ} {P Q : Finset V} (hq : 6 ≤ q)
    (hn : 2 * q ≤ #P + #Q)
    (he : (q - 1) * (#P + #Q) ≤ ec G P Q + (2 * q - 5)) :
    4 * q - 5 ≤ #P + #Q := by
  have hp := ec_le_product (G := G) P Q
  by_contra! hsmall
  have hqZ : (6 : ℤ) ≤ q := by exact_mod_cast hq
  zify at hn he hp hsmall
  rw [Bq.pred_cast (by omega), L34.constant_cast hq] at he
  have hprod : (0 : ℤ) ≤ ((#P : ℤ) + #Q - 2) *
      (4 * (q : ℤ) - ((#P : ℤ) + #Q) - 6) :=
    mul_nonneg (by omega) (by omega)
  have hs := sq_nonneg ((#P : ℤ) - #Q)
  have hid :
      4 * (((q : ℤ) - 1) * ((#P : ℤ) + #Q) - (2 * q - 5)) -
        4 * (#P : ℤ) * #Q =
      8 + (((#P : ℤ) + #Q) - 2) *
        (4 * (q : ℤ) - ((#P : ℤ) + #Q) - 6) + ((#P : ℤ) - #Q)^2 := by ring
  nlinarith

end Erdos585.L34MinimumSupport
