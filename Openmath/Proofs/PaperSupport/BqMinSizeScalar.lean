import Openmath.Proofs.PaperSupport.BqMinSizeTypes
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.BqMinimumSupport
open QB4 B5
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Faithful formalization of the previously paid simple bipartite ceiling. -/
theorem dense_order {q : ℕ} {P Q : Finset V} (hq : 5 ≤ q)
    (hn : 2 ≤ #P + #Q) (he : (q - 1) * (#P + #Q) ≤ ec G P Q + q) :
    4 * q - 5 ≤ #P + #Q := by
  have hp := ec_le_product (G := G) P Q
  by_contra! hsmall
  have hqZ : (5 : ℤ) ≤ q := by exact_mod_cast hq
  zify at hn he hp hsmall
  rw [Bq.pred_cast hq] at he
  have hprod : (0 : ℤ) ≤ ((#P : ℤ) + #Q - 2) *
      (4 * (q : ℤ) - ((#P : ℤ) + #Q) - 6) :=
    mul_nonneg (by omega) (by omega)
  have hs := sq_nonneg ((#P : ℤ) - #Q)
  have hid :
      4 * (((q : ℤ) - 1) * ((#P : ℤ) + #Q) - q) - 4 * (#P : ℤ) * #Q =
      4 * ((q : ℤ) - 3) + (((#P : ℤ) + #Q) - 2) *
        (4 * (q : ℤ) - ((#P : ℤ) + #Q) - 6) + ((#P : ℤ) - #Q)^2 := by ring
  nlinarith
end Erdos585.BqMinimumSupport
