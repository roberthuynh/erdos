import Polarity
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic

namespace Erdos60.Construction
open scoped LinearAlgebra.Projectivization
open Projectivization Matrix
variable (K : Type*) [Field K]
abbrev Point := ℙ K (Fin 3 → K)

def dotPolarity : Erdos60.Geometry.Polarity (P := Point K) (L := Point K) where
  line := Equiv.refl _
  reciprocal := fun _x _y => Projectivization.orthogonal_comm

noncomputable def absoluteLine : Point K := mk K ![1,1,1] (by simp)

theorem absolute_iff_on_line [CharP K 2] (p : Point K) :
    p ∈ (dotPolarity K).line p ↔ p ∈ absoluteLine K := by
  induction p using Projectivization.ind with | h v hv =>
  change orthogonal (mk K v hv) (mk K v hv) ↔ orthogonal (mk K v hv) (absoluteLine K)
  rw [orthogonal_mk, absoluteLine, orthogonal_mk]
  simp only [dotProduct, Fin.sum_univ_succ, 
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.sum_univ_zero, add_zero, mul_one]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  constructor
  · intro h
    have hs : (v 0 + v 1 + v 2)^2 = 0 := by
      calc
        _ = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 +
          2 * (v 0 * v 1 + v 0 * v 2 + v 1 * v 2) := by ring
        _ = 0 := by rw [htwo, zero_mul, add_zero]; simpa [add_assoc] using h
    have hz : v 0 + v 1 + v 2 = 0 := (pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0)).mp hs
    simpa [add_assoc] using hz
  · intro h
    have heq : (v 0 + v 1 + v 2)^2 = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 := by
      calc
        _ = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 + 2 * (v 0 * v 1 + v 0 * v 2 + v 1 * v 2) := by ring
        _ = _ := by rw [htwo, zero_mul, add_zero]
    rw [add_assoc, h, zero_pow (by decide : (2:ℕ) ≠ 0)] at heq
    simpa [add_assoc] using heq.symm

theorem plane_order [Finite K] [DecidableEq K] :
    Configuration.ProjectivePlane.order (Point K) (Point K) = Nat.card K := by
  classical
  let : Fintype (Point K) := Fintype.ofFinite _
  have hp := Configuration.ProjectivePlane.card_points (Point K) (Point K)
  have hc := Projectivization.card_of_finrank K (Fin 3 → K)
    (by simp : Module.finrank K (Fin 3 → K) = 3)
  have hc' : Nat.card (Point K) = Nat.card K ^ 2 + Nat.card K + 1 := by
    simpa [Finset.sum_range_succ, pow_zero, pow_one, add_comm, add_left_comm, add_assoc] using hc
  rw [Nat.card_eq_fintype_card] at hc'
  nlinarith

theorem absolute_count [Finite K] [DecidableEq K] [CharP K 2] :
    Nat.card {p : Point K // p ∈ (dotPolarity K).line p} = Nat.card K + 1 := by
  have he : {p : Point K // p ∈ (dotPolarity K).line p} ≃
      {p : Point K // p ∈ absoluteLine K} :=
    Equiv.subtypeEquivRight (absolute_iff_on_line K)
  rw [Nat.card_congr he]
  change Configuration.pointCount (Point K) (absoluteLine K) = _
  rw [Configuration.ProjectivePlane.pointCount_eq, plane_order]

instance prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

noncomputable instance binaryFieldDecidable (k : ℕ) : DecidableEq (GaloisField 2 k) := Classical.decEq _

/-- Actual finite-field polarity at every nontrivial power of two, with
its order and number of absolute points. -/
theorem power_two_construction (k : ℕ) (hk : k ≠ 0) :
    ∃ π : Erdos60.Geometry.Polarity
        (P := Point (GaloisField 2 k)) (L := Point (GaloisField 2 k)),
      Configuration.ProjectivePlane.order
        (Point (GaloisField 2 k)) (Point (GaloisField 2 k)) = 2^k ∧
      Nat.card {p : Point (GaloisField 2 k) // p ∈ π.line p} = 2^k + 1 ∧
      ∃ l : Point (GaloisField 2 k), ∀ p, p ∈ π.line p ↔ p ∈ l := by
  classical
  refine ⟨dotPolarity _, ?_, ?_, absoluteLine _, absolute_iff_on_line _⟩
  · rw [plane_order, GaloisField.card 2 k hk]
  · rw [absolute_count, GaloisField.card 2 k hk]

#print axioms power_two_construction
#print axioms absolute_iff_on_line
#print axioms plane_order
#print axioms absolute_count
end Erdos60.Construction
