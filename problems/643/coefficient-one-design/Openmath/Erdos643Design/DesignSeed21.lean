import Openmath.Erdos643Design.ProjectivePlaneDesign
import Openmath.Erdos643Design.DesignTransport
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Fintype.EquivFin

/-! The 21-point, block-size-five seed from the projective plane over a four-element field. -/
set_option autoImplicit false
namespace Erdos643Design.Seed21

instance primeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
abbrev Field4 := GaloisField 2 2
noncomputable instance fieldFintype : Fintype Field4 := Fintype.ofFinite _
noncomputable instance fieldDecidableEq : DecidableEq Field4 := Classical.decEq _

theorem field_card : Fintype.card Field4 = 4 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)]
  decide

theorem plane_card : Fintype.card (Foundation.ProjectivePlane.Points Field4) = 21 := by
  rw [Foundation.ProjectivePlane.card_points, field_card]
  decide

/-- Relabel the actual field-plane points by exactly 21 finite indices. -/
noncomputable def pointEquiv : Foundation.ProjectivePlane.Points Field4 ≃ Fin 21 :=
  Fintype.equivFinOfCardEq plane_card

/-- Actual field-plane blocks transported by a bijection. -/
noncomputable def blocks : Finset (Finset (Fin 21)) :=
  DesignTransport.relabel pointEquiv (Foundation.ProjectivePlane.blocks (F := Field4))

theorem isBlockDesign : blocks.IsBlockDesign 2 5 := by
  have h := Foundation.ProjectivePlane.isBlockDesign (F := Field4)
  rw [field_card] at h
  exact DesignTransport.isBlockDesign_relabel pointEquiv _ 2 5 h

/-- The concrete order-21 seed, with no assumed design existence. -/
theorem exists_design : ∃ B : Finset (Finset (Fin 21)), B.IsBlockDesign 2 5 :=
  ⟨blocks, isBlockDesign⟩

end Erdos643Design.Seed21
