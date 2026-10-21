import Openmath.Erdos643Design.Prime61
import Openmath.Erdos643Design.DesignTransport
import Mathlib.Data.Fintype.EquivFin

/-! Finite cyclic difference-family seed, relabeled on the exact finite order. -/
set_option autoImplicit false

namespace Erdos643Design.Seed61

noncomputable def pointEquiv : ZMod 61 ≃ Fin 61 :=
  Fintype.equivFinOfCardEq (ZMod.card 61)

noncomputable def blocks : Finset (Finset (Fin 61)) :=
  DesignTransport.relabel pointEquiv PrimeDifference61.supplied.developed

theorem isBlockDesign : blocks.IsBlockDesign 2 5 :=
  DesignTransport.isBlockDesign_relabel pointEquiv _ 2 5 PrimeDifference61.design

theorem exists_design : ∃ B : Finset (Finset (Fin 61)), B.IsBlockDesign 2 5 :=
  ⟨blocks, isBlockDesign⟩

end Erdos643Design.Seed61
