import Openmath.Erdos643Design.Prime41
import Openmath.Erdos643Design.DesignTransport
import Mathlib.Data.Fintype.EquivFin

/-! Finite cyclic difference-family seed, relabeled on the exact finite order. -/
set_option autoImplicit false

namespace Erdos643Design.Seed41

noncomputable def pointEquiv : ZMod 41 ≃ Fin 41 :=
  Fintype.equivFinOfCardEq (ZMod.card 41)

noncomputable def blocks : Finset (Finset (Fin 41)) :=
  DesignTransport.relabel pointEquiv PrimeDifference41.supplied.developed

theorem isBlockDesign : blocks.IsBlockDesign 2 5 :=
  DesignTransport.isBlockDesign_relabel pointEquiv _ 2 5 PrimeDifference41.design

theorem exists_design : ∃ B : Finset (Finset (Fin 41)), B.IsBlockDesign 2 5 :=
  ⟨blocks, isBlockDesign⟩

end Erdos643Design.Seed41
