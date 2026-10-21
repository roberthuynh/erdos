import Openmath.Erdos643Design.Prime281
import Openmath.Erdos643Design.DesignTransport
import Mathlib.Data.Fintype.EquivFin

/-! Finite cyclic difference-family seed, relabeled on the exact finite order. -/
set_option autoImplicit false

namespace Erdos643Design.Seed281

noncomputable def pointEquiv : ZMod 281 ≃ Fin 281 :=
  Fintype.equivFinOfCardEq (ZMod.card 281)

noncomputable def blocks : Finset (Finset (Fin 281)) :=
  DesignTransport.relabel pointEquiv PrimeDifference281.supplied.developed

theorem isBlockDesign : blocks.IsBlockDesign 2 5 :=
  DesignTransport.isBlockDesign_relabel pointEquiv _ 2 5 PrimeDifference281.design

theorem exists_design : ∃ B : Finset (Finset (Fin 281)), B.IsBlockDesign 2 5 :=
  ⟨blocks, isBlockDesign⟩

end Erdos643Design.Seed281
