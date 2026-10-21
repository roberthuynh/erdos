import Openmath.Erdos643Design.DifferenceFamilyCertificate
import Openmath.Erdos643Design.DesignTransport
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.EquivFin

/-! An independently searched finite cyclic seed, certified by exact directed counts. -/
set_option autoImplicit false

namespace Erdos643Design.CyclicSeed81
open Erdos643Design.DifferenceFamily

def base : Finset (Finset (ZMod 81)) := {
  {0,1,9,58,61},
  {0,5,15,22,41},
  {0,2,13,50,56},
  {0,4,18,34,46}}

theorem uniform : base.IsUniform 5 := by
  intro B hB
  simp only [base, Finset.mem_insert, Finset.mem_singleton] at hB
  rcases hB with rfl | rfl | rfl | rfl <;> decide

theorem counts : ∀ d : ZMod 81, d ≠ 0 → (smallWitnesses base d).card = 1 := by
  intro d hd
  fin_cases d <;> first | exact False.elim (hd rfl) | decide

def supplied : Supplied (ZMod 81) 5 := Supplied.of_small_counts base uniform counts

theorem developed_isBlockDesign : supplied.developed.IsBlockDesign 2 5 :=
  supplied.developed_isBlockDesign

noncomputable def pointEquiv : ZMod 81 ≃ Fin 81 :=
  Fintype.equivFinOfCardEq (by simp)

noncomputable def blocks : Finset (Finset (Fin 81)) :=
  DesignTransport.relabel pointEquiv supplied.developed

theorem isBlockDesign : blocks.IsBlockDesign 2 5 :=
  DesignTransport.isBlockDesign_relabel pointEquiv _ 2 5 developed_isBlockDesign

theorem exists_design : ∃ B : Finset (Finset (Fin 81)), B.IsBlockDesign 2 5 :=
  ⟨blocks, isBlockDesign⟩

end Erdos643Design.CyclicSeed81
