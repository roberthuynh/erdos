import Openmath.Erdos643Design.DifferenceFamilyCertificate
import Openmath.Erdos643Design.DesignTransport
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.EquivFin

/-! An independently searched finite cyclic seed, certified by exact directed counts. -/
set_option autoImplicit false

namespace Erdos643Design.CyclicSeed161
open Erdos643Design.DifferenceFamily

def base : Finset (Finset (ZMod 161)) := {
  {0,22,88,105,152},
  {0,21,49,54,141},
  {0,62,81,158,160},
  {0,7,51,55,122},
  {0,11,23,38,147},
  {0,13,43,72,129},
  {0,8,26,61,119},
  {0,6,16,40,76}}

theorem uniform : base.IsUniform 5 := by
  intro B hB
  simp only [base, Finset.mem_insert, Finset.mem_singleton] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem counts : ∀ d : ZMod 161, d ≠ 0 → (smallWitnesses base d).card = 1 := by
  intro d hd
  fin_cases d <;> first | exact False.elim (hd rfl) | decide

def supplied : Supplied (ZMod 161) 5 := Supplied.of_small_counts base uniform counts

theorem developed_isBlockDesign : supplied.developed.IsBlockDesign 2 5 :=
  supplied.developed_isBlockDesign

noncomputable def pointEquiv : ZMod 161 ≃ Fin 161 :=
  Fintype.equivFinOfCardEq (by simp)

noncomputable def blocks : Finset (Finset (Fin 161)) :=
  DesignTransport.relabel pointEquiv supplied.developed

theorem isBlockDesign : blocks.IsBlockDesign 2 5 :=
  DesignTransport.isBlockDesign_relabel pointEquiv _ 2 5 developed_isBlockDesign

theorem exists_design : ∃ B : Finset (Finset (Fin 161)), B.IsBlockDesign 2 5 :=
  ⟨blocks, isBlockDesign⟩

end Erdos643Design.CyclicSeed161
