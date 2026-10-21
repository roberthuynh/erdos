import Openmath.Erdos643Design.DifferenceFamilyCertificate
import Openmath.Erdos643Design.DesignTransport
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.EquivFin

/-! An independently searched finite cyclic seed, certified by exact directed counts. -/
set_option autoImplicit false

namespace Erdos643Design.CyclicSeed141
open Erdos643Design.DifferenceFamily

def base : Finset (Finset (ZMod 141)) := {
  {0,73,86,89,130},
  {0,72,82,102,120},
  {0,27,76,88,90},
  {0,9,43,117,124},
  {0,8,40,45,87},
  {0,35,112,118,140},
  {0,4,19,50,75}}

theorem uniform : base.IsUniform 5 := by
  intro B hB
  simp only [base, Finset.mem_insert, Finset.mem_singleton] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem counts : ∀ d : ZMod 141, d ≠ 0 → (smallWitnesses base d).card = 1 := by
  intro d hd
  fin_cases d <;> first | exact False.elim (hd rfl) | decide

def supplied : Supplied (ZMod 141) 5 := Supplied.of_small_counts base uniform counts

theorem developed_isBlockDesign : supplied.developed.IsBlockDesign 2 5 :=
  supplied.developed_isBlockDesign

noncomputable def pointEquiv : ZMod 141 ≃ Fin 141 :=
  Fintype.equivFinOfCardEq (by simp)

noncomputable def blocks : Finset (Finset (Fin 141)) :=
  DesignTransport.relabel pointEquiv supplied.developed

theorem isBlockDesign : blocks.IsBlockDesign 2 5 :=
  DesignTransport.isBlockDesign_relabel pointEquiv _ 2 5 developed_isBlockDesign

theorem exists_design : ∃ B : Finset (Finset (Fin 141)), B.IsBlockDesign 2 5 :=
  ⟨blocks, isBlockDesign⟩

end Erdos643Design.CyclicSeed141
