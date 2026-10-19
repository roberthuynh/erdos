import Openmath.Erdos643Design.DifferenceFamilyCertificate
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
namespace Erdos643Design.PrimeDifference61
open Erdos643Design.DifferenceFamily

def base : Finset (Finset (ZMod 61)) := {
  {5,39,45,46,48},
  {1,9,20,34,58},
  {4,14,19,36,49}}

theorem uniform : base.IsUniform 5 := by
  intro B hB
  simp only [base, Finset.mem_insert, Finset.mem_singleton] at hB
  rcases hB with rfl | rfl | rfl <;> decide

theorem counts : ∀ d : ZMod 61, d ≠ 0 → (smallWitnesses base d).card = 1 := by
  intro d hd
  fin_cases d <;> first | exact False.elim (hd rfl) | decide

def supplied : Supplied (ZMod 61) 5 := Supplied.of_small_counts base uniform counts

theorem design : supplied.developed.IsBlockDesign 2 5 := supplied.developed_isBlockDesign
end Erdos643Design.PrimeDifference61
