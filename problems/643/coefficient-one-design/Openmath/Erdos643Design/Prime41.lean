import Openmath.Erdos643Design.DifferenceFamilyCertificate
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
namespace Erdos643Design.PrimeDifference41
open Erdos643Design.DifferenceFamily

def base : Finset (Finset (ZMod 41)) := {
  {2,20,32,33,36},
  {1,10,16,18,37}}

theorem uniform : base.IsUniform 5 := by
  intro B hB
  simp only [base, Finset.mem_insert, Finset.mem_singleton] at hB
  rcases hB with rfl | rfl <;> decide

theorem counts : ∀ d : ZMod 41, d ≠ 0 → (smallWitnesses base d).card = 1 := by
  intro d hd
  fin_cases d <;> first | exact False.elim (hd rfl) | decide

def supplied : Supplied (ZMod 41) 5 := Supplied.of_small_counts base uniform counts

theorem design : supplied.developed.IsBlockDesign 2 5 := supplied.developed_isBlockDesign
end Erdos643Design.PrimeDifference41
