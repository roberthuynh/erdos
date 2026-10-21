import Openmath.Erdos643Design.DifferenceFamilyCertificate
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
namespace Erdos643Design.PrimeDifference281
open Erdos643Design.DifferenceFamily

def base : Finset (Finset (ZMod 281)) := {
  {32,70,118,119,223},
  {14,80,136,157,175},
  {9,121,212,248,253},
  {16,35,59,200,252},
  {7,40,68,219,228},
  {8,100,126,158,170},
  {20,34,114,144,250},
  {4,50,63,79,85},
  {10,17,57,72,125},
  {2,25,172,180,183},
  {5,36,149,169,203},
  {1,86,90,153,232},
  {18,143,215,225,242},
  {43,45,116,141,217}}

theorem uniform : base.IsUniform 5 := by
  intro B hB
  simp only [base, Finset.mem_insert, Finset.mem_singleton] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem counts : ∀ d : ZMod 281, d ≠ 0 → (smallWitnesses base d).card = 1 := by
  intro d hd
  fin_cases d <;> first | exact False.elim (hd rfl) | decide

def supplied : Supplied (ZMod 281) 5 := Supplied.of_small_counts base uniform counts

theorem design : supplied.developed.IsBlockDesign 2 5 := supplied.developed_isBlockDesign
end Erdos643Design.PrimeDifference281
