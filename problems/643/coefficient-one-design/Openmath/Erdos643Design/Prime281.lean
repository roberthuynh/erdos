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

private theorem smallWitnesses_card_sum (d : ZMod 281) :
    (smallWitnesses base d).card =
      ∑ B ∈ base, ((B ×ˢ B).filter (fun xy => xy.1 - xy.2 = d)).card := by
  rw [smallWitnesses, Finset.filter_biUnion]
  have hdis : (base : Set (Finset (ZMod 281))).PairwiseDisjoint
      (fun B => ((B ×ˢ B).image (fun xy => (B, xy))).filter
        (fun w => w.2.1 - w.2.2 = d)) := by
    intro B hB C hC hBC
    apply Finset.disjoint_left.mpr
    intro w hwB hwC
    obtain ⟨xy, _, hxy⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hwB).1
    obtain ⟨uv, _, huv⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hwC).1
    exact hBC ((congrArg Prod.fst hxy).trans (congrArg Prod.fst huv).symm)
  rw [Finset.card_biUnion hdis]
  apply Finset.sum_congr rfl
  intro B hB
  rw [Finset.filter_image]
  apply Finset.card_image_of_injective
  intro x y hxy
  exact (Prod.mk.inj hxy).2

theorem counts : ∀ d : ZMod 281, d ≠ 0 → (smallWitnesses base d).card = 1 := by
  intro d hd
  rw [smallWitnesses_card_sum]
  fin_cases d <;> first | exact False.elim (hd rfl) | decide

def supplied : Supplied (ZMod 281) 5 := Supplied.of_small_counts base uniform counts

theorem design : supplied.developed.IsBlockDesign 2 5 := supplied.developed_isBlockDesign
end Erdos643Design.PrimeDifference281
