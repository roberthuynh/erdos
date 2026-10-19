import Openmath.Erdos643Design.FieldFamilyCertificate

/-! Explicit additive-coordinate certificate for a design on 45 points.
The coordinate table is original output of the construction in Smith, theorem 24.
All finite claims below are checked by Lean's kernel using `decide`. -/
set_option autoImplicit false

namespace Erdos643Design.FieldFamily9
open Finset Erdos643Design.RelativeDifferenceFamily

abbrev A := (Fin 2 → ZMod 3)

def base : Finset (Finset (ZMod 5 × A)) := {
  {(0, ![0, 0]), (1, ![1, 0]), (1, ![2, 0]), (4, ![0, 2]), (4, ![0, 1])},
  {(0, ![0, 0]), (1, ![1, 1]), (1, ![2, 2]), (4, ![1, 2]), (4, ![2, 1])}}

def blocks : List (List (ZMod 5 × A)) := [
  [(0, ![0, 0]), (1, ![1, 0]), (1, ![2, 0]), (4, ![0, 2]), (4, ![0, 1])],
  [(0, ![0, 0]), (1, ![1, 1]), (1, ![2, 2]), (4, ![1, 2]), (4, ![2, 1])]]

theorem base_eq : FieldFamilyCertificate.baseFromLists blocks = base := by decide

theorem uniform : base.IsUniform 5 := by
  intro B hB
  simp only [base, mem_insert, mem_singleton] at hB
  rcases hB with rfl | rfl
  all_goals decide

theorem projection_card : ∀ B ∈ base, (B.image Prod.snd).card = B.card := by
  intro B hB
  simp only [base, mem_insert, mem_singleton] at hB
  rcases hB with rfl | rfl
  all_goals decide

theorem transverse : ∀ B ∈ base, ∀ x ∈ B, ∀ y ∈ B, x.2 = y.2 → x = y :=
  FieldFamilyCertificate.transverse_of_projection_card base projection_card

def claimedDifferences : List (ZMod 5 × A) := [
  (4, ![2, 0]), (4, ![1, 0]), (1, ![0, 1]), (1, ![0, 2]), (1, ![1, 0]),
  (0, ![2, 0]), (2, ![1, 1]), (2, ![1, 2]), (1, ![2, 0]), (0, ![1, 0]),
  (2, ![2, 1]), (2, ![2, 2]), (4, ![0, 2]), (3, ![2, 2]), (3, ![1, 2]),
  (0, ![0, 1]), (4, ![0, 1]), (3, ![2, 1]), (3, ![1, 1]), (0, ![0, 2]),
  (4, ![2, 2]), (4, ![1, 1]), (1, ![2, 1]), (1, ![1, 2]), (1, ![1, 1]),
  (0, ![2, 2]), (2, ![0, 2]), (2, ![2, 0]), (1, ![2, 2]), (0, ![1, 1]),
  (2, ![1, 0]), (2, ![0, 1]), (4, ![1, 2]), (3, ![0, 1]), (3, ![2, 0]),
  (0, ![2, 1]), (4, ![2, 1]), (3, ![1, 0]), (3, ![0, 2]), (0, ![1, 2])]

theorem difference_eq : (FieldFamilyCertificate.witnessList blocks).map difference =
    claimedDifferences := by decide

theorem difference_nodup : claimedDifferences.Nodup := by decide

theorem witness_count : (FieldFamilyCertificate.witnessList blocks).length =
    5 * (Fintype.card A - 1) := by decide

def supplied : Supplied A := FieldFamilyCertificate.suppliedOfLists blocks
  (by rw [base_eq]; exact uniform) (by rw [base_eq]; exact transverse)
  claimedDifferences difference_eq difference_nodup witness_count

theorem exists_design : ∃ B : Finset (Finset (Fin 45)), B.IsBlockDesign 2 5 := by
  obtain ⟨B,hB⟩ := supplied.exists_design_fin
  let e : Fin (5 * Fintype.card A) ≃ Fin 45 := finCongr (by decide)
  exact ⟨DesignTransport.relabel e B,
    DesignTransport.isBlockDesign_relabel e B 2 5 hB⟩

end Erdos643Design.FieldFamily9
