import Openmath.Erdos643Design.FieldFamilyCertificate

/-! Explicit additive-coordinate certificate for a design on 65 points.
The coordinate table is original output of the construction in Smith, theorem 24.
All finite claims below are checked by Lean's kernel using `decide`. -/
set_option autoImplicit false

namespace Erdos643Design.FieldFamily13
open Finset Erdos643Design.RelativeDifferenceFamily

abbrev A := ZMod 13

def base : Finset (Finset (ZMod 5 × A)) := {
  {(0, 0), (1, 1), (1, 12), (4, 8), (4, 5)},
  {(0, 0), (1, 2), (1, 11), (4, 3), (4, 10)},
  {(0, 0), (1, 4), (1, 9), (4, 6), (4, 7)}}

def blocks : List (List (ZMod 5 × A)) := [
  [(0, 0), (1, 1), (1, 12), (4, 8), (4, 5)],
  [(0, 0), (1, 2), (1, 11), (4, 3), (4, 10)],
  [(0, 0), (1, 4), (1, 9), (4, 6), (4, 7)]]

theorem base_eq : FieldFamilyCertificate.baseFromLists blocks = base := by decide

theorem uniform : base.IsUniform 5 := by
  intro B hB
  simp only [base, mem_insert, mem_singleton] at hB
  rcases hB with rfl | rfl | rfl
  all_goals decide

theorem projection_card : ∀ B ∈ base, (B.image Prod.snd).card = B.card := by
  intro B hB
  simp only [base, mem_insert, mem_singleton] at hB
  rcases hB with rfl | rfl | rfl
  all_goals decide

theorem transverse : ∀ B ∈ base, ∀ x ∈ B, ∀ y ∈ B, x.2 = y.2 → x = y :=
  FieldFamilyCertificate.transverse_of_projection_card base projection_card

def claimedDifferences : List (ZMod 5 × A) := [
  (4, 12), (4, 1), (1, 5), (1, 8), (1, 1),
  (0, 2), (2, 6), (2, 9), (1, 12), (0, 11),
  (2, 4), (2, 7), (4, 8), (3, 7), (3, 9),
  (0, 3), (4, 5), (3, 4), (3, 6), (0, 10),
  (4, 11), (4, 2), (1, 10), (1, 3), (1, 2),
  (0, 4), (2, 12), (2, 5), (1, 11), (0, 9),
  (2, 8), (2, 1), (4, 3), (3, 1), (3, 5),
  (0, 6), (4, 10), (3, 8), (3, 12), (0, 7),
  (4, 9), (4, 4), (1, 7), (1, 6), (1, 4),
  (0, 8), (2, 11), (2, 10), (1, 9), (0, 5),
  (2, 3), (2, 2), (4, 6), (3, 2), (3, 10),
  (0, 12), (4, 7), (3, 3), (3, 11), (0, 1)]

theorem difference_eq : (FieldFamilyCertificate.witnessList blocks).map difference =
    claimedDifferences := by decide

theorem difference_nodup : claimedDifferences.Nodup := by decide

theorem witness_count : (FieldFamilyCertificate.witnessList blocks).length =
    5 * (Fintype.card A - 1) := by decide

def supplied : Supplied A := FieldFamilyCertificate.suppliedOfLists blocks
  (by rw [base_eq]; exact uniform) (by rw [base_eq]; exact transverse)
  claimedDifferences difference_eq difference_nodup witness_count

theorem exists_design : ∃ B : Finset (Finset (Fin 65)), B.IsBlockDesign 2 5 := by
  obtain ⟨B,hB⟩ := supplied.exists_design_fin
  let e : Fin (5 * Fintype.card A) ≃ Fin 65 := finCongr (by decide)
  exact ⟨DesignTransport.relabel e B,
    DesignTransport.isBlockDesign_relabel e B 2 5 hB⟩

end Erdos643Design.FieldFamily13
