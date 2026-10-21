import Openmath.Erdos643Design.FieldFamilyCertificate

/-! Explicit additive-coordinate certificate for a design on 145 points.
The coordinate table is original output of the construction in Smith, theorem 24.
All finite claims below are checked by Lean's kernel using `decide`. -/
set_option autoImplicit false

namespace Erdos643Design.FieldFamily29
open Finset Erdos643Design.RelativeDifferenceFamily

abbrev A := ZMod 29

def base : Finset (Finset (ZMod 5 × A)) := {
  {(0, 0), (1, 1), (1, 28), (4, 12), (4, 17)},
  {(0, 0), (1, 2), (1, 27), (4, 24), (4, 5)},
  {(0, 0), (1, 4), (1, 25), (4, 19), (4, 10)},
  {(0, 0), (1, 8), (1, 21), (4, 9), (4, 20)},
  {(0, 0), (1, 16), (1, 13), (4, 18), (4, 11)},
  {(0, 0), (1, 3), (1, 26), (4, 7), (4, 22)},
  {(0, 0), (1, 6), (1, 23), (4, 14), (4, 15)}}

def blocks : List (List (ZMod 5 × A)) := [
  [(0, 0), (1, 1), (1, 28), (4, 12), (4, 17)],
  [(0, 0), (1, 2), (1, 27), (4, 24), (4, 5)],
  [(0, 0), (1, 4), (1, 25), (4, 19), (4, 10)],
  [(0, 0), (1, 8), (1, 21), (4, 9), (4, 20)],
  [(0, 0), (1, 16), (1, 13), (4, 18), (4, 11)],
  [(0, 0), (1, 3), (1, 26), (4, 7), (4, 22)],
  [(0, 0), (1, 6), (1, 23), (4, 14), (4, 15)]]

theorem base_eq : FieldFamilyCertificate.baseFromLists blocks = base := by decide

theorem uniform : base.IsUniform 5 := by
  intro B hB
  simp only [base, mem_insert, mem_singleton] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem projection_card : ∀ B ∈ base, (B.image Prod.snd).card = B.card := by
  intro B hB
  simp only [base, mem_insert, mem_singleton] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem transverse : ∀ B ∈ base, ∀ x ∈ B, ∀ y ∈ B, x.2 = y.2 → x = y :=
  FieldFamilyCertificate.transverse_of_projection_card base projection_card

def claimedDifferences : List (ZMod 5 × A) := [
  (4, 28), (4, 1), (1, 17), (1, 12), (1, 1),
  (0, 2), (2, 18), (2, 13), (1, 28), (0, 27),
  (2, 16), (2, 11), (4, 12), (3, 11), (3, 13),
  (0, 24), (4, 17), (3, 16), (3, 18), (0, 5),
  (4, 27), (4, 2), (1, 5), (1, 24), (1, 2),
  (0, 4), (2, 7), (2, 26), (1, 27), (0, 25),
  (2, 3), (2, 22), (4, 24), (3, 22), (3, 26),
  (0, 19), (4, 5), (3, 3), (3, 7), (0, 10),
  (4, 25), (4, 4), (1, 10), (1, 19), (1, 4),
  (0, 8), (2, 14), (2, 23), (1, 25), (0, 21),
  (2, 6), (2, 15), (4, 19), (3, 15), (3, 23),
  (0, 9), (4, 10), (3, 6), (3, 14), (0, 20),
  (4, 21), (4, 8), (1, 20), (1, 9), (1, 8),
  (0, 16), (2, 28), (2, 17), (1, 21), (0, 13),
  (2, 12), (2, 1), (4, 9), (3, 1), (3, 17),
  (0, 18), (4, 20), (3, 12), (3, 28), (0, 11),
  (4, 13), (4, 16), (1, 11), (1, 18), (1, 16),
  (0, 3), (2, 27), (2, 5), (1, 13), (0, 26),
  (2, 24), (2, 2), (4, 18), (3, 2), (3, 5),
  (0, 7), (4, 11), (3, 24), (3, 27), (0, 22),
  (4, 26), (4, 3), (1, 22), (1, 7), (1, 3),
  (0, 6), (2, 25), (2, 10), (1, 26), (0, 23),
  (2, 19), (2, 4), (4, 7), (3, 4), (3, 10),
  (0, 14), (4, 22), (3, 19), (3, 25), (0, 15),
  (4, 23), (4, 6), (1, 15), (1, 14), (1, 6),
  (0, 12), (2, 21), (2, 20), (1, 23), (0, 17),
  (2, 9), (2, 8), (4, 14), (3, 8), (3, 20),
  (0, 28), (4, 15), (3, 9), (3, 21), (0, 1)]

theorem difference_eq : (FieldFamilyCertificate.witnessList blocks).map difference =
    claimedDifferences := by decide

theorem difference_nodup : claimedDifferences.Nodup := by decide

theorem witness_count : (FieldFamilyCertificate.witnessList blocks).length =
    5 * (Fintype.card A - 1) := by decide

def supplied : Supplied A := FieldFamilyCertificate.suppliedOfLists blocks
  (by rw [base_eq]; exact uniform) (by rw [base_eq]; exact transverse)
  claimedDifferences difference_eq difference_nodup witness_count

theorem exists_design : ∃ B : Finset (Finset (Fin 145)), B.IsBlockDesign 2 5 := by
  obtain ⟨B,hB⟩ := supplied.exists_design_fin
  let e : Fin (5 * Fintype.card A) ≃ Fin 145 := finCongr (by decide)
  exact ⟨DesignTransport.relabel e B,
    DesignTransport.isBlockDesign_relabel e B 2 5 hB⟩

end Erdos643Design.FieldFamily29
