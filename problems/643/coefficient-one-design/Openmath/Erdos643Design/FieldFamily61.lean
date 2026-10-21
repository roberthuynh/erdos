import Openmath.Erdos643Design.FieldFamilyCertificate

/-! Explicit additive-coordinate certificate for a design on 305 points.
The coordinate table is original output of the construction in Smith, theorem 24.
All finite claims below are checked by Lean's kernel using `decide`. -/
set_option autoImplicit false

namespace Erdos643Design.FieldFamily61
open Finset Erdos643Design.RelativeDifferenceFamily

abbrev A := ZMod 61

def base : Finset (Finset (ZMod 5 × A)) := {
  {(0, 0), (1, 1), (1, 60), (4, 11), (4, 50)},
  {(0, 0), (1, 2), (1, 59), (4, 22), (4, 39)},
  {(0, 0), (1, 4), (1, 57), (4, 44), (4, 17)},
  {(0, 0), (1, 8), (1, 53), (4, 27), (4, 34)},
  {(0, 0), (1, 16), (1, 45), (4, 54), (4, 7)},
  {(0, 0), (1, 32), (1, 29), (4, 47), (4, 14)},
  {(0, 0), (1, 3), (1, 58), (4, 33), (4, 28)},
  {(0, 0), (1, 6), (1, 55), (4, 5), (4, 56)},
  {(0, 0), (1, 12), (1, 49), (4, 10), (4, 51)},
  {(0, 0), (1, 24), (1, 37), (4, 20), (4, 41)},
  {(0, 0), (1, 48), (1, 13), (4, 40), (4, 21)},
  {(0, 0), (1, 35), (1, 26), (4, 19), (4, 42)},
  {(0, 0), (1, 9), (1, 52), (4, 38), (4, 23)},
  {(0, 0), (1, 18), (1, 43), (4, 15), (4, 46)},
  {(0, 0), (1, 36), (1, 25), (4, 30), (4, 31)}}

def blocks : List (List (ZMod 5 × A)) := [
  [(0, 0), (1, 1), (1, 60), (4, 11), (4, 50)],
  [(0, 0), (1, 2), (1, 59), (4, 22), (4, 39)],
  [(0, 0), (1, 4), (1, 57), (4, 44), (4, 17)],
  [(0, 0), (1, 8), (1, 53), (4, 27), (4, 34)],
  [(0, 0), (1, 16), (1, 45), (4, 54), (4, 7)],
  [(0, 0), (1, 32), (1, 29), (4, 47), (4, 14)],
  [(0, 0), (1, 3), (1, 58), (4, 33), (4, 28)],
  [(0, 0), (1, 6), (1, 55), (4, 5), (4, 56)],
  [(0, 0), (1, 12), (1, 49), (4, 10), (4, 51)],
  [(0, 0), (1, 24), (1, 37), (4, 20), (4, 41)],
  [(0, 0), (1, 48), (1, 13), (4, 40), (4, 21)],
  [(0, 0), (1, 35), (1, 26), (4, 19), (4, 42)],
  [(0, 0), (1, 9), (1, 52), (4, 38), (4, 23)],
  [(0, 0), (1, 18), (1, 43), (4, 15), (4, 46)],
  [(0, 0), (1, 36), (1, 25), (4, 30), (4, 31)]]

theorem base_eq : FieldFamilyCertificate.baseFromLists blocks = base := by decide

theorem uniform : base.IsUniform 5 := by
  intro B hB
  simp only [base, mem_insert, mem_singleton] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem projection_card : ∀ B ∈ base, (B.image Prod.snd).card = B.card := by
  intro B hB
  simp only [base, mem_insert, mem_singleton] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem transverse : ∀ B ∈ base, ∀ x ∈ B, ∀ y ∈ B, x.2 = y.2 → x = y :=
  FieldFamilyCertificate.transverse_of_projection_card base projection_card

def claimedDifferences : List (ZMod 5 × A) := [
  (4, 60), (4, 1), (1, 50), (1, 11), (1, 1),
  (0, 2), (2, 51), (2, 12), (1, 60), (0, 59),
  (2, 49), (2, 10), (4, 11), (3, 10), (3, 12),
  (0, 22), (4, 50), (3, 49), (3, 51), (0, 39),
  (4, 59), (4, 2), (1, 39), (1, 22), (1, 2),
  (0, 4), (2, 41), (2, 24), (1, 59), (0, 57),
  (2, 37), (2, 20), (4, 22), (3, 20), (3, 24),
  (0, 44), (4, 39), (3, 37), (3, 41), (0, 17),
  (4, 57), (4, 4), (1, 17), (1, 44), (1, 4),
  (0, 8), (2, 21), (2, 48), (1, 57), (0, 53),
  (2, 13), (2, 40), (4, 44), (3, 40), (3, 48),
  (0, 27), (4, 17), (3, 13), (3, 21), (0, 34),
  (4, 53), (4, 8), (1, 34), (1, 27), (1, 8),
  (0, 16), (2, 42), (2, 35), (1, 53), (0, 45),
  (2, 26), (2, 19), (4, 27), (3, 19), (3, 35),
  (0, 54), (4, 34), (3, 26), (3, 42), (0, 7),
  (4, 45), (4, 16), (1, 7), (1, 54), (1, 16),
  (0, 32), (2, 23), (2, 9), (1, 45), (0, 29),
  (2, 52), (2, 38), (4, 54), (3, 38), (3, 9),
  (0, 47), (4, 7), (3, 52), (3, 23), (0, 14),
  (4, 29), (4, 32), (1, 14), (1, 47), (1, 32),
  (0, 3), (2, 46), (2, 18), (1, 29), (0, 58),
  (2, 43), (2, 15), (4, 47), (3, 15), (3, 18),
  (0, 33), (4, 14), (3, 43), (3, 46), (0, 28),
  (4, 58), (4, 3), (1, 28), (1, 33), (1, 3),
  (0, 6), (2, 31), (2, 36), (1, 58), (0, 55),
  (2, 25), (2, 30), (4, 33), (3, 30), (3, 36),
  (0, 5), (4, 28), (3, 25), (3, 31), (0, 56),
  (4, 55), (4, 6), (1, 56), (1, 5), (1, 6),
  (0, 12), (2, 1), (2, 11), (1, 55), (0, 49),
  (2, 50), (2, 60), (4, 5), (3, 60), (3, 11),
  (0, 10), (4, 56), (3, 50), (3, 1), (0, 51),
  (4, 49), (4, 12), (1, 51), (1, 10), (1, 12),
  (0, 24), (2, 2), (2, 22), (1, 49), (0, 37),
  (2, 39), (2, 59), (4, 10), (3, 59), (3, 22),
  (0, 20), (4, 51), (3, 39), (3, 2), (0, 41),
  (4, 37), (4, 24), (1, 41), (1, 20), (1, 24),
  (0, 48), (2, 4), (2, 44), (1, 37), (0, 13),
  (2, 17), (2, 57), (4, 20), (3, 57), (3, 44),
  (0, 40), (4, 41), (3, 17), (3, 4), (0, 21),
  (4, 13), (4, 48), (1, 21), (1, 40), (1, 48),
  (0, 35), (2, 8), (2, 27), (1, 13), (0, 26),
  (2, 34), (2, 53), (4, 40), (3, 53), (3, 27),
  (0, 19), (4, 21), (3, 34), (3, 8), (0, 42),
  (4, 26), (4, 35), (1, 42), (1, 19), (1, 35),
  (0, 9), (2, 16), (2, 54), (1, 26), (0, 52),
  (2, 7), (2, 45), (4, 19), (3, 45), (3, 54),
  (0, 38), (4, 42), (3, 7), (3, 16), (0, 23),
  (4, 52), (4, 9), (1, 23), (1, 38), (1, 9),
  (0, 18), (2, 32), (2, 47), (1, 52), (0, 43),
  (2, 14), (2, 29), (4, 38), (3, 29), (3, 47),
  (0, 15), (4, 23), (3, 14), (3, 32), (0, 46),
  (4, 43), (4, 18), (1, 46), (1, 15), (1, 18),
  (0, 36), (2, 3), (2, 33), (1, 43), (0, 25),
  (2, 28), (2, 58), (4, 15), (3, 58), (3, 33),
  (0, 30), (4, 46), (3, 28), (3, 3), (0, 31),
  (4, 25), (4, 36), (1, 31), (1, 30), (1, 36),
  (0, 11), (2, 6), (2, 5), (1, 25), (0, 50),
  (2, 56), (2, 55), (4, 30), (3, 55), (3, 5),
  (0, 60), (4, 31), (3, 56), (3, 6), (0, 1)]

theorem difference_eq : (FieldFamilyCertificate.witnessList blocks).map difference =
    claimedDifferences := by decide

theorem difference_nodup : claimedDifferences.Nodup := by decide

theorem witness_count : (FieldFamilyCertificate.witnessList blocks).length =
    5 * (Fintype.card A - 1) := by decide

def supplied : Supplied A := FieldFamilyCertificate.suppliedOfLists blocks
  (by rw [base_eq]; exact uniform) (by rw [base_eq]; exact transverse)
  claimedDifferences difference_eq difference_nodup witness_count

theorem exists_design : ∃ B : Finset (Finset (Fin 305)), B.IsBlockDesign 2 5 := by
  obtain ⟨B,hB⟩ := supplied.exists_design_fin
  let e : Fin (5 * Fintype.card A) ≃ Fin 305 := finCongr (by decide)
  exact ⟨DesignTransport.relabel e B,
    DesignTransport.isBlockDesign_relabel e B 2 5 hB⟩

end Erdos643Design.FieldFamily61
