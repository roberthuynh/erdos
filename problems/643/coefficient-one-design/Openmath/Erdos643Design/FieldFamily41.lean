import Openmath.Erdos643Design.FieldFamilyCertificate

/-! Explicit additive-coordinate certificate for a design on 205 points.
The coordinate table is original output of the construction in Smith, theorem 24.
All finite claims below are checked by Lean's kernel using `decide`. -/
set_option autoImplicit false

namespace Erdos643Design.FieldFamily41
open Finset Erdos643Design.RelativeDifferenceFamily

abbrev A := ZMod 41

def base : Finset (Finset (ZMod 5 × A)) := {
  {(0, 0), (1, 1), (1, 40), (4, 32), (4, 9)},
  {(0, 0), (1, 6), (1, 35), (4, 28), (4, 13)},
  {(0, 0), (1, 36), (1, 5), (4, 4), (4, 37)},
  {(0, 0), (1, 11), (1, 30), (4, 24), (4, 17)},
  {(0, 0), (1, 25), (1, 16), (4, 21), (4, 20)},
  {(0, 0), (1, 27), (1, 14), (4, 3), (4, 38)},
  {(0, 0), (1, 39), (1, 2), (4, 18), (4, 23)},
  {(0, 0), (1, 29), (1, 12), (4, 26), (4, 15)},
  {(0, 0), (1, 10), (1, 31), (4, 33), (4, 8)},
  {(0, 0), (1, 19), (1, 22), (4, 34), (4, 7)}}

def blocks : List (List (ZMod 5 × A)) := [
  [(0, 0), (1, 1), (1, 40), (4, 32), (4, 9)],
  [(0, 0), (1, 6), (1, 35), (4, 28), (4, 13)],
  [(0, 0), (1, 36), (1, 5), (4, 4), (4, 37)],
  [(0, 0), (1, 11), (1, 30), (4, 24), (4, 17)],
  [(0, 0), (1, 25), (1, 16), (4, 21), (4, 20)],
  [(0, 0), (1, 27), (1, 14), (4, 3), (4, 38)],
  [(0, 0), (1, 39), (1, 2), (4, 18), (4, 23)],
  [(0, 0), (1, 29), (1, 12), (4, 26), (4, 15)],
  [(0, 0), (1, 10), (1, 31), (4, 33), (4, 8)],
  [(0, 0), (1, 19), (1, 22), (4, 34), (4, 7)]]

theorem base_eq : FieldFamilyCertificate.baseFromLists blocks = base := by decide

theorem uniform : base.IsUniform 5 := by
  intro B hB
  simp only [base, mem_insert, mem_singleton] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem projection_card : ∀ B ∈ base, (B.image Prod.snd).card = B.card := by
  intro B hB
  simp only [base, mem_insert, mem_singleton] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem transverse : ∀ B ∈ base, ∀ x ∈ B, ∀ y ∈ B, x.2 = y.2 → x = y :=
  FieldFamilyCertificate.transverse_of_projection_card base projection_card

def claimedDifferences : List (ZMod 5 × A) := [
  (4, 40), (4, 1), (1, 9), (1, 32), (1, 1),
  (0, 2), (2, 10), (2, 33), (1, 40), (0, 39),
  (2, 8), (2, 31), (4, 32), (3, 31), (3, 33),
  (0, 23), (4, 9), (3, 8), (3, 10), (0, 18),
  (4, 35), (4, 6), (1, 13), (1, 28), (1, 6),
  (0, 12), (2, 19), (2, 34), (1, 35), (0, 29),
  (2, 7), (2, 22), (4, 28), (3, 22), (3, 34),
  (0, 15), (4, 13), (3, 7), (3, 19), (0, 26),
  (4, 5), (4, 36), (1, 37), (1, 4), (1, 36),
  (0, 31), (2, 32), (2, 40), (1, 5), (0, 10),
  (2, 1), (2, 9), (4, 4), (3, 9), (3, 40),
  (0, 8), (4, 37), (3, 1), (3, 32), (0, 33),
  (4, 30), (4, 11), (1, 17), (1, 24), (1, 11),
  (0, 22), (2, 28), (2, 35), (1, 30), (0, 19),
  (2, 6), (2, 13), (4, 24), (3, 13), (3, 35),
  (0, 7), (4, 17), (3, 6), (3, 28), (0, 34),
  (4, 16), (4, 25), (1, 20), (1, 21), (1, 25),
  (0, 9), (2, 4), (2, 5), (1, 16), (0, 32),
  (2, 36), (2, 37), (4, 21), (3, 37), (3, 5),
  (0, 1), (4, 20), (3, 36), (3, 4), (0, 40),
  (4, 14), (4, 27), (1, 38), (1, 3), (1, 27),
  (0, 13), (2, 24), (2, 30), (1, 14), (0, 28),
  (2, 11), (2, 17), (4, 3), (3, 17), (3, 30),
  (0, 6), (4, 38), (3, 11), (3, 24), (0, 35),
  (4, 2), (4, 39), (1, 23), (1, 18), (1, 39),
  (0, 37), (2, 21), (2, 16), (1, 2), (0, 4),
  (2, 25), (2, 20), (4, 18), (3, 20), (3, 16),
  (0, 36), (4, 23), (3, 25), (3, 21), (0, 5),
  (4, 12), (4, 29), (1, 15), (1, 26), (1, 29),
  (0, 17), (2, 3), (2, 14), (1, 12), (0, 24),
  (2, 27), (2, 38), (4, 26), (3, 38), (3, 14),
  (0, 11), (4, 15), (3, 27), (3, 3), (0, 30),
  (4, 31), (4, 10), (1, 8), (1, 33), (1, 10),
  (0, 20), (2, 18), (2, 2), (1, 31), (0, 21),
  (2, 39), (2, 23), (4, 33), (3, 23), (3, 2),
  (0, 25), (4, 8), (3, 39), (3, 18), (0, 16),
  (4, 22), (4, 19), (1, 7), (1, 34), (1, 19),
  (0, 38), (2, 26), (2, 12), (1, 22), (0, 3),
  (2, 29), (2, 15), (4, 34), (3, 15), (3, 12),
  (0, 27), (4, 7), (3, 29), (3, 26), (0, 14)]

theorem difference_eq : (FieldFamilyCertificate.witnessList blocks).map difference =
    claimedDifferences := by decide

theorem difference_nodup : claimedDifferences.Nodup := by decide

theorem witness_count : (FieldFamilyCertificate.witnessList blocks).length =
    5 * (Fintype.card A - 1) := by decide

def supplied : Supplied A := FieldFamilyCertificate.suppliedOfLists blocks
  (by rw [base_eq]; exact uniform) (by rw [base_eq]; exact transverse)
  claimedDifferences difference_eq difference_nodup witness_count

theorem exists_design : ∃ B : Finset (Finset (Fin 205)), B.IsBlockDesign 2 5 := by
  obtain ⟨B,hB⟩ := supplied.exists_design_fin
  let e : Fin (5 * Fintype.card A) ≃ Fin 205 := finCongr (by decide)
  exact ⟨DesignTransport.relabel e B,
    DesignTransport.isBlockDesign_relabel e B 2 5 hB⟩

end Erdos643Design.FieldFamily41
