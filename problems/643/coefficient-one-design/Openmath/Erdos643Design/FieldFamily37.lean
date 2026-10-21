import Openmath.Erdos643Design.FieldFamilyCertificate

/-! Explicit additive-coordinate certificate for a design on 185 points.
The coordinate table is original output of the construction in Smith, theorem 24.
All finite claims below are checked by Lean's kernel using `decide`. -/
set_option autoImplicit false

namespace Erdos643Design.FieldFamily37
open Finset Erdos643Design.RelativeDifferenceFamily

abbrev A := ZMod 37

def base : Finset (Finset (ZMod 5 × A)) := {
  {(0, 0), (1, 1), (1, 36), (4, 31), (4, 6)},
  {(0, 0), (1, 2), (1, 35), (4, 25), (4, 12)},
  {(0, 0), (1, 4), (1, 33), (4, 13), (4, 24)},
  {(0, 0), (1, 8), (1, 29), (4, 26), (4, 11)},
  {(0, 0), (1, 16), (1, 21), (4, 15), (4, 22)},
  {(0, 0), (1, 32), (1, 5), (4, 30), (4, 7)},
  {(0, 0), (1, 27), (1, 10), (4, 23), (4, 14)},
  {(0, 0), (1, 17), (1, 20), (4, 9), (4, 28)},
  {(0, 0), (1, 34), (1, 3), (4, 18), (4, 19)}}

def blocks : List (List (ZMod 5 × A)) := [
  [(0, 0), (1, 1), (1, 36), (4, 31), (4, 6)],
  [(0, 0), (1, 2), (1, 35), (4, 25), (4, 12)],
  [(0, 0), (1, 4), (1, 33), (4, 13), (4, 24)],
  [(0, 0), (1, 8), (1, 29), (4, 26), (4, 11)],
  [(0, 0), (1, 16), (1, 21), (4, 15), (4, 22)],
  [(0, 0), (1, 32), (1, 5), (4, 30), (4, 7)],
  [(0, 0), (1, 27), (1, 10), (4, 23), (4, 14)],
  [(0, 0), (1, 17), (1, 20), (4, 9), (4, 28)],
  [(0, 0), (1, 34), (1, 3), (4, 18), (4, 19)]]

theorem base_eq : FieldFamilyCertificate.baseFromLists blocks = base := by decide

theorem uniform : base.IsUniform 5 := by
  intro B hB
  simp only [base, mem_insert, mem_singleton] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem projection_card : ∀ B ∈ base, (B.image Prod.snd).card = B.card := by
  intro B hB
  simp only [base, mem_insert, mem_singleton] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem transverse : ∀ B ∈ base, ∀ x ∈ B, ∀ y ∈ B, x.2 = y.2 → x = y :=
  FieldFamilyCertificate.transverse_of_projection_card base projection_card

def claimedDifferences : List (ZMod 5 × A) := [
  (4, 36), (4, 1), (1, 6), (1, 31), (1, 1),
  (0, 2), (2, 7), (2, 32), (1, 36), (0, 35),
  (2, 5), (2, 30), (4, 31), (3, 30), (3, 32),
  (0, 25), (4, 6), (3, 5), (3, 7), (0, 12),
  (4, 35), (4, 2), (1, 12), (1, 25), (1, 2),
  (0, 4), (2, 14), (2, 27), (1, 35), (0, 33),
  (2, 10), (2, 23), (4, 25), (3, 23), (3, 27),
  (0, 13), (4, 12), (3, 10), (3, 14), (0, 24),
  (4, 33), (4, 4), (1, 24), (1, 13), (1, 4),
  (0, 8), (2, 28), (2, 17), (1, 33), (0, 29),
  (2, 20), (2, 9), (4, 13), (3, 9), (3, 17),
  (0, 26), (4, 24), (3, 20), (3, 28), (0, 11),
  (4, 29), (4, 8), (1, 11), (1, 26), (1, 8),
  (0, 16), (2, 19), (2, 34), (1, 29), (0, 21),
  (2, 3), (2, 18), (4, 26), (3, 18), (3, 34),
  (0, 15), (4, 11), (3, 3), (3, 19), (0, 22),
  (4, 21), (4, 16), (1, 22), (1, 15), (1, 16),
  (0, 32), (2, 1), (2, 31), (1, 21), (0, 5),
  (2, 6), (2, 36), (4, 15), (3, 36), (3, 31),
  (0, 30), (4, 22), (3, 6), (3, 1), (0, 7),
  (4, 5), (4, 32), (1, 7), (1, 30), (1, 32),
  (0, 27), (2, 2), (2, 25), (1, 5), (0, 10),
  (2, 12), (2, 35), (4, 30), (3, 35), (3, 25),
  (0, 23), (4, 7), (3, 12), (3, 2), (0, 14),
  (4, 10), (4, 27), (1, 14), (1, 23), (1, 27),
  (0, 17), (2, 4), (2, 13), (1, 10), (0, 20),
  (2, 24), (2, 33), (4, 23), (3, 33), (3, 13),
  (0, 9), (4, 14), (3, 24), (3, 4), (0, 28),
  (4, 20), (4, 17), (1, 28), (1, 9), (1, 17),
  (0, 34), (2, 8), (2, 26), (1, 20), (0, 3),
  (2, 11), (2, 29), (4, 9), (3, 29), (3, 26),
  (0, 18), (4, 28), (3, 11), (3, 8), (0, 19),
  (4, 3), (4, 34), (1, 19), (1, 18), (1, 34),
  (0, 31), (2, 16), (2, 15), (1, 3), (0, 6),
  (2, 22), (2, 21), (4, 18), (3, 21), (3, 15),
  (0, 36), (4, 19), (3, 22), (3, 16), (0, 1)]

theorem difference_eq : (FieldFamilyCertificate.witnessList blocks).map difference =
    claimedDifferences := by decide

theorem difference_nodup : claimedDifferences.Nodup := by decide

theorem witness_count : (FieldFamilyCertificate.witnessList blocks).length =
    5 * (Fintype.card A - 1) := by decide

def supplied : Supplied A := FieldFamilyCertificate.suppliedOfLists blocks
  (by rw [base_eq]; exact uniform) (by rw [base_eq]; exact transverse)
  claimedDifferences difference_eq difference_nodup witness_count

theorem exists_design : ∃ B : Finset (Finset (Fin 185)), B.IsBlockDesign 2 5 := by
  obtain ⟨B,hB⟩ := supplied.exists_design_fin
  let e : Fin (5 * Fintype.card A) ≃ Fin 185 := finCongr (by decide)
  exact ⟨DesignTransport.relabel e B,
    DesignTransport.isBlockDesign_relabel e B 2 5 hB⟩

end Erdos643Design.FieldFamily37
