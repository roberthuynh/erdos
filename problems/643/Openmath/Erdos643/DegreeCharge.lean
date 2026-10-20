import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! The finite weighted incidence argument used in published PV Lemma 11. -/
namespace Erdos643
namespace DegreeCharge

open Finset

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def leftNeighbors (R : X → Y → Prop) (x : X) : Finset Y := by
  classical
  exact univ.filter (R x)

noncomputable def rightNeighbors (R : X → Y → Prop) (y : Y) : Finset X := by
  classical
  exact univ.filter (fun x => R x y)

/-- If every left vertex is incident and each incident right degree is at most
its left degree, weighting edges by reciprocal right degree gives |X| <= |Y|. -/
theorem card_le_card_of_degree (R : X → Y → Prop)
    (hpos : ∀ x, ∃ y, R x y)
    (hdeg : ∀ x y, R x y → (rightNeighbors R y).card ≤ (leftNeighbors R x).card) :
    Fintype.card X ≤ Fintype.card Y := by
  classical
  let dl : X → ℕ := fun x => (leftNeighbors R x).card
  let dr : Y → ℕ := fun y => (rightNeighbors R y).card
  let w : X → Y → ℝ := fun x y => if R x y then 1 / (dr y : ℝ) else 0
  have hdl : ∀ x, 0 < (dl x : ℝ) := by
    intro x
    obtain ⟨y, hy⟩ := hpos x
    have hn : 0 < (leftNeighbors R x).card := card_pos.mpr ⟨y, by simp [leftNeighbors, hy]⟩
    exact_mod_cast hn
  have hdr : ∀ x y, R x y → 0 < (dr y : ℝ) := by
    intro x y hxy
    have hn : 0 < (rightNeighbors R y).card := card_pos.mpr ⟨x, by simp [rightNeighbors, hxy]⟩
    exact_mod_cast hn
  have hrow : ∀ x, (1 : ℝ) ≤ ∑ y, w x y := by
    intro x
    calc
      (1 : ℝ) = ∑ _y ∈ leftNeighbors R x, 1 / (dl x : ℝ) := by
        simp only [sum_const, nsmul_eq_mul]
        change 1 = (dl x : ℝ) * (1 / (dl x : ℝ))
        rw [mul_one_div, div_self (ne_of_gt (hdl x))]
      _ ≤ ∑ y ∈ leftNeighbors R x, 1 / (dr y : ℝ) := by
        apply sum_le_sum
        intro y hy
        have hxy : R x y := by simpa [leftNeighbors] using hy
        have hd : (dr y : ℝ) ≤ (dl x : ℝ) := by exact_mod_cast hdeg x y hxy
        exact one_div_le_one_div_of_le (hdr x y hxy) hd
      _ = ∑ y, w x y := by simp [w, leftNeighbors, sum_filter]
  have hcol : ∀ y, (∑ x, w x y) ≤ (1 : ℝ) := by
    intro y
    calc
      (∑ x, w x y) = ∑ _x ∈ rightNeighbors R y, 1 / (dr y : ℝ) := by
        simp only [w, rightNeighbors, sum_filter]
      _ = (dr y : ℝ) * (1 / (dr y : ℝ)) := by
        simp only [sum_const, nsmul_eq_mul]
        rfl
      _ ≤ 1 := by
        by_cases hz : dr y = 0
        · simp [hz]
        · rw [mul_one_div, div_self (by exact_mod_cast hz)]
  have hc : (Fintype.card X : ℝ) ≤ (Fintype.card Y : ℝ) := calc
    _ = ∑ _x : X, (1 : ℝ) := by simp
    _ ≤ ∑ x : X, ∑ y : Y, w x y := sum_le_sum (fun x _ => hrow x)
    _ = ∑ y : Y, ∑ x : X, w x y := sum_comm
    _ ≤ ∑ _y : Y, (1 : ℝ) := sum_le_sum (fun y _ => hcol y)
    _ = _ := by simp
  exact_mod_cast hc

end DegreeCharge
end Erdos643
