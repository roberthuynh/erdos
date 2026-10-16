import PartialSymmetryCompletion

/-! Actual finite-plane incidence double counting for the elementary Dow route.
For |S|=q+1, lines meeting S in a number other than one, plus q, equal
the sum of selected-point secant degrees. No counting identity is assumed. -/
namespace Erdos60.PartialSymmetryCompletion
open Finset
open scoped BigOperators Classical
variable {P L : Type*} [Membership P L] [Fintype P] [Fintype L]

/-- Selected-point / line incidences counted in both directions. -/
theorem section_incidence_sum [Configuration.ProjectivePlane P L] (S : Finset P) :
    (∑ l : L, (sectionPts S l).card) =
      S.card * (Configuration.ProjectivePlane.order P L + 1) := by
  classical
  simp only [sectionPts,Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x ∈ S, (Configuration.ProjectivePlane.order P L + 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_boole]
      have hc := Configuration.ProjectivePlane.lineCount_eq L x
      simpa [Configuration.lineCount,Nat.card_eq_fintype_card,Fintype.card_subtype] using hc
    _ = _ := by simp

/-- Secant incidences counted by selected points or by their actual lines. -/
theorem secant_incidence_sum (S : Finset P) :
    (∑ x ∈ S, (secantsAt (L := L) S x).card) =
      ∑ l : L, if 2 ≤ (sectionPts S l).card then (sectionPts S l).card else 0 := by
  classical
  unfold secantsAt
  conv_lhs => arg 2; ext x; rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  change (∑ x ∈ S, if x ∈ l ∧ 2 ≤ (sectionPts S l).card then 1 else 0) = _
  by_cases hn : 2 ≤ (sectionPts S l).card
  · simp only [hn,and_true,ite_true]
    rw [← Finset.card_filter]
    rfl
  · simp [hn]

/-- Split total incidence into secants and tangents, with zero-intersection
lines contributing zero. -/
theorem secants_add_tangents (S : Finset P) :
    (∑ x ∈ S, (secantsAt (L := L) S x).card) +
      ((Finset.univ : Finset L).filter fun l => (sectionPts S l).card = 1).card =
      ∑ l : L, (sectionPts S l).card := by
  classical
  rw [secant_incidence_sum,Finset.card_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases h1 : (sectionPts S l).card = 1
  · simp [h1]
  · by_cases h2 : 2 ≤ (sectionPts S l).card
    · simp [h1,h2]
    · have h0 : (sectionPts S l).card = 0 := by omega
      simp [h0]

/-- Exact incidence identity needed for the small exceptional-set route.
The bad-line set counts all intersection sizes other than one, including zero. -/
theorem bad_lines_add_order_eq_secant_sum [Configuration.ProjectivePlane P L]
    (S : Finset P) (hS : S.card = Configuration.ProjectivePlane.order P L + 1) :
    ((Finset.univ : Finset L).filter fun l => (sectionPts S l).card ≠ 1).card +
      Configuration.ProjectivePlane.order P L =
      ∑ x ∈ S, (secantsAt (L := L) S x).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset L))
    (p := fun l => (sectionPts S l).card = 1)
  have hinc := secants_add_tangents (L := L) S
  rw [section_incidence_sum, hS] at hinc
  have hlines := Configuration.ProjectivePlane.card_lines P L
  simp only [Finset.card_univ] at hsplit
  rw [hlines] at hsplit
  nlinarith

/-- Elementary Dow consequence: a noncollinear (q+1)-set has at least 2q
lines whose intersection with it is not exactly one point. -/
theorem bad_lines_lower_of_not_collinear [Configuration.ProjectivePlane P L]
    (S : Finset P) (hS : S.card = Configuration.ProjectivePlane.order P L + 1)
    (hnc : ∀ l : L, ∃ z ∈ S, z ∉ l) :
    2 * Configuration.ProjectivePlane.order P L ≤
      ((Finset.univ : Finset L).filter fun l => (sectionPts S l).card ≠ 1).card := by
  have hq := Configuration.ProjectivePlane.one_lt_order P L
  have hsize : 3 ≤ S.card := by omega
  have hdeg := secant_degree_sum_of_not_collinear S hsize hnc
  have hid := bad_lines_add_order_eq_secant_sum S hS
  rw [hS,Nat.add_sub_cancel] at hdeg
  omega

end Erdos60.PartialSymmetryCompletion
