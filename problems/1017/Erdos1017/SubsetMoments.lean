import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unnormalized uniform mass on the d-element subsets of T. -/
noncomputable def layerMass (T : Finset ι) (d : ℕ) (S : Finset ι) : ℝ :=
  if S ∈ T.powersetCard d then 1 else 0

noncomputable def subsetMoment (w : Finset ι → ℝ) (B : Finset ι) : ℝ :=
  ∑ S, if B ⊆ S then w S else 0

theorem layer_moment_card (T B : Finset ι) (d : ℕ) :
    subsetMoment (layerMass T d) B = ((T.powersetCard d).filter (B ⊆ ·)).card := by
  simp only [subsetMoment, layerMass]
  have hi (S : Finset ι) :
      (if B ⊆ S then (if S ∈ T.powersetCard d then (1 : ℝ) else 0) else 0) =
      (if S ∈ (T.powersetCard d).filter (B ⊆ ·) then 1 else 0) := by
    by_cases h : B ⊆ S <;> simp [h]
  simp_rw [hi]
  simp
  congr 1
  ext S
  simp

theorem layer_moment (T B : Finset ι) (d : ℕ) (hBT : B ⊆ T) (hBd : B.card ≤ d) :
    subsetMoment (layerMass T d) B = ((T.card - B.card).choose (d-B.card) : ℝ) := by
  rw [layer_moment_card, Finset.card_filter_powersetCard_subset B T d hBT hBd]

theorem layer_moment_zero_of_card (T B : Finset ι) (d : ℕ) (hBd : d < B.card) :
    subsetMoment (layerMass T d) B = 0 := by
  rw [layer_moment_card]
  have hz : (T.powersetCard d).filter (B ⊆ ·) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    obtain ⟨hST, hBS⟩ := Finset.mem_filter.mp hS
    have hcard := (Finset.mem_powersetCard.mp hST).2
    have hle := Finset.card_le_card hBS
    omega
  simp [hz]

theorem layer_moment_zero_of_not_subset (T B : Finset ι) (d : ℕ) (hBT : ¬ B ⊆ T) :
    subsetMoment (layerMass T d) B = 0 := by
  rw [layer_moment_card]
  have hz : (T.powersetCard d).filter (B ⊆ ·) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    obtain ⟨hST, hBS⟩ := Finset.mem_filter.mp hS
    exact hBT (hBS.trans (Finset.mem_powersetCard.mp hST).1)
  simp [hz]

theorem layer_moment_formula (T B : Finset ι) (d : ℕ) (hBT : B ⊆ T) :
    subsetMoment (layerMass T d) B =
      if B.card ≤ d then ((T.card - B.card).choose (d-B.card) : ℝ) else 0 := by
  by_cases h : B.card ≤ d
  · rw [if_pos h]; exact layer_moment T B d hBT h
  · rw [if_neg h]; exact layer_moment_zero_of_card T B d (Nat.lt_of_not_ge h)

theorem subsetMoment_add (w z : Finset ι → ℝ) (B : Finset ι) :
    subsetMoment (fun S => w S + z S) B = subsetMoment w B + subsetMoment z B := by
  unfold subsetMoment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

theorem subsetMoment_sub (w z : Finset ι → ℝ) (B : Finset ι) :
    subsetMoment (fun S => w S - z S) B = subsetMoment w B - subsetMoment z B := by
  unfold subsetMoment
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

theorem subsetMoment_mul (w : Finset ι → ℝ) (t : ℝ) (B : Finset ι) :
    subsetMoment (fun S => t * w S) B = t * subsetMoment w B := by
  unfold subsetMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

end Erdos1017
