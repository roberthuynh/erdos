import Erdos1017.Basic
import Erdos1017.ProductSelector
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! An independent rooted constructor on multipartite clique types.
GraphSelector constructs the corresponding graph partitions. -/
namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def rootedMass (a : ℝ) (w : ι → ℝ) (x : ι → Bool) : ℝ :=
  a^2 * selectorMass (fun i => w i / a) x

noncomputable def rootedCost (a : ℝ) (w : ι → ℝ) : ℝ :=
  ∑ x : ι → Bool, if x = (fun _ => false) then 0 else rootedMass a w x

omit [DecidableEq ι] in
theorem rootedMass_nonneg {a : ℝ} (ha : 0 < a) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmax : ∀ i, w i ≤ a) (x : ι → Bool) :
    0 ≤ rootedMass a w x := by
  apply mul_nonneg (sq_nonneg a)
  exact selectorMass_nonneg _ (fun i => div_nonneg (hw i) ha.le)
    (fun i => (div_le_one ha).mpr (hmax i)) x

theorem rooted_root_load {a : ℝ} (ha : a ≠ 0) (w : ι → ℝ) (i : ι) :
    (∑ x : ι → Bool, rootedMass a w x * (if x i then 1 else 0)) = a * w i := by
  simp only [rootedMass, mul_assoc]
  rw [← Finset.mul_sum, selector_singleton]
  field_simp

theorem rooted_pair_load {a : ℝ} (ha : a ≠ 0) (w : ι → ℝ) (i j : ι) (h : i ≠ j) :
    (∑ x : ι → Bool, rootedMass a w x *
      ((if x i then 1 else 0) * (if x j then 1 else 0))) = w i * w j := by
  simp only [rootedMass, mul_assoc]
  rw [← Finset.mul_sum, selector_pair _ i j h]
  field_simp

theorem rooted_total (a : ℝ) (w : ι → ℝ) :
    ∑ x : ι → Bool, rootedMass a w x = a^2 := by
  simp [rootedMass, ← Finset.mul_sum, selector_total]

omit [DecidableEq ι] in
theorem rooted_empty_mass (a : ℝ) (w : ι → ℝ) :
    rootedMass a w (fun _ => false) = a^2 * ∏ i, (1-w i/a) := by
  simp [rootedMass, selectorMass]

theorem rooted_cost_identity (a : ℝ) (w : ι → ℝ) :
    rootedCost a w = a^2 * (1-∏ i, (1-w i/a)) := by
  have hsplit : rootedCost a w + rootedMass a w (fun _ => false) = a^2 := by
    calc
      _ = ∑ x : ι → Bool, rootedMass a w x := by
        have hz : rootedMass a w (fun _ => false) =
            ∑ x : ι → Bool, if x = (fun _ => false) then rootedMass a w x else 0 := by simp
        rw [rootedCost, hz, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> simp_all
      _ = _ := rooted_total a w
  rw [rooted_empty_mass] at hsplit
  calc
    _ = a^2 - a^2 * ∏ i, (1-w i/a) := eq_sub_of_add_eq hsplit
    _ = _ := by ring

theorem rooted_cost_le_square {a : ℝ} (ha : 0 < a) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmax : ∀ i, w i ≤ a) : rootedCost a w ≤ a^2 := by
  rw [← rooted_total a w]
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · exact rootedMass_nonneg ha w hw hmax x
  · exact le_rfl

/-- Certificate for the independent clique-type constructor.
Graph-level lifting is proved separately. -/
theorem rooted_selector_certificate {a : ℝ} (ha : 0 < a) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmax : ∀ i, w i ≤ a) :
    (∀ x, 0 ≤ rootedMass a w x) ∧
    (∀ i, (∑ x : ι → Bool, rootedMass a w x * (if x i then 1 else 0)) = a * w i) ∧
    (∀ i j, i ≠ j → (∑ x : ι → Bool, rootedMass a w x *
      ((if x i then 1 else 0) * (if x j then 1 else 0))) = w i * w j) ∧
    rootedCost a w = a^2 * (1-∏ i, (1-w i/a)) ∧ rootedCost a w ≤ a^2 := by
  exact ⟨rootedMass_nonneg ha w hw hmax, rooted_root_load (ne_of_gt ha) w,
    rooted_pair_load (ne_of_gt ha) w, rooted_cost_identity a w,
    rooted_cost_le_square ha w hw hmax⟩

end Erdos1017
