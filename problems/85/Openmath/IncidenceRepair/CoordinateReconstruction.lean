import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
Actual Cartesian-chart counting for §6 of the incidence repair argument.
Geometry supplies the reconstruction implication, but coordinate fiber sizes and
the global union bound are proved here from the full finite Cartesian domain.
-/

open scoped BigOperators

namespace Erdos85.IncidenceRepair

/-- Each coordinate value occurs equally often in the entire affine chart. -/
theorem coordinate_fiber_card
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    (i : I) (a : K) :
    (Finset.univ.filter (fun x : I → K => x i = a)).card =
      Fintype.card K ^ (Fintype.card I - 1) := by
  simpa only [Fintype.piFinset_univ, Finset.card_univ] using
    Fintype.card_filter_piFinset_const_eq_of_mem (ι := I)
      (Finset.univ : Finset K) i (Finset.mem_univ a)

/-- Exact number of full-chart assignments with one coordinate in a bad set. -/
theorem coordinate_preimage_card
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    (i : I) (s : Finset K) :
    (Finset.univ.filter (fun x : I → K => x i ∈ s)).card =
      Fintype.card K ^ (Fintype.card I - 1) * s.card := by
  calc
    (Finset.univ.filter (fun x : I → K => x i ∈ s)).card =
        ∑ x ∈ Finset.univ.filter (fun x : I → K => x i ∈ s), (1 : ℕ) :=
      Finset.card_eq_sum_ones _
    _ = ∑ a ∈ s, ∑ x ∈ Finset.univ.filter (fun x : I → K => x i = a), (1 : ℕ) :=
      (Finset.sum_fiberwise_eq_sum_filter Finset.univ s (fun x : I → K => x i)
        (fun _ => (1 : ℕ))).symm
    _ = ∑ _a ∈ s, Fintype.card K ^ (Fintype.card I - 1) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.card_eq_sum_ones, coordinate_fiber_card]
    _ = Fintype.card K ^ (Fintype.card I - 1) * s.card := by simp [mul_comm]

/-- Full affine-chart mismatch bound. The exceptional flag set is a set of
actual full-chart points. Coordinate exceptions are lifted with their exact
fiber cardinality; their overlaps can only improve the bound. -/
theorem coordinate_reconstruction_card_le
    {I K L P : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K] [DecidableEq L] [DecidableEq P]
    (φ : (I → K) → P) (τ : (I → L) → P)
    (f : I → K → L) (σ : K → L)
    (proper : I → Finset K) (badFlags : Finset (I → K))
    (hreconstruct : ∀ x, x ∉ badFlags → (∀ i, x i ∈ proper i) →
      φ x = τ (fun i => f i (x i))) :
    (Finset.univ.filter (fun x => φ x ≠ τ (fun i => σ (x i)))).card ≤
      badFlags.card + Fintype.card K ^ (Fintype.card I - 1) *
        ∑ i, ((Finset.univ \ proper i).card +
          (Finset.univ.filter (fun a => f i a ≠ σ a)).card) := by
  classical
  let coordinateBad (i : I) : Finset K :=
    (Finset.univ \ proper i) ∪ Finset.univ.filter (fun a => f i a ≠ σ a)
  let lifted (i : I) : Finset (I → K) :=
    Finset.univ.filter (fun x => x i ∈ coordinateBad i)
  have hsub : Finset.univ.filter (fun x => φ x ≠ τ (fun i => σ (x i))) ⊆
      badFlags ∪ Finset.univ.biUnion lifted := by
    intro x hx
    by_cases hb : x ∈ badFlags
    · exact Finset.mem_union_left _ hb
    · apply Finset.mem_union_right
      by_contra hn
      have hclean : ∀ i, x i ∉ coordinateBad i := by
        intro i hi
        exact hn (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
          Finset.mem_filter.mpr ⟨Finset.mem_univ x, hi⟩⟩)
      have hp : ∀ i, x i ∈ proper i := by
        intro i
        by_contra hi
        exact hclean i (Finset.mem_union_left _ (by simp [hi]))
      have heq : (fun i => f i (x i)) = (fun i => σ (x i)) := by
        funext i
        by_contra hi
        exact hclean i (Finset.mem_union_right _ (by simp [hi]))
      exact (Finset.mem_filter.mp hx).2 (by rw [hreconstruct x hb hp, heq])
  calc
    _ ≤ (badFlags ∪ Finset.univ.biUnion lifted).card := Finset.card_le_card hsub
    _ ≤ badFlags.card + (Finset.univ.biUnion lifted).card := Finset.card_union_le _ _
    _ ≤ badFlags.card + ∑ i, (lifted i).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ = badFlags.card + ∑ i,
        Fintype.card K ^ (Fintype.card I - 1) * (coordinateBad i).card := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact coordinate_preimage_card i (coordinateBad i)
    _ ≤ badFlags.card + ∑ i, Fintype.card K ^ (Fintype.card I - 1) *
        ((Finset.univ \ proper i).card +
          (Finset.univ.filter (fun a => f i a ≠ σ a)).card) := by
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul_left _ (Finset.card_union_le _ _)
    _ = _ := by rw [Finset.mul_sum]

/-- Numerical specialization of the full-chart count with the constants in §6. -/
theorem coordinate_reconstruction_numeric_bound
    {I K L P : Type*} [Fintype I] [Fintype K] [Nonempty I]
    [DecidableEq I] [DecidableEq K] [DecidableEq L] [DecidableEq P]
    (φ : (I → K) → P) (τ : (I → L) → P)
    (f : I → K → L) (σ : K → L)
    (proper : I → Finset K) (badFlags : Finset (I → K))
    (hreconstruct : ∀ x, x ∉ badFlags → (∀ i, x i ∈ proper i) →
      φ x = τ (fun i => f i (x i)))
    (γ η E : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (hE : γ + η ≤ E)
    (hflags : (badFlags.card : ℝ) ≤ γ * (Fintype.card K : ℝ) ^ Fintype.card I)
    (hproper : (∑ i, ((Finset.univ \ proper i).card : ℝ)) ≤
      34 * η * (Fintype.card K : ℝ))
    (hscalar : (∑ i, ((Finset.univ.filter (fun a => f i a ≠ σ a)).card : ℝ)) ≤
      936 * η * (Fintype.card K : ℝ)) :
    ((Finset.univ.filter (fun x => φ x ≠ τ (fun i => σ (x i)))).card : ℝ) ≤
      (γ + 970 * η) * (Fintype.card K : ℝ) ^ Fintype.card I ∧
    (γ + 970 * η) * (Fintype.card K : ℝ) ^ Fintype.card I ≤
      971 * E * (Fintype.card K : ℝ) ^ Fintype.card I := by
  classical
  have hc :
      ((Finset.univ.filter (fun x => φ x ≠ τ (fun i => σ (x i)))).card : ℝ) ≤
        (badFlags.card : ℝ) + (Fintype.card K : ℝ) ^ (Fintype.card I - 1) *
          ∑ i, (((Finset.univ \ proper i).card : ℝ) +
            ((Finset.univ.filter (fun a => f i a ≠ σ a)).card : ℝ)) := by
    exact_mod_cast coordinate_reconstruction_card_le φ τ f σ proper badFlags hreconstruct
  have hpow : (Fintype.card K : ℝ) ^ (Fintype.card I - 1) * (Fintype.card K : ℝ) =
      (Fintype.card K : ℝ) ^ Fintype.card I := by
    rw [← pow_succ, Nat.sub_add_cancel Fintype.card_pos]
  rw [Finset.sum_add_distrib] at hc
  have hm := mul_le_mul_of_nonneg_left (add_le_add hproper hscalar)
    (show 0 ≤ (Fintype.card K : ℝ) ^ (Fintype.card I - 1) by positivity)
  constructor
  · calc
      _ ≤ γ * (Fintype.card K : ℝ) ^ Fintype.card I +
          (Fintype.card K : ℝ) ^ (Fintype.card I - 1) *
            (34 * η * (Fintype.card K : ℝ) + 936 * η * (Fintype.card K : ℝ)) :=
        hc.trans (add_le_add hflags hm)
      _ = _ := by nlinarith [hpow]
  · apply mul_le_mul_of_nonneg_right
    · linarith
    · positivity

end Erdos85.IncidenceRepair
