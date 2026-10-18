import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Finite-field counting components of the protected-plane support argument.
These lemmas do not assert the geometric broken-flag implications. -/

namespace Erdos85.IncidenceRepair
open Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The actual number of mixed coordinates on slope `a`. -/
def mixedCount (X Z : Finset K) (a : K) : ℕ :=
  (X.filter fun t => a * t ∈ Z).card

/-- Every mixed pair with both coordinates nonzero has exactly one nonzero slope. -/
theorem slope_multiplicity (X Z : Finset K) (hZ : (0 : K) ∉ Z) :
    ∑ a ∈ (univ.erase (0 : K)), mixedCount X Z a = (X.erase 0).card * Z.card := by
  let s := (univ.erase (0 : K)).sigma fun a => X.filter fun t => a * t ∈ Z
  have hc : s.card = ((X.erase 0) ×ˢ Z).card := by
    apply Finset.card_bij (fun u _ => (u.2, u.1 * u.2))
    · intro u hu
      simp only [s, mem_sigma, mem_erase, mem_univ, and_true, mem_filter] at hu
      have ht : u.2 ≠ 0 := by
        intro hz
        apply hZ
        simpa [hz] using hu.2.2
      exact mem_product.mpr ⟨mem_erase.mpr ⟨ht, hu.2.1⟩, hu.2.2⟩
    · intro u hu v hv huv
      have ht : u.2 ≠ 0 := by
        intro hz
        have hm := (mem_sigma.mp hu).2
        apply hZ
        simpa [hz] using (mem_filter.mp hm).2
      have htuv : u.2 = v.2 := congrArg Prod.fst huv
      have ha : u.1 = v.1 := by
        apply mul_right_cancel₀ ht
        simpa [← htuv] using congrArg Prod.snd huv
      cases u
      cases v
      simp_all
    · intro p hp
      obtain ⟨hx, hz⟩ := mem_product.mp hp
      obtain ⟨hx0, hxX⟩ := mem_erase.mp hx
      have hz0 : p.2 ≠ 0 := fun hh => hZ (hh ▸ hz)
      refine ⟨⟨p.2 / p.1, p.1⟩, ?_, ?_⟩
      · simp only [s, mem_sigma, mem_erase, mem_univ, and_true, mem_filter]
        exact ⟨div_ne_zero hz0 hx0, hxX, by simpa [div_mul_cancel₀ _ hx0] using hz⟩
      · simp [div_mul_cancel₀ _ hx0]
  simpa [s, card_sigma, mixedCount, card_product] using hc

/-- Removing bad coordinates perturbs the two mixed directions only by their sizes. -/
theorem mixed_sdiff_imbalance {α : Type*} [DecidableEq α]
    (X A BX C : Finset α) :
    ((X \ (A ∪ C)).card : ℤ) - (A \ (X ∪ BX)).card ≤
      (X.card : ℤ) - A.card + BX.card ∧
    ((A \ (X ∪ BX)).card : ℤ) - (X \ (A ∪ C)).card ≤
      (A.card : ℤ) - X.card + C.card := by
  have hbase : (X \ A).card + A.card = (A \ X).card + X.card := by
    rw [card_sdiff_add_card, card_sdiff_add_card, union_comm]
  have hleft : (X \ (A ∪ C)).card ≤ (X \ A).card :=
    card_le_card (by intro x hx; simp only [mem_sdiff, mem_union, not_or] at *; exact ⟨hx.1, hx.2.1⟩)
  have hright : (A \ (X ∪ BX)).card ≤ (A \ X).card :=
    card_le_card (by intro x hx; simp only [mem_sdiff, mem_union, not_or] at *; exact ⟨hx.1, hx.2.1⟩)
  have hremoveX := card_le_card_sdiff_add_card (s := A \ X) (t := BX)
  have hremoveY := card_le_card_sdiff_add_card (s := X \ A) (t := C)
  have heqX : (A \ X) \ BX = A \ (X ∪ BX) := by ext; simp; tauto
  have heqY : (X \ A) \ C = X \ (A ∪ C) := by ext; simp; tauto
  rw [heqX] at hremoveX
  rw [heqY] at hremoveY
  constructor <;> omega

/-- Pulling a set back along a nonzero slope preserves its cardinality. -/
theorem slope_preimage_card (Y : Finset K) (a : K) (ha : a ≠ 0) :
    (univ.filter fun t : K => a * t ∈ Y).card = Y.card := by
  apply card_bij (fun t _ => a * t)
  · intro t ht
    exact (mem_filter.mp ht).2
  · intro t ht u hu h
    exact mul_left_cancel₀ ha h
  · intro y hy
    refine ⟨y / a, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩ <;>
      simpa [mul_div_cancel₀ _ ha] using hy

/-- The mixed-direction imbalance from §2.1, for the actual complement sets. -/
theorem mixedCount_imbalance (X Y BX BY : Finset K) (a : K) (ha : a ≠ 0) :
    |(mixedCount X (univ \ (Y ∪ BY)) a : ℤ) -
      mixedCount (univ \ (X ∪ BX)) Y a| ≤
      |(X.card : ℤ) - Y.card| + BX.card + BY.card := by
  let A := univ.filter fun t : K => a * t ∈ Y
  let C := univ.filter fun t : K => a * t ∈ BY
  have hA : A.card = Y.card := slope_preimage_card Y a ha
  have hC : C.card = BY.card := slope_preimage_card BY a ha
  have hr : mixedCount X (univ \ (Y ∪ BY)) a = (X \ (A ∪ C)).card := by
    unfold mixedCount
    congr 1
    ext t
    simp [A, C]
  have hs : mixedCount (univ \ (X ∪ BX)) Y a = (A \ (X ∪ BX)).card := by
    unfold mixedCount
    congr 1
    ext t
    simp [A]
    tauto
  obtain ⟨h₁, h₂⟩ := mixed_sdiff_imbalance X A BX C
  rw [hA] at h₁
  rw [hA, hC] at h₂
  rw [hr, hs]
  have hplus := le_abs_self ((X.card : ℤ) - Y.card)
  have hminus := neg_le_abs ((X.card : ℤ) - Y.card)
  rw [abs_le]
  constructor <;> omega

/-- Reciprocal coverage gains one because both good sets contain zero. -/
theorem overlap_coverage_card {α : Type*} [Fintype α] [DecidableEq α]
    (X Y E : Finset α) (z : α) (hzX : z ∈ X) (hzY : z ∈ Y)
    (hcover : univ ⊆ X ∪ Y ∪ E) :
    Fintype.card α + 1 ≤ X.card + Y.card + E.card := by
  have hc := card_le_card hcover
  have hu := card_union_le (X ∪ Y) E
  have he := card_union_add_card_inter X Y
  have hi : 1 ≤ (X ∩ Y).card := by
    exact card_pos.mpr ⟨z, mem_inter.mpr ⟨hzX, hzY⟩⟩
  simp only [card_univ] at hc
  omega

/-- The reciprocal-slope coverage count (2.6), with the exceptional slopes explicit. -/
theorem reciprocal_coverage (X Y BX BY R : Finset K)
    (hX : (0 : K) ∈ X) (hY : (0 : K) ∈ Y)
    (hcover : ∀ a : K, a ≠ 0 →
      a ∈ Y ∨ a ∈ BY ∨ a⁻¹ ∈ X ∨ a⁻¹ ∈ BX ∨ a ∈ R) :
    Fintype.card K + 1 ≤ X.card + Y.card + BX.card + BY.card + R.card := by
  let XI := X.image fun a => a⁻¹
  let BI := BX.image fun a => a⁻¹
  have hXI : XI.card = X.card := card_image_of_injective X inv_injective
  have hBI : BI.card = BX.card := card_image_of_injective BX inv_injective
  have hzero : (0 : K) ∈ XI := mem_image.mpr ⟨0, hX, inv_zero⟩
  have hc : univ ⊆ XI ∪ Y ∪ (BY ∪ BI ∪ R) := by
    intro a ha
    by_cases hz : a = 0
    · subst a
      simp only [mem_union]
      exact Or.inl (Or.inr hY)
    · rcases hcover a hz with hy | hby | hx | hbx | hr
      · exact mem_union_left _ (mem_union_right _ hy)
      · exact mem_union_right _ (mem_union_left _ (mem_union_left _ hby))
      · exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨a⁻¹, hx, inv_inv a⟩))
      · exact mem_union_right _ (mem_union_left _ (mem_union_right _
          (mem_image.mpr ⟨a⁻¹, hbx, inv_inv a⟩)))
      · exact mem_union_right _ (mem_union_right _ hr)
  have hb := overlap_coverage_card XI Y (BY ∪ BI ∪ R) 0 hzero hY hc
  have hu₁ := card_union_le BY BI
  have hu₂ := card_union_le (BY ∪ BI) R
  rw [hXI] at hb
  rw [hBI] at hu₁
  omega

/-- Marked nonzero first coordinates on a given pencil line. -/
def slopeErrors (E : Finset (K × K)) (a : K) : Finset K :=
  univ.filter fun t => t ≠ 0 ∧ (t, a * t) ∈ E

/-- A marked affine point with nonzero first coordinate is charged on at most one slope. -/
theorem slope_error_load (E : Finset (K × K)) :
    ∑ a ∈ univ.erase (0 : K), (slopeErrors E a).card ≤ E.card := by
  let s := (univ.erase (0 : K)).sigma (slopeErrors E)
  have hc : s.card ≤ E.card := by
    apply card_le_card_of_injOn (fun u => (u.2, u.1 * u.2))
    · intro u hu
      exact (mem_filter.mp (mem_sigma.mp hu).2).2.2
    · intro u hu v hv huv
      have ht := (mem_filter.mp (mem_sigma.mp hu).2).2.1
      have htuv : u.2 = v.2 := congrArg Prod.fst huv
      have ha : u.1 = v.1 := by
        apply mul_right_cancel₀ ht
        simpa [← htuv] using congrArg Prod.snd huv
      cases u
      cases v
      simp_all
  simpa [s, card_sigma] using hc

/-- The pencil charging inequality: bad anchors cost at most a whole line, while
all remaining mixed-coordinate charges are paid once by the explicit affine error set. -/
theorem pencil_min_bound (R S : K → Finset K) (bad : Finset K)
    (E : Finset (K × K))
    (hgood : ∀ a : K, a ≠ 0 → a ∉ bad →
      R a ⊆ slopeErrors E a ∨ S a ⊆ slopeErrors E a) :
    ∑ a ∈ univ.erase (0 : K), min (R a).card (S a).card ≤
      Fintype.card K * bad.card + E.card := by
  let A := univ.erase (0 : K)
  have hpoint : ∀ a ∈ A, min (R a).card (S a).card ≤
      (if a ∈ bad then Fintype.card K else 0) + (slopeErrors E a).card := by
    intro a ha
    by_cases hb : a ∈ bad
    · simp only [hb, ↓reduceIte]
      have hr : (R a).card ≤ Fintype.card K := card_le_univ _
      exact (min_le_left _ _).trans (hr.trans (Nat.le_add_right _ _))
    · simp only [hb, ↓reduceIte, zero_add]
      rcases hgood a (mem_erase.mp ha).1 hb with hr | hs
      · exact (min_le_left _ _).trans (card_le_card hr)
      · exact (min_le_right _ _).trans (card_le_card hs)
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib] at hsum
  have hbad : (∑ a ∈ A, if a ∈ bad then Fintype.card K else 0) ≤
      Fintype.card K * bad.card := by
    rw [← sum_filter]
    simp only [sum_const, smul_eq_mul]
    have hc : (A.filter fun a => a ∈ bad).card ≤ bad.card :=
      card_le_card (by intro a ha; exact (mem_filter.mp ha).2)
    simpa [mul_comm] using Nat.mul_le_mul_left (Fintype.card K) hc
  have he := slope_error_load E
  exact hsum.trans (Nat.add_le_add hbad he)

/-- Exact combinatorial product estimate before normalizing the flag-error budget.
The premise says that, on an unbroken anchor, one of the two mixed types is marked. -/
theorem mixed_product_bound (X Y BX BY bad : Finset K) (E : Finset (K × K))
    (hY : (0 : K) ∈ Y)
    (hgood : ∀ a : K, a ≠ 0 → a ∉ bad →
      (X.filter fun t => a * t ∈ univ \ (Y ∪ BY)) ⊆ slopeErrors E a ∨
      ((univ \ (X ∪ BX)).filter fun t => a * t ∈ Y) ⊆ slopeErrors E a) :
    (X.erase 0).card * (univ \ (Y ∪ BY)).card ≤
      Fintype.card K * bad.card + E.card +
      (Fintype.card K - 1) *
        (Int.natAbs ((X.card : ℤ) - Y.card) + BX.card + BY.card) := by
  let R := fun a => X.filter fun t => a * t ∈ univ \ (Y ∪ BY)
  let S := fun a => (univ \ (X ∪ BX)).filter fun t => a * t ∈ Y
  let b := Int.natAbs ((X.card : ℤ) - Y.card) + BX.card + BY.card
  let A := univ.erase (0 : K)
  have hb : (b : ℤ) = |(X.card : ℤ) - Y.card| + BX.card + BY.card := by
    simp [b]
  have hp : ∀ a ∈ A, (R a).card ≤ min (R a).card (S a).card + b := by
    intro a ha
    have hi := mixedCount_imbalance X Y BX BY a (mem_erase.mp ha).1
    change |((R a).card : ℤ) - (S a).card| ≤ _ at hi
    have ha := le_abs_self (((R a).card : ℤ) - (S a).card)
    omega
  have hsum := sum_le_sum hp
  rw [sum_add_distrib] at hsum
  have hm := pencil_min_bound R S bad E hgood
  have hz : (0 : K) ∉ univ \ (Y ∪ BY) := by simp [hY]
  have hmult := slope_multiplicity X (univ \ (Y ∪ BY)) hz
  have hcard : A.card = Fintype.card K - 1 := by simp [A]
  have hconst : (∑ _a ∈ A, b) = (Fintype.card K - 1) * b := by
    simp [hcard]
  rw [hconst] at hsum
  change (∑ a ∈ A, mixedCount X (univ \ (Y ∪ BY)) a) ≤ _ at hsum
  rw [hmult] at hsum
  exact hsum.trans (Nat.add_le_add_right hm _)

end Erdos85.IncidenceRepair
