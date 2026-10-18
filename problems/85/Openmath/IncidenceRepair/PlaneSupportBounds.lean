import Openmath.IncidenceRepair.PlaneSupport

namespace Erdos85.IncidenceRepair

/-- The final scalar support argument (2.5)--(2.7), including the two-element field. -/
theorem support_bounds (q : ℕ) (hq : 2 ≤ q) (x y η : ℝ)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 12)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hxq : x ≤ q) (hyq : y ≤ q)
    (hclose : |x - y| ≤ η * q)
    (hcover : (q : ℝ) + 1 - η * q ≤ x + y)
    (hproduct : (x - 1) * (q - y) ≤ 4 * η * (q : ℝ)^2) :
    (q : ℝ) - x ≤ 17 * η * q ∧ (q : ℝ) - y ≤ 16 * η * q := by
  by_cases hq2 : q = 2
  · subst q
    norm_num at hxq hyq ⊢
    constructor <;> nlinarith
  · have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast (show 3 ≤ q by omega)
    have hqpos : (0 : ℝ) < q := by linarith
    obtain ⟨hclose₁, hclose₂⟩ := abs_le.mp hclose
    have hηq := mul_le_mul_of_nonneg_right hηsmall (le_of_lt hqpos)
    have hlower : (q : ℝ) / 4 ≤ x - 1 := by nlinarith
    have hmul := mul_nonneg (sub_nonneg.mpr hlower) (sub_nonneg.mpr hyq)
    have hybound : (q : ℝ) - y ≤ 16 * η * q := by
      nlinarith
    constructor
    · nlinarith
    · exact hybound

open Finset

/-- Normalize the exact mixed-pair counting estimate by the actual error budgets.
The geometric layer supplies `hgood`; all multiplicities are proved in PlaneSupport. -/
theorem mixed_support_product {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (X Y BX BY bad : Finset K) (E : Finset (K × K)) (η : ℝ)
    (hη : 0 ≤ η) (hX : (0 : K) ∈ X) (hY : (0 : K) ∈ Y)
    (hYBY : Disjoint Y BY)
    (hgood : ∀ a : K, a ≠ 0 → a ∉ bad →
      (X.filter fun t => a * t ∈ univ \ (Y ∪ BY)) ⊆ slopeErrors E a ∨
      ((univ \ (X ∪ BX)).filter fun t => a * t ∈ Y) ⊆ slopeErrors E a)
    (hcost : (Fintype.card K : ℝ) * bad.card + E.card ≤ η * (Fintype.card K : ℝ)^2)
    (himbalance : |(X.card : ℝ) - Y.card| + BX.card + BY.card ≤
      2 * η * Fintype.card K)
    (hBY : (BY.card : ℝ) ≤ η * Fintype.card K) :
    ((X.card : ℝ) - 1) * ((Fintype.card K : ℝ) - Y.card) ≤
      4 * η * (Fintype.card K : ℝ)^2 := by
  let q := Fintype.card K
  have hq : 1 ≤ q := Fintype.card_pos
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hXcard : 1 ≤ X.card := card_pos.mpr ⟨0, hX⟩
  have hXq : X.card ≤ q := card_le_univ _
  have hXqR : (X.card : ℝ) ≤ q := by exact_mod_cast hXq
  have hXcardR : (1 : ℝ) ≤ X.card := by exact_mod_cast hXcard
  have hz : (univ \ (Y ∪ BY)).card + Y.card + BY.card = q := by
    have hc := card_sdiff_add_card_eq_card (subset_univ (Y ∪ BY))
    rw [card_union_of_disjoint hYBY, card_univ] at hc
    omega
  have hzR : ((univ \ (Y ∪ BY)).card : ℝ) = q - Y.card - BY.card := by
    have hh : ((univ \ (Y ∪ BY)).card : ℝ) + Y.card + BY.card = q := by exact_mod_cast hz
    linarith
  have hxR : ((X.erase 0).card : ℝ) = (X.card : ℝ) - 1 := by
    rw [card_erase_of_mem hX, Nat.cast_sub hXcard]
    norm_num
  have hqminus : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub hq]
    norm_num
  have habs : (Int.natAbs ((X.card : ℤ) - Y.card) : ℝ) = |(X.card : ℝ) - Y.card| := by
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  have hp := mixed_product_bound X Y BX BY bad E hY hgood
  have hpR : ((X.erase 0).card : ℝ) * (univ \ (Y ∪ BY)).card ≤
      (q : ℝ) * bad.card + E.card + ((q - 1 : ℕ) : ℝ) *
        ((Int.natAbs ((X.card : ℤ) - Y.card) : ℝ) + BX.card + BY.card) := by
    exact_mod_cast hp
  rw [hxR, hzR, hqminus, habs] at hpR
  have hi := mul_le_mul_of_nonneg_left himbalance (by linarith : (0 : ℝ) ≤ q - 1)
  have heq : (Fintype.card K : ℝ) = q := rfl
  rw [heq] at hcost himbalance hBY hi ⊢
  have hetaq : 0 ≤ η * q := mul_nonneg hη (by positivity)
  have hby0 : (0 : ℝ) ≤ BY.card := by positivity
  have hbyx := mul_nonneg (sub_nonneg.mpr hXqR) hby0
  have hbyq := mul_le_mul_of_nonneg_left hBY (by positivity : (0 : ℝ) ≤ q)
  nlinarith

/-- Full finite-set support conclusion from the geometric marked-set premise and
its normalized budgets. The conclusion is exactly the 17/16 support estimate. -/
theorem finite_support_bounds {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (X Y BX BY bad : Finset K) (E : Finset (K × K)) (η : ℝ)
    (hq : 2 ≤ Fintype.card K) (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 12)
    (hX0 : (0 : K) ∈ X) (hY0 : (0 : K) ∈ Y)
    (hX2 : 2 ≤ X.card) (hY2 : 2 ≤ Y.card) (hYBY : Disjoint Y BY)
    (hgood : ∀ a : K, a ≠ 0 → a ∉ bad →
      (X.filter fun t => a * t ∈ univ \ (Y ∪ BY)) ⊆ slopeErrors E a ∨
      ((univ \ (X ∪ BX)).filter fun t => a * t ∈ Y) ⊆ slopeErrors E a)
    (hcost : (Fintype.card K : ℝ) * bad.card + E.card ≤ η * (Fintype.card K : ℝ)^2)
    (himbalance : |(X.card : ℝ) - Y.card| + BX.card + BY.card ≤
      2 * η * Fintype.card K)
    (hBY : (BY.card : ℝ) ≤ η * Fintype.card K)
    (hclose : |(X.card : ℝ) - Y.card| ≤ η * Fintype.card K)
    (hcover : (Fintype.card K : ℝ) + 1 - η * Fintype.card K ≤ X.card + Y.card) :
    (Fintype.card K : ℝ) - X.card ≤ 17 * η * Fintype.card K ∧
    (Fintype.card K : ℝ) - Y.card ≤ 16 * η * Fintype.card K := by
  have hp := mixed_support_product X Y BX BY bad E η hη hX0 hY0 hYBY hgood
    hcost himbalance hBY
  apply support_bounds (Fintype.card K) hq X.card Y.card η hη hηsmall
  · exact_mod_cast hX2
  · exact_mod_cast hY2
  · exact_mod_cast card_le_univ X
  · exact_mod_cast card_le_univ Y
  · exact hclose
  · exact hcover
  · exact hp

end Erdos85.IncidenceRepair
