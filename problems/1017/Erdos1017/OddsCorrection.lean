import Erdos1017.CollisionBound
import Erdos1017.OddsBounds

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

/-- The first-order corrected lower bound used for degrees 3, 4, 5 and 6 in
the sharp-line rectangle certificate. The theorem holds for every degree at least 3. -/
theorem first_order_odds_lower (s : Finset ι) (p : ι → ℝ) (m : ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hm : ∀ i ∈ s, p i ≤ m) (hm1 : m < 1)
    (hSm : 0 ≤ (∑ i ∈ s, p i)-m)
    (hgap : 0 < (∑ i ∈ s, p i)-(∑ i ∈ s, (p i)^2)) (k : ℕ) :
    collisionLower (k+1) (∑ i ∈ s, p i) (∑ i ∈ s, (p i)^2) +
      ((∑ i ∈ s, p i)*(∑ i ∈ s, (p i)^2)/
        ((∑ i ∈ s, p i)-(∑ i ∈ s, (p i)^2))) *
        collisionLower k ((∑ i ∈ s, p i)-m) (∑ i ∈ s, (p i)^2) ≤
      elementarySum s (fun i => p i/(1-p i)) (k+3) := by
  let d : ι → ℝ := fun i => (p i)^2/(1-p i)
  have hlt : ∀ i ∈ s, p i < 1 := fun i hi => (hm i hi).trans_lt hm1
  have hd : ∀ i ∈ s, 0 ≤ d i := fun i hi =>
    div_nonneg (sq_nonneg _) (sub_pos.mpr (hlt i hi)).le
  have hbase : collisionLower (k+1) (∑ i ∈ s, p i) (∑ i ∈ s, (p i)^2) ≤
      elementarySum s p (k+3) := by
    simpa only [Nat.add_assoc] using collisionLower_le_elementarySum s p hp (k+1)
  have hminor (i : ι) (hi : i ∈ s) :
      collisionLower k ((∑ j ∈ s, p j)-m) (∑ j ∈ s, (p j)^2) ≤
        elementarySum (s.erase i) p (k+2) := by
    apply collisionLower_of_bounds (s.erase i) p
      (fun j hj => hp j (Finset.mem_of_mem_erase hj)) k _ _ hSm
    · have he := Finset.sum_erase_add s p hi
      linarith [hm i hi]
    · have he := Finset.sum_erase_add s (fun j => (p j)^2) hi
      linarith [sq_nonneg (p i)]
  have hc := (odds_sum_certificate s p m hp hm hm1 hgap).2
  have hcorr :
      ((∑ i ∈ s, p i)*(∑ i ∈ s, (p i)^2)/
        ((∑ i ∈ s, p i)-(∑ i ∈ s, (p i)^2))) *
        collisionLower k ((∑ i ∈ s, p i)-m) (∑ i ∈ s, (p i)^2) ≤
        ∑ i ∈ s, d i * elementarySum (s.erase i) p (k+2) := by
    calc
      _ ≤ (∑ i ∈ s, d i) * collisionLower k ((∑ i ∈ s, p i)-m)
          (∑ i ∈ s, (p i)^2) :=
        mul_le_mul_of_nonneg_right hc (collisionLower_nonneg _ _ _)
      _ = ∑ i ∈ s, d i * collisionLower k ((∑ j ∈ s, p j)-m)
          (∑ j ∈ s, (p j)^2) := Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hminor i hi) (hd i hi))
  have hfirst := elementarySum_add_first_order s p d hp hd (k+3)
  have hreindex : (∑ T ∈ s.powersetCard (k+3), firstOrderTerm T p d) =
      ∑ i ∈ s, d i * elementarySum (s.erase i) p (k+2) := by
    simpa only [Nat.add_assoc] using sum_firstOrderTerm s p d (k+2)
  rw [hreindex] at hfirst
  have heq : elementarySum s (fun i => p i+d i) (k+3) =
      elementarySum s (fun i => p i/(1-p i)) (k+3) := by
    apply Finset.sum_congr rfl
    intro T hT
    apply Finset.prod_congr rfl
    intro i hi
    exact (odds_decomposition (p i) (hlt i ((Finset.mem_powersetCard.mp hT).1 hi))).symm
  rw [heq] at hfirst
  linarith

end Erdos1017
