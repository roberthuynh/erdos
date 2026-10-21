import Erdos1017.ElementaryLower

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

/-- The nonnegative collision lower bound for degree `k+2`. -/
noncomputable def collisionLower (k : ℕ) (S q : ℝ) : ℝ :=
  max 0 ((S^(k+2) - ((k+2 : ℝ)*(k+1)/2)*S^k*q) / (k+2).factorial)

theorem collisionLower_nonneg (k : ℕ) (S q : ℝ) : 0 ≤ collisionLower k S q := le_max_left _ _

theorem collisionLower_mono_sum (k : ℕ) (x y q : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    collisionLower k x q ≤ collisionLower k y q := by
  have hy : 0 ≤ y := hx.trans hxy
  have hf : (0 : ℝ) < (k+2).factorial := by exact_mod_cast Nat.factorial_pos _
  have hform (z : ℝ) : z^(k+2) - ((k+2 : ℝ)*(k+1)/2)*z^k*q =
      z^k * (z^2 - ((k+2 : ℝ)*(k+1)/2)*q) := by ring
  unfold collisionLower
  rw [hform x, hform y]
  by_cases hpos : 0 ≤ x^2 - ((k+2 : ℝ)*(k+1)/2)*q
  · apply max_le_max (le_refl 0)
    apply div_le_div_of_nonneg_right _ hf.le
    exact mul_le_mul (pow_le_pow_left₀ hx hxy k)
      (sub_le_sub_right (by nlinarith : x^2 ≤ y^2) _) hpos (pow_nonneg hy _)
  · have hn : x^k * (x^2 - ((k+2 : ℝ)*(k+1)/2)*q) / (k+2).factorial ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx _) (le_of_not_ge hpos)) hf.le
    rw [max_eq_left hn]
    exact le_max_left _ _

theorem collisionLower_antitone_square (k : ℕ) (S q₁ q₂ : ℝ)
    (hS : 0 ≤ S) (hq : q₁ ≤ q₂) : collisionLower k S q₂ ≤ collisionLower k S q₁ := by
  unfold collisionLower
  apply max_le_max (le_refl 0)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply sub_le_sub_left
  exact mul_le_mul_of_nonneg_left hq (by positivity)

theorem collisionLower_le_elementarySum (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (k : ℕ) :
    collisionLower k (∑ i ∈ s, p i) (∑ i ∈ s, (p i)^2) ≤ elementarySum s p (k+2) := by
  apply max_le (elementarySum_nonneg s p hp _)
  apply (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos (k+2) : (0 : ℝ) < (k+2).factorial)).mpr
  simpa [mul_comm] using factorial_mul_elementarySum_lower s p hp k

theorem collisionLower_of_bounds (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (k : ℕ) (S q : ℝ)
    (hS : 0 ≤ S) (hsum : S ≤ ∑ i ∈ s, p i) (hsq : (∑ i ∈ s, (p i)^2) ≤ q) :
    collisionLower k S q ≤ elementarySum s p (k+2) := by
  exact (collisionLower_mono_sum k S (∑ i ∈ s, p i) q hS hsum).trans
    ((collisionLower_antitone_square k (∑ i ∈ s, p i) _ q (Finset.sum_nonneg hp) hsq).trans
      (collisionLower_le_elementarySum s p hp k))

end Erdos1017
