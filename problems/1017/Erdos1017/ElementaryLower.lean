import Erdos1017.ElementaryIncidence

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

theorem elementarySum_one (s : Finset ι) (p : ι → ℝ) :
    elementarySum s p 1 = ∑ i ∈ s, p i := by
  simpa [elementarySum_zero] using (elementarySum_degree_identity s p 0).symm

theorem elementarySum_erase (s : Finset ι) (p : ι → ℝ) (i : ι) (hi : i ∈ s) (k : ℕ) :
    elementarySum s p (k+1) = elementarySum (s.erase i) p (k+1) +
      p i * elementarySum (s.erase i) p k := by
  simpa [Finset.insert_erase hi] using
    elementarySum_insert (s.erase i) p i (Finset.notMem_erase i s) k

theorem elementarySum_sum_recurrence (s : Finset ι) (p : ι → ℝ) (k : ℕ) :
    (∑ i ∈ s, p i) * elementarySum s p (k+1) =
      (k+2 : ℕ) * elementarySum s p (k+2) +
        ∑ i ∈ s, (p i)^2 * elementarySum (s.erase i) p k := by
  rw [Finset.sum_mul, ← elementarySum_degree_identity s p (k+1), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [elementarySum_erase s p i hi k]
  ring

theorem factorial_mul_repeated_term_le (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (k : ℕ) :
    (k.factorial : ℝ) * (∑ i ∈ s, (p i)^2 * elementarySum (s.erase i) p k) ≤
      (∑ i ∈ s, (p i)^2) * (∑ i ∈ s, p i)^k := by
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hn : 0 ≤ ∑ j ∈ s.erase i, p j :=
    Finset.sum_nonneg (fun j hj => hp j (Finset.mem_of_mem_erase hj))
  have hs : (∑ j ∈ s.erase i, p j) ≤ ∑ j ∈ s, p j := by
    have he := Finset.sum_erase_add s p hi
    linarith [hp i hi]
  have hu := (factorial_mul_elementarySum_le (s.erase i) p
    (fun j hj => hp j (Finset.mem_of_mem_erase hj)) k).trans (pow_le_pow_left₀ hn hs k)
  have hm := mul_le_mul_of_nonneg_left hu (sq_nonneg (p i))
  nlinarith

/-- A collision union bound, obtained algebraically from the elementary-sum recurrence.
It is uniform in the number of coordinates and allows zeros. -/
theorem factorial_mul_elementarySum_lower (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (k : ℕ) :
    (∑ i ∈ s, p i)^(k+2) - ((k+2 : ℝ)*(k+1)/2) *
      (∑ i ∈ s, p i)^k * (∑ i ∈ s, (p i)^2) ≤
      ((k+2).factorial : ℝ) * elementarySum s p (k+2) := by
  have hs : 0 ≤ ∑ i ∈ s, p i := Finset.sum_nonneg hp
  induction k with
  | zero =>
    have he := elementarySum_sum_recurrence s p 0
    norm_num [elementarySum_one, elementarySum_zero] at he ⊢
    nlinarith
  | succ k ih =>
    have he := elementarySum_sum_recurrence s p (k+1)
    have hu := factorial_mul_repeated_term_le s p hp (k+1)
    have hmul := mul_le_mul_of_nonneg_left ih hs
    have hrec := congrArg (fun x : ℝ => ((k+2).factorial : ℝ) * x) he
    have hub := mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ k+2)
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, Nat.add_assoc, pow_succ, pow_zero, mul_one] at hrec hub hmul ⊢
    nlinarith

end Erdos1017
