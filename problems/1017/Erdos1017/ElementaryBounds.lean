import Erdos1017.SubsetMoments
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Elementary symmetric sums used to bound the total withdrawal at each cell. -/
namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

noncomputable def elementarySum (s : Finset ι) (r : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ T ∈ s.powersetCard k, ∏ i ∈ T, r i

theorem elementarySum_nonneg (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) (k : ℕ) :
    0 ≤ elementarySum s r k := by
  apply Finset.sum_nonneg
  intro T hT
  apply Finset.prod_nonneg
  intro i hi
  exact hr i ((Finset.mem_powersetCard.mp hT).1 hi)

theorem elementarySum_zero (s : Finset ι) (r : ι → ℝ) : elementarySum s r 0 = 1 := by
  simp [elementarySum]

theorem elementarySum_empty (r : ι → ℝ) (k : ℕ) :
    elementarySum ∅ r (k+1) = 0 := by
  have h : (∅ : Finset ι).powersetCard (k+1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro T hT
    obtain ⟨hs, hc⟩ := Finset.mem_powersetCard.mp hT
    have ht : T = ∅ := Finset.subset_empty.mp hs
    simp [ht] at hc
  simp [elementarySum, h]

theorem elementarySum_insert (s : Finset ι) (r : ι → ℝ) (a : ι) (ha : a ∉ s) (k : ℕ) :
    elementarySum (insert a s) r (k+1) = elementarySum s r (k+1) + r a * elementarySum s r k := by
  simp only [elementarySum, Finset.powersetCard_eq_filter, Finset.sum_filter]
  rw [Finset.sum_powerset_insert ha]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have haT : a ∉ T := fun h => ha ((Finset.mem_powerset.mp hT) h)
  rw [Finset.card_insert_of_notMem haT, Finset.prod_insert haT]
  by_cases hk : T.card = k <;> simp [hk]

theorem add_pow_first_order (s x : ℝ) (hs : 0 ≤ s) (hx : 0 ≤ x) (k : ℕ) :
    s^(k+1) + (k+1 : ℕ) * x * s^k ≤ (s+x)^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hm := mul_le_mul_of_nonneg_right ih (add_nonneg hs hx)
    have hrem : 0 ≤ (k+1 : ℕ) * x^2 * s^k := by positivity
    push_cast at *
    simp only [pow_succ] at *
    nlinarith

/-- No fixed bound on the number of coordinates is needed. -/
theorem factorial_mul_elementarySum_le (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 ≤ r i) (k : ℕ) :
    (k.factorial : ℝ) * elementarySum s r k ≤ (∑ i ∈ s, r i)^k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    cases k with
    | zero => simp [elementarySum_zero]
    | succ k => simp [elementarySum_empty]
  | @insert a s ha ih =>
    have ha0 : 0 ≤ r a := hr a (Finset.mem_insert_self _ _)
    have hs0 : ∀ i ∈ s, 0 ≤ r i := fun i hi => hr i (Finset.mem_insert_of_mem hi)
    have hsum : 0 ≤ ∑ i ∈ s, r i := Finset.sum_nonneg hs0
    cases k with
    | zero => simp [elementarySum_zero]
    | succ k =>
      rw [elementarySum_insert s r a ha k, Finset.sum_insert ha]
      have h1 := ih hs0 (k+1)
      have h2 := mul_le_mul_of_nonneg_left (ih hs0 k) (mul_nonneg (by positivity : (0 : ℝ) ≤ k+1) ha0)
      have hp := add_pow_first_order (∑ i ∈ s, r i) (r a) hsum ha0 k
      simp only [Nat.cast_add, Nat.cast_one] at hp
      rw [add_comm (r a)]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h1 ⊢
      nlinarith

theorem elementarySum_le_power_div_factorial (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 ≤ r i) (k : ℕ) :
    elementarySum s r k ≤ (∑ i ∈ s, r i)^k / k.factorial := by
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  apply (le_div_iff₀ hk).mpr
  simpa [mul_comm] using factorial_mul_elementarySum_le s r hr k

noncomputable def firstOrderTerm (s : Finset ι) (p d : ι → ℝ) : ℝ :=
  ∑ i ∈ s, d i * ∏ j ∈ s.erase i, p j

theorem firstOrderTerm_nonneg (s : Finset ι) (p d : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hd : ∀ i ∈ s, 0 ≤ d i) : 0 ≤ firstOrderTerm s p d := by
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (hd i hi)
  exact Finset.prod_nonneg (fun j hj => hp j (Finset.mem_of_mem_erase hj))

theorem firstOrderTerm_insert (s : Finset ι) (p d : ι → ℝ) (a : ι) (ha : a ∉ s) :
    firstOrderTerm (insert a s) p d = d a * (∏ i ∈ s, p i) + p a * firstOrderTerm s p d := by
  unfold firstOrderTerm
  rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hai : a ≠ i := by intro h; subst i; exact ha hi
  rw [Finset.erase_insert_of_ne hai, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
  ring

/-- Retain zero and one perturbation factor in the exact product expansion. -/
theorem product_add_first_order (s : Finset ι) (p d : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hd : ∀ i ∈ s, 0 ≤ d i) :
    (∏ i ∈ s, p i) + firstOrderTerm s p d ≤ ∏ i ∈ s, (p i+d i) := by
  induction s using Finset.induction_on with
  | empty => simp [firstOrderTerm]
  | @insert a s ha ih =>
    have hp0 := hp a (Finset.mem_insert_self _ _)
    have hd0 := hd a (Finset.mem_insert_self _ _)
    have hpS : ∀ i ∈ s, 0 ≤ p i := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have hdS : ∀ i ∈ s, 0 ≤ d i := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hi := mul_le_mul_of_nonneg_left (ih hpS hdS) (add_nonneg hp0 hd0)
    have hn := mul_nonneg hd0 (firstOrderTerm_nonneg s p d hpS hdS)
    rw [Finset.prod_insert ha, firstOrderTerm_insert s p d a ha, Finset.prod_insert ha]
    nlinarith

theorem elementarySum_add_first_order (s : Finset ι) (p d : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hd : ∀ i ∈ s, 0 ≤ d i) (k : ℕ) :
    elementarySum s p k + (∑ T ∈ s.powersetCard k, firstOrderTerm T p d) ≤
      elementarySum s (fun i => p i+d i) k := by
  unfold elementarySum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro T hT
  have hsub := (Finset.mem_powersetCard.mp hT).1
  exact product_add_first_order T p d (fun i hi => hp i (hsub hi)) (fun i hi => hd i (hsub hi))

end Erdos1017
