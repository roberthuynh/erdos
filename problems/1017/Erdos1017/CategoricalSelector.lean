import Erdos1017.ProductSelector

namespace Erdos1017
open scoped BigOperators
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

noncomputable def categoricalMass (q : ι → β → ℝ) (x : ι → β) : ℝ := ∏ i, q i (x i)

omit [DecidableEq β] in
theorem categorical_factorization (q f : ι → β → ℝ) :
    (∑ x : ι → β, categoricalMass q x * ∏ i, f i (x i)) =
      ∏ i, ∑ b, q i b * f i b := by
  simp only [categoricalMass, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b => q i b * f i b)).symm

theorem categorical_total (q : ι → β → ℝ) (h : ∀ i, ∑ b, q i b = 1) :
    ∑ x : ι → β, categoricalMass q x = 1 := by
  simpa [h] using categorical_factorization q (fun _ _ => 1)

theorem categorical_pair (q : ι → β → ℝ) (hn : ∀ i, ∑ b, q i b = 1)
    (i j : ι) (hij : i ≠ j) (u v : β) :
    (∑ x : ι → β, categoricalMass q x *
      ((if x i = u then 1 else 0) * (if x j = v then 1 else 0))) = q i u * q j v := by
  let f : ι → β → ℝ := fun k b =>
    (if k = i then (if b = u then 1 else 0) else 1) *
    (if k = j then (if b = v then 1 else 0) else 1)
  have hp (x : ι → β) : (∏ k, f k (x k)) =
      (if x i = u then 1 else 0) * (if x j = v then 1 else 0) := by
    dsimp [f]
    rw [Finset.prod_mul_distrib]
    simp
  have hm (k : ι) : (∑ b, q k b * f k b) =
      (if k = i then q i u else 1) * (if k = j then q j v else 1) := by
    by_cases hi : k = i
    · subst k
      simp [f, hij, mul_ite]
    · by_cases hj : k = j
      · subst k
        simp [f, hi, mul_ite]
      · simp [f, hi, hj, hn]
  calc
    _ = ∑ x : ι → β, categoricalMass q x * ∏ k, f k (x k) := by simp_rw [hp]
    _ = ∏ k, ∑ b, q k b * f k b := categorical_factorization q f
    _ = ∏ k, ((if k = i then q i u else 1) * (if k = j then q j v else 1)) :=
      Finset.prod_congr rfl (fun k _ => hm k)
    _ = q i u * q j v := by rw [Finset.prod_mul_distrib]; simp

end Erdos1017
