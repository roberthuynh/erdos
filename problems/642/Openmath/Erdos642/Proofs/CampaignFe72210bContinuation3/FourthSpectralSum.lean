import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralSum
import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralEntries

/-! Genuine fourth-coordinate energies and actual finite spectral remainders. -/
namespace Erdos642.CampaignFe72210bContinuation3
open Erdos642.CampaignFe72210b
variable {ι : Type*}

theorem spectral_sum_fourth_step_bound (K : Finset ι) (lam a b : ι → ℝ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (t : ℕ) (ht : 4 ≤ t)
    (hgap : ∀ j ∈ K, |lam j| ≤ ρ) :
    |∑ j ∈ K, (lam j) ^ t * a j * b j| ≤
      ρ ^ (t - 4) * Real.sqrt (∑ j ∈ K, (lam j ^ 2 * a j) ^ 2) *
        Real.sqrt (∑ j ∈ K, (lam j ^ 2 * b j) ^ 2) := by
  classical
  have hterm (j : ι) (hj : j ∈ K) :
      |(lam j) ^ t * a j * b j| ≤
        ρ ^ (t - 4) * (|lam j ^ 2 * a j| * |lam j ^ 2 * b j|) := by
    calc
      |(lam j) ^ t * a j * b j| = |lam j| ^ t * |a j| * |b j| := by
        rw [abs_mul, abs_mul, abs_pow]
      _ = (|lam j| ^ (t - 4) * |lam j| ^ 4) * |a j| * |b j| := by
        rw [← pow_add, Nat.sub_add_cancel ht]
      _ = |lam j| ^ (t - 4) * (|lam j ^ 2 * a j| * |lam j ^ 2 * b j|) := by
        simp only [abs_mul, abs_pow]
        ring
      _ ≤ ρ ^ (t - 4) * (|lam j ^ 2 * a j| * |lam j ^ 2 * b j|) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _) (hgap j hj) _)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc
    |∑ j ∈ K, (lam j) ^ t * a j * b j| ≤
        ∑ j ∈ K, |(lam j) ^ t * a j * b j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ K, ρ ^ (t - 4) * (|lam j ^ 2 * a j| * |lam j ^ 2 * b j|) :=
      Finset.sum_le_sum hterm
    _ = ρ ^ (t - 4) * (∑ j ∈ K, |lam j ^ 2 * a j| * |lam j ^ 2 * b j|) := by
      rw [Finset.mul_sum]
    _ ≤ ρ ^ (t - 4) *
        (Real.sqrt (∑ j ∈ K, (lam j ^ 2 * a j) ^ 2) *
          Real.sqrt (∑ j ∈ K, (lam j ^ 2 * b j) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (sum_abs_mul_abs_le_sqrt_sum_sq K (fun j => lam j ^ 2 * a j)
          (fun j => lam j ^ 2 * b j)) (pow_nonneg hρ _)
    _ = ρ ^ (t - 4) * Real.sqrt (∑ j ∈ K, (lam j ^ 2 * a j) ^ 2) *
        Real.sqrt (∑ j ∈ K, (lam j ^ 2 * b j) ^ 2) := by ring

section Matrix
open Matrix
variable [Fintype ι] [DecidableEq ι]

/-- The actual fourth spectral coordinate energy equals the actual matrix diagonal. -/
theorem hermitian_eigenbasis_fourth_energy_eq_diagonal (B : Matrix ι ι ℝ)
    (hB : B.IsHermitian) (x : ι) :
    (∑ j, (hB.eigenvalues j ^ 2 * (hB.eigenvectorBasis j) x) ^ 2) = (B ^ 4) x x := by
  rw [hermitian_pow_entry B hB 4 x x]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hermitian_partial_spectral_sum_fourth_step_bound (B : Matrix ι ι ℝ)
    (hB : B.IsHermitian) (K : Finset ι) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (t : ℕ) (ht : 4 ≤ t) (hgap : ∀ j ∈ K, |hB.eigenvalues j| ≤ ρ)
    (x y : ι) :
    |∑ j ∈ K, (hB.eigenvalues j) ^ t *
        (hB.eigenvectorBasis j) x * (hB.eigenvectorBasis j) y| ≤
      ρ ^ (t - 4) * Real.sqrt ((B ^ 4) x x) * Real.sqrt ((B ^ 4) y y) := by
  classical
  have hx : (∑ j ∈ K, (hB.eigenvalues j ^ 2 * (hB.eigenvectorBasis j) x) ^ 2) ≤
      (B ^ 4) x x := by
    rw [← hermitian_eigenbasis_fourth_energy_eq_diagonal B hB x]
    exact Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
  have hy : (∑ j ∈ K, (hB.eigenvalues j ^ 2 * (hB.eigenvectorBasis j) y) ^ 2) ≤
      (B ^ 4) y y := by
    rw [← hermitian_eigenbasis_fourth_energy_eq_diagonal B hB y]
    exact Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
  calc
    |∑ j ∈ K, (hB.eigenvalues j) ^ t *
        (hB.eigenvectorBasis j) x * (hB.eigenvectorBasis j) y| ≤
        ρ ^ (t - 4) *
          Real.sqrt (∑ j ∈ K, (hB.eigenvalues j ^ 2 * (hB.eigenvectorBasis j) x) ^ 2) *
          Real.sqrt (∑ j ∈ K, (hB.eigenvalues j ^ 2 * (hB.eigenvectorBasis j) y) ^ 2) :=
      spectral_sum_fourth_step_bound K hB.eigenvalues
        (fun j => (hB.eigenvectorBasis j) x) (fun j => (hB.eigenvectorBasis j) y)
        ρ hρ t ht hgap
    _ ≤ ρ ^ (t - 4) * Real.sqrt ((B ^ 4) x x) * Real.sqrt ((B ^ 4) y y) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hx) (pow_nonneg hρ _))
        (Real.sqrt_le_sqrt hy) (Real.sqrt_nonneg _)
        (mul_nonneg (pow_nonneg hρ _) (Real.sqrt_nonneg _))

end Matrix
end Erdos642.CampaignFe72210bContinuation3
