import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-! Finite spectral-sum inequalities for the reviewed two-step heat-kernel argument.
These declarations do not assert a graph cycle theorem. -/

namespace Erdos642.CampaignFe72210b

variable {ι : Type*}

/-- Finite Cauchy-Schwarz with absolute coordinates and explicit square roots. -/
theorem sum_abs_mul_abs_le_sqrt_sum_sq (K : Finset ι) (a b : ι → ℝ) :
    (∑ j ∈ K, |a j| * |b j|) ≤
      Real.sqrt (∑ j ∈ K, (a j) ^ 2) * Real.sqrt (∑ j ∈ K, (b j) ^ 2) := by
  classical
  have ha : 0 ≤ ∑ j ∈ K, (a j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hb : 0 ≤ ∑ j ∈ K, (b j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hs : 0 ≤ ∑ j ∈ K, |a j| * |b j| :=
    Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hr : 0 ≤ Real.sqrt (∑ j ∈ K, (a j) ^ 2) *
      Real.sqrt (∑ j ∈ K, (b j) ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply (sq_le_sq₀ hs hr).mp
  calc
    (∑ j ∈ K, |a j| * |b j|) ^ 2 ≤
        (∑ j ∈ K, (a j) ^ 2) * (∑ j ∈ K, (b j) ^ 2) := by
      simpa only [sq_abs] using
        (Finset.sum_mul_sq_le_sq_mul_sq K (fun j => |a j|) (fun j => |b j|))
    _ = (Real.sqrt (∑ j ∈ K, (a j) ^ 2) *
        Real.sqrt (∑ j ∈ K, (b j) ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- Two powers of each eigenvalue remain inside the coordinate energies.
The inequality includes signed coordinates, empty sets, and `ρ = 0`, `t = 2`. -/
theorem spectral_sum_two_step_bound (K : Finset ι) (lam a b : ι → ℝ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (t : ℕ) (ht : 2 ≤ t)
    (hgap : ∀ j ∈ K, |lam j| ≤ ρ) :
    |∑ j ∈ K, (lam j) ^ t * a j * b j| ≤
      ρ ^ (t - 2) * Real.sqrt (∑ j ∈ K, (lam j * a j) ^ 2) *
        Real.sqrt (∑ j ∈ K, (lam j * b j) ^ 2) := by
  classical
  have hterm (j : ι) (hj : j ∈ K) :
      |(lam j) ^ t * a j * b j| ≤
        ρ ^ (t - 2) * (|lam j * a j| * |lam j * b j|) := by
    calc
      |(lam j) ^ t * a j * b j| = |lam j| ^ t * |a j| * |b j| := by
        rw [abs_mul, abs_mul, abs_pow]
      _ = (|lam j| ^ (t - 2) * |lam j| ^ 2) * |a j| * |b j| := by
        rw [← pow_add, Nat.sub_add_cancel ht]
      _ = |lam j| ^ (t - 2) * (|lam j * a j| * |lam j * b j|) := by
        simp only [abs_mul]
        ring
      _ ≤ ρ ^ (t - 2) * (|lam j * a j| * |lam j * b j|) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _) (hgap j hj) _)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc
    |∑ j ∈ K, (lam j) ^ t * a j * b j| ≤
        ∑ j ∈ K, |(lam j) ^ t * a j * b j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ K, ρ ^ (t - 2) * (|lam j * a j| * |lam j * b j|) :=
      Finset.sum_le_sum hterm
    _ = ρ ^ (t - 2) * (∑ j ∈ K, |lam j * a j| * |lam j * b j|) := by
      rw [Finset.mul_sum]
    _ ≤ ρ ^ (t - 2) *
        (Real.sqrt (∑ j ∈ K, (lam j * a j) ^ 2) *
          Real.sqrt (∑ j ∈ K, (lam j * b j) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (sum_abs_mul_abs_le_sqrt_sum_sq K (fun j => lam j * a j)
          (fun j => lam j * b j)) (pow_nonneg hρ _)
    _ = ρ ^ (t - 2) * Real.sqrt (∑ j ∈ K, (lam j * a j) ^ 2) *
        Real.sqrt (∑ j ∈ K, (lam j * b j) ^ 2) := by ring

section Matrix

open Matrix

variable [Fintype ι] [DecidableEq ι]

/-- The full two-step coordinate energy of a real Hermitian matrix is its
squared-matrix diagonal. This is the Parseval step in the heat-kernel bound. -/
theorem hermitian_eigenbasis_energy_eq_diagonal (B : Matrix ι ι ℝ)
    (hB : B.IsHermitian) (x : ι) :
    (∑ j, (hB.eigenvalues j * (hB.eigenvectorBasis j) x) ^ 2) = (B ^ 2) x x := by
  classical
  let e : EuclideanSpace ℝ ι := EuclideanSpace.single x 1
  have hs : B.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hev (j : ι) : B.toEuclideanLin (hB.eigenvectorBasis j) =
      hB.eigenvalues j • hB.eigenvectorBasis j := by
    apply PiLp.ext
    intro y
    change (B *ᵥ ⇑(hB.eigenvectorBasis j)) y =
      hB.eigenvalues j * (hB.eigenvectorBasis j) y
    simpa only [Pi.smul_apply, smul_eq_mul] using
      congrFun (hB.mulVec_eigenvectorBasis j) y
  have hc (j : ι) :
      inner ℝ (hB.eigenvectorBasis j) (B.toEuclideanLin e) =
        hB.eigenvalues j * (hB.eigenvectorBasis j) x := by
    rw [← hs, hev]
    simp [e, EuclideanSpace.inner_single_right]
  calc
    (∑ j, (hB.eigenvalues j * (hB.eigenvectorBasis j) x) ^ 2) =
        ∑ j, (inner ℝ (hB.eigenvectorBasis j) (B.toEuclideanLin e)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hc]
    _ = ‖B.toEuclideanLin e‖ ^ 2 :=
      hB.eigenvectorBasis.sum_sq_inner_right _
    _ = ∑ j, (B j x) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      change (B *ᵥ Pi.single x 1) j = B j x
      simp
    _ = (B ^ 2) x x := by
      rw [pow_two, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j _
      have hsym : B x j = B j x := by simpa using hB.apply j x
      rw [hsym]
      ring

/-- A partial spectral sum is smoothed by the actual two-step matrix diagonal.
The exceptional eigenspaces can be removed by choosing the finite set `K`. -/
theorem hermitian_partial_spectral_sum_two_step_bound (B : Matrix ι ι ℝ)
    (hB : B.IsHermitian) (K : Finset ι) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (t : ℕ) (ht : 2 ≤ t) (hgap : ∀ j ∈ K, |hB.eigenvalues j| ≤ ρ)
    (x y : ι) :
    |∑ j ∈ K, (hB.eigenvalues j) ^ t *
        (hB.eigenvectorBasis j) x * (hB.eigenvectorBasis j) y| ≤
      ρ ^ (t - 2) * Real.sqrt ((B ^ 2) x x) * Real.sqrt ((B ^ 2) y y) := by
  classical
  have hx : (∑ j ∈ K, (hB.eigenvalues j * (hB.eigenvectorBasis j) x) ^ 2) ≤
      (B ^ 2) x x := by
    rw [← hermitian_eigenbasis_energy_eq_diagonal B hB x]
    exact Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
  have hy : (∑ j ∈ K, (hB.eigenvalues j * (hB.eigenvectorBasis j) y) ^ 2) ≤
      (B ^ 2) y y := by
    rw [← hermitian_eigenbasis_energy_eq_diagonal B hB y]
    exact Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
  calc
    |∑ j ∈ K, (hB.eigenvalues j) ^ t *
        (hB.eigenvectorBasis j) x * (hB.eigenvectorBasis j) y| ≤
        ρ ^ (t - 2) *
          Real.sqrt (∑ j ∈ K, (hB.eigenvalues j * (hB.eigenvectorBasis j) x) ^ 2) *
          Real.sqrt (∑ j ∈ K, (hB.eigenvalues j * (hB.eigenvectorBasis j) y) ^ 2) :=
      spectral_sum_two_step_bound K hB.eigenvalues
        (fun j => (hB.eigenvectorBasis j) x) (fun j => (hB.eigenvectorBasis j) y)
        ρ hρ t ht hgap
    _ ≤ ρ ^ (t - 2) * Real.sqrt ((B ^ 2) x x) * Real.sqrt ((B ^ 2) y y) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hx) (pow_nonneg hρ _))
        (Real.sqrt_le_sqrt hy) (Real.sqrt_nonneg _)
        (mul_nonneg (pow_nonneg hρ _) (Real.sqrt_nonneg _))

end Matrix

end Erdos642.CampaignFe72210b
