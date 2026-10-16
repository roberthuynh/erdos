import Openmath.Erdos642.Proofs.CampaignFe72210b.SimpleEigenprojector

/-! Actual Hermitian matrix-power entries and the exact two trivial eigenspaces.
This file supplies algebraic decompositions, without any heat-kernel premise. -/

namespace Erdos642.CampaignFe72210b

open Matrix Unitary

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every power entry expands in the actual canonical Hermitian eigenbasis,
including power zero. -/
theorem hermitian_pow_entry (B : Matrix V V ℝ) (hB : B.IsHermitian)
    (n : ℕ) (x y : V) :
    (B ^ n) x y =
      ∑ j, (hB.eigenvalues j) ^ n *
        (hB.eigenvectorBasis j) x * (hB.eigenvectorBasis j) y := by
  classical
  calc
    (B ^ n) x y =
        ((hB.eigenvectorUnitary : Matrix V V ℝ) *
          diagonal (fun j => (hB.eigenvalues j) ^ n) *
          star (hB.eigenvectorUnitary : Matrix V V ℝ)) x y := by
      conv_lhs =>
        rw [hB.spectral_theorem, ← map_pow, conjStarAlgAut_apply, diagonal_pow]
      rfl
    _ = ∑ j, (hB.eigenvalues j) ^ n *
        (hB.eigenvectorBasis j) x * (hB.eigenvectorBasis j) y := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.mul_diagonal, Matrix.star_apply, star_trivial,
        Matrix.IsHermitian.eigenvectorUnitary_apply]
      ring

/-- Explicit unit eigenvectors identify the two simple exceptional terms.
The remaining sum is the actual canonical spectral remainder. -/
theorem hermitian_pow_entry_split_trivial (B : Matrix V V ℝ) (hB : B.IsHermitian)
    (wplus wminus : EuclideanSpace ℝ V)
    (hsimpleplus : Module.finrank ℝ (Module.End.eigenspace B.toEuclideanLin 1) = 1)
    (hsimpleminus : Module.finrank ℝ (Module.End.eigenspace B.toEuclideanLin (-1)) = 1)
    (hwplus : B.toEuclideanLin wplus = (1 : ℝ) • wplus)
    (hwminus : B.toEuclideanLin wminus = (-1 : ℝ) • wminus)
    (hunitplus : ‖wplus‖ = 1) (hunitminus : ‖wminus‖ = 1)
    (n : ℕ) (x y : V) :
    (B ^ n) x y =
      wplus x * wplus y + (-1 : ℝ) ^ n * wminus x * wminus y +
        ∑ j ∈ Finset.univ.filter
          (fun j => hB.eigenvalues j ≠ 1 ∧ hB.eigenvalues j ≠ -1),
          (hB.eigenvalues j) ^ n *
            (hB.eigenvectorBasis j) x * (hB.eigenvectorBasis j) y := by
  classical
  let F : V → ℝ := fun j => (hB.eigenvalues j) ^ n *
    (hB.eigenvectorBasis j) x * (hB.eigenvectorBasis j) y
  have hsplit : (∑ j, F j) =
      (∑ j ∈ Finset.univ.filter (fun j => hB.eigenvalues j = 1), F j) +
      (∑ j ∈ Finset.univ.filter (fun j => hB.eigenvalues j = -1), F j) +
      (∑ j ∈ Finset.univ.filter
        (fun j => hB.eigenvalues j ≠ 1 ∧ hB.eigenvalues j ≠ -1), F j) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hp : hB.eigenvalues j = 1
    · norm_num [hp]
    · by_cases hm : hB.eigenvalues j = -1 <;> norm_num [hp, hm]
  have hplus :
      (∑ j ∈ Finset.univ.filter (fun j => hB.eigenvalues j = 1), F j) =
        wplus x * wplus y := by
    calc
      _ = ∑ j ∈ Finset.univ.filter (fun j => hB.eigenvalues j = 1),
          (hB.eigenvectorBasis j) x * (hB.eigenvectorBasis j) y := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjval : hB.eigenvalues j = 1 := (Finset.mem_filter.mp hj).2
        simp [F, hjval]
      _ = wplus x * wplus y :=
        hermitian_simple_eigenprojector_sum B hB 1 wplus
          hsimpleplus hwplus hunitplus x y
  have hminus :
      (∑ j ∈ Finset.univ.filter (fun j => hB.eigenvalues j = -1), F j) =
        (-1 : ℝ) ^ n * (wminus x * wminus y) := by
    calc
      _ = (-1 : ℝ) ^ n *
          (∑ j ∈ Finset.univ.filter (fun j => hB.eigenvalues j = -1),
            (hB.eigenvectorBasis j) x * (hB.eigenvectorBasis j) y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjval : hB.eigenvalues j = -1 := (Finset.mem_filter.mp hj).2
        simp only [F, hjval]
        ring
      _ = (-1 : ℝ) ^ n * (wminus x * wminus y) := by
        rw [hermitian_simple_eigenprojector_sum B hB (-1) wminus
          hsimpleminus hwminus hunitminus x y]
  rw [hermitian_pow_entry]
  change (∑ j, F j) = _
  rw [hsplit, hplus, hminus]
  simp only [F]
  ring

end Erdos642.CampaignFe72210b
