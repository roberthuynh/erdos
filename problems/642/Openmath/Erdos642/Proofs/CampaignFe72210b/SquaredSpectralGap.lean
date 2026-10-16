import Openmath.Erdos642.Proofs.CampaignFe72210b.SimpleEigenprojector
import Openmath.Erdos642.Proofs.CampaignFe72210b.QuadraticPower

/-! Squared spectral gap after deriving both exceptional coefficient vanishings.
    The matrix is the actual Hermitian B, and the power is its actual square. -/
namespace Erdos642.CampaignFe72210b

open Matrix Submodule

variable {V : Type*} [Fintype V]

/-- Orthogonality to one nonzero unit vector removes its entire simple eigenspace. -/
theorem simple_eigenspace_inner_zero
    (T : Module.End ℝ (EuclideanSpace ℝ V)) (lam : ℝ)
    (w z f : EuclideanSpace ℝ V)
    (hsimple : Module.finrank ℝ (T.eigenspace lam) = 1)
    (hw : T w = lam • w) (hz : T z = lam • z)
    (hwunit : ‖w‖ = 1) (horth : inner ℝ w f = 0) :
    inner ℝ z f = 0 := by
  have hwne : w ≠ 0 := by
    intro he
    simp only [he, norm_zero] at hwunit
    norm_num at hwunit
  have hspan : T.eigenspace lam = ℝ ∙ w :=
    eq_span_singleton_of_mem_of_finrank_eq_one hsimple
      (Module.End.mem_eigenspace_iff.mpr hw) hwne
  have hzmem : z ∈ ℝ ∙ w := by
    rw [← hspan]
    exact Module.End.mem_eigenspace_iff.mpr hz
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hzmem
  rw [← ha, inner_smul_left, horth]
  simp

variable [DecidableEq V]

 theorem hermitian_canonical_eigen_equation (B : Matrix V V ℝ) (hB : B.IsHermitian)
    (j : V) : B.toEuclideanLin (hB.eigenvectorBasis j) =
      hB.eigenvalues j • hB.eigenvectorBasis j := by
  apply PiLp.ext
  intro x
  change (B *ᵥ ⇑(hB.eigenvectorBasis j)) x =
    hB.eigenvalues j * (hB.eigenvectorBasis j) x
  simpa only [Pi.smul_apply, smul_eq_mul] using congrFun (hB.mulVec_eigenvectorBasis j) x

 theorem hermitian_canonical_hasEigenvalue (B : Matrix V V ℝ) (hB : B.IsHermitian)
    (j : V) : Module.End.HasEigenvalue B.toEuclideanLin (hB.eigenvalues j) := by
  have he := hermitian_canonical_eigen_equation B hB j
  have hn : hB.eigenvectorBasis j ≠ 0 := by
    intro hz
    have hu := hB.eigenvectorBasis.orthonormal.norm_eq_one j
    simp only [hz, norm_zero] at hu
    norm_num at hu
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr he, hn⟩

/-- The generic two-exception squared gap, from actual eigenvectors and multiplicities. -/
theorem hermitian_squared_gap (B : Matrix V V ℝ) (hB : B.IsHermitian)
    (u v : V → ℝ) (hu : (∑ x, u x ^ 2) = 1) (hv : (∑ x, v x ^ 2) = 1)
    (hBu : B *ᵥ u = u) (hBv : B *ᵥ v = -v)
    (hsimplePlus : Module.finrank ℝ (Module.End.eigenspace B.toEuclideanLin 1) = 1)
    (hsimpleMinus : Module.finrank ℝ (Module.End.eigenspace B.toEuclideanLin (-1)) = 1)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hrest : ∀ lam : ℝ, Module.End.HasEigenvalue B.toEuclideanLin lam →
      lam ≠ 1 → lam ≠ -1 → |lam| ≤ ρ)
    (f : V → ℝ) (hfu : dotProduct f u = 0) (hfv : dotProduct f v = 0) :
    dotProduct f ((B ^ 2) *ᵥ f) ≤ ρ ^ 2 * ∑ x, f x ^ 2 := by
  let uE : EuclideanSpace ℝ V := WithLp.toLp 2 u
  let vE : EuclideanSpace ℝ V := WithLp.toLp 2 v
  let fE : EuclideanSpace ℝ V := WithLp.toLp 2 f
  have hunorm : ‖uE‖ = 1 := by
    have hs : ‖uE‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact hu
    nlinarith [norm_nonneg uE]
  have hvnorm : ‖vE‖ = 1 := by
    have hs : ‖vE‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact hv
    nlinarith [norm_nonneg vE]
  have huEigen : B.toEuclideanLin uE = (1 : ℝ) • uE := by
    apply PiLp.ext
    intro x
    change (B *ᵥ u) x = 1 * u x
    simpa only [one_mul] using congrFun hBu x
  have hvEigen : B.toEuclideanLin vE = (-1 : ℝ) • vE := by
    apply PiLp.ext
    intro x
    change (B *ᵥ v) x = -1 * v x
    simpa only [Pi.neg_apply, neg_one_mul] using congrFun hBv x
  have hou : inner ℝ uE fE = 0 := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    exact hfu
  have hov : inner ℝ vE fE = 0 := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    exact hfv
  have hplus (j : V) (hj : hB.eigenvalues j = 1) :
      inner ℝ (hB.eigenvectorBasis j) fE = 0 := by
    have he := hermitian_canonical_eigen_equation B hB j
    rw [hj] at he
    exact simple_eigenspace_inner_zero B.toEuclideanLin 1 uE
      (hB.eigenvectorBasis j) fE hsimplePlus huEigen he hunorm hou
  have hminus (j : V) (hj : hB.eigenvalues j = -1) :
      inner ℝ (hB.eigenvectorBasis j) fE = 0 := by
    have he := hermitian_canonical_eigen_equation B hB j
    rw [hj] at he
    exact simple_eigenspace_inner_zero B.toEuclideanLin (-1) vE
      (hB.eigenvectorBasis j) fE hsimpleMinus hvEigen he hvnorm hov
  rw [Erdos642.QuadraticPower.power_quadratic_expansion B hB 2]
  calc
    (∑ j, hB.eigenvalues j ^ 2 * (inner ℝ (hB.eigenvectorBasis j) fE) ^ 2) ≤
      ∑ j, ρ ^ 2 * (inner ℝ (hB.eigenvectorBasis j) fE) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hp : hB.eigenvalues j = 1
        · rw [hplus j hp]
          simp
        · by_cases hm : hB.eigenvalues j = -1
          · rw [hminus j hm]
            simp
          · have hl := hrest (hB.eigenvalues j)
              (hermitian_canonical_hasEigenvalue B hB j) hp hm
            have hsq : hB.eigenvalues j ^ 2 ≤ ρ ^ 2 := by
              have hh := (sq_le_sq₀ (abs_nonneg (hB.eigenvalues j)) hρ).2 hl
              simpa only [sq_abs] using hh
            exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = ρ ^ 2 * ∑ x, f x ^ 2 := by
      rw [← Finset.mul_sum, hB.eigenvectorBasis.sum_sq_inner_right,
        EuclideanSpace.real_norm_sq_eq]

end Erdos642.CampaignFe72210b
