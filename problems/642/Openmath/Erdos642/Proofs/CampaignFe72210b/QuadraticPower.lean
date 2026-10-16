import Openmath.Erdos642.Proofs.CampaignFe72210b.TiltedOperator
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-! Powers of actual finite positive matrices under a Euclidean quadratic bound. -/
namespace Erdos642.QuadraticPower

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The quadratic bound controls every eigenvalue; the norm is genuine finite ℓ². -/
theorem eigenvalue_bounds (A : Matrix V V ℝ) (hA : A.IsHermitian) (c : ℝ)
    (hpos : ∀ f : V → ℝ, 0 ≤ dotProduct f (A *ᵥ f))
    (hupper : ∀ f : V → ℝ, dotProduct f (A *ᵥ f) ≤ c * ∑ i, f i ^ 2)
    (i : V) : 0 ≤ hA.eigenvalues i ∧ hA.eigenvalues i ≤ c := by
  have he : dotProduct (⇑(hA.eigenvectorBasis i))
      (A *ᵥ ⇑(hA.eigenvectorBasis i)) = hA.eigenvalues i := by
    simpa using (hA.eigenvalues_eq i).symm
  have hn : (∑ j, (hA.eigenvectorBasis i) j ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, OrthonormalBasis.norm_eq_one]
    norm_num
  constructor
  · simpa only [he] using hpos (⇑(hA.eigenvectorBasis i))
  · simpa only [he, hn, mul_one] using hupper (⇑(hA.eigenvectorBasis i))

 theorem power_eigenvector (A : Matrix V V ℝ) (hA : A.IsHermitian) (n : ℕ) (i : V) :
    (A ^ n) *ᵥ ⇑(hA.eigenvectorBasis i) =
      (hA.eigenvalues i ^ n) • ⇑(hA.eigenvectorBasis i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hA.mulVec_eigenvectorBasis]
    simp [smul_smul, pow_succ, mul_comm]

/-- Exact spectral expansion of the actual matrix power quadratic form. -/
theorem power_quadratic_expansion (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (n : ℕ) (v : V → ℝ) :
    dotProduct v ((A ^ n) *ᵥ v) =
      ∑ i, hA.eigenvalues i ^ n *
        (inner ℝ (hA.eigenvectorBasis i) (WithLp.toLp 2 v)) ^ 2 := by
  let x : EuclideanSpace ℝ V := WithLp.toLp 2 v
  have hs : (A ^ n).toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.pow n)
  have hev (i : V) : (A ^ n).toEuclideanLin (hA.eigenvectorBasis i) =
      (hA.eigenvalues i ^ n) • hA.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    change ((A ^ n) *ᵥ ⇑(hA.eigenvectorBasis i)) j =
      hA.eigenvalues i ^ n * (hA.eigenvectorBasis i) j
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun (power_eigenvector A hA n i) j
  have hc (i : V) : inner ℝ (hA.eigenvectorBasis i) ((A ^ n).toEuclideanLin x) =
      hA.eigenvalues i ^ n * inner ℝ (hA.eigenvectorBasis i) x := by
    rw [← hs, hev, inner_smul_left]
    rfl
  calc
    dotProduct v ((A ^ n) *ᵥ v) = inner ℝ x ((A ^ n).toEuclideanLin x) := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
      change dotProduct v ((A ^ n) *ᵥ v) = dotProduct ((A ^ n) *ᵥ v) v
      exact dotProduct_comm _ _
    _ = ∑ i, inner ℝ x (hA.eigenvectorBasis i) *
        inner ℝ (hA.eigenvectorBasis i) ((A ^ n).toEuclideanLin x) :=
      (hA.eigenvectorBasis.sum_inner_mul_inner _ _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hc, real_inner_comm x]
      ring

/-- Actual matrix powers inherit the finite ℓ² quadratic bound, including `n = 0`. -/
theorem quadratic_power_bound (A : Matrix V V ℝ) (hA : A.IsHermitian) (c : ℝ)
    (_hc : 0 ≤ c) (hpos : ∀ f : V → ℝ, 0 ≤ dotProduct f (A *ᵥ f))
    (hupper : ∀ f : V → ℝ, dotProduct f (A *ᵥ f) ≤ c * ∑ i, f i ^ 2)
    (n : ℕ) (v : V → ℝ) :
    |dotProduct v ((A ^ n) *ᵥ v)| ≤ c ^ n * ∑ i, v i ^ 2 := by
  rw [power_quadratic_expansion A hA]
  have ht (i : V) :
      0 ≤ hA.eigenvalues i ^ n *
        (inner ℝ (hA.eigenvectorBasis i) (WithLp.toLp 2 v)) ^ 2 :=
    mul_nonneg (pow_nonneg (eigenvalue_bounds A hA c hpos hupper i).1 n) (sq_nonneg _)
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => ht i)]
  calc
    (∑ i, hA.eigenvalues i ^ n *
        (inner ℝ (hA.eigenvectorBasis i) (WithLp.toLp 2 v)) ^ 2) ≤
      ∑ i, c ^ n * (inner ℝ (hA.eigenvectorBasis i) (WithLp.toLp 2 v)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (eigenvalue_bounds A hA c hpos hupper i).1
            (eigenvalue_bounds A hA c hpos hupper i).2 n) (sq_nonneg _)
    _ = c ^ n * ∑ i, v i ^ 2 := by
      rw [← Finset.mul_sum, hA.eigenvectorBasis.sum_sq_inner_right,
        EuclideanSpace.real_norm_sq_eq]

/-- The literal diagonal matrix of the exponential coordinate tilt. -/
noncomputable def diagonalTilt (S : Finset V) (γ : ℝ) : Matrix V V ℝ :=
  Matrix.diagonal (fun i => if i ∈ S then Real.exp (-γ / 32) else 1)

noncomputable def tiltedMatrix (A : Matrix V V ℝ) (S : Finset V) (γ : ℝ) :
    Matrix V V ℝ := diagonalTilt S γ * A * diagonalTilt S γ

 theorem diagonalTilt_mulVec (S : Finset V) (γ : ℝ) (f : V → ℝ) :
    diagonalTilt S γ *ᵥ f = TiltedOperator.tilt S γ f := by
  ext i
  by_cases hi : i ∈ S <;> simp [diagonalTilt, TiltedOperator.tilt, Matrix.mulVec_diagonal, hi]

 theorem diagonalTilt_move (S : Finset V) (γ : ℝ) (f g : V → ℝ) :
    dotProduct f (diagonalTilt S γ *ᵥ g) =
      dotProduct (diagonalTilt S γ *ᵥ f) g := by
  simp only [diagonalTilt, Matrix.mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

 theorem tilted_quadratic_identity (A : Matrix V V ℝ) (S : Finset V) (γ : ℝ)
    (f : V → ℝ) :
    dotProduct f (tiltedMatrix A S γ *ᵥ f) =
      dotProduct (TiltedOperator.tilt S γ f) (A *ᵥ TiltedOperator.tilt S γ f) := by
  rw [tiltedMatrix, ← mulVec_mulVec, ← mulVec_mulVec, diagonalTilt_move,
    diagonalTilt_mulVec]

/-- Actual powers of the literal tilted matrix, from the original quadratic gap. -/
theorem tilted_matrix_power_bound (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (u : V → ℝ) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hu : (∑ i, u i ^ 2) = 1) (hAu : A *ᵥ u = u)
    (hpos : ∀ f : V → ℝ, 0 ≤ dotProduct f (A *ᵥ f))
    (hgap : ∀ h : V → ℝ, dotProduct h u = 0 →
      dotProduct h (A *ᵥ h) ≤ (1 - γ) * ∑ i, h i ^ 2)
    (S : Finset V) (n : ℕ) (v : V → ℝ) :
    |dotProduct v ((tiltedMatrix A S γ ^ n) *ᵥ v)| ≤
      (1 - 3 * γ * TiltedOperator.mass S u / 64) ^ n * ∑ i, v i ^ 2 := by
  have hD : (diagonalTilt S γ).IsHermitian := Matrix.isHermitian_diagonal _
  have hB : (tiltedMatrix A S γ).IsHermitian := by
    simpa only [hD.eq, tiltedMatrix] using Matrix.isHermitian_conjTranspose_mul_mul (diagonalTilt S γ) hA
  have hμ0 := TiltedOperator.mass_nonneg S u
  have hμ1 : TiltedOperator.mass S u ≤ 1 := by
    simpa only [TiltedOperator.sqNorm, hu] using TiltedOperator.mass_le_sqNorm S u
  have hprod : γ * TiltedOperator.mass S u ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hμ1 (le_of_lt hγ)
    nlinarith
  have hc : 0 ≤ 1 - 3 * γ * TiltedOperator.mass S u / 64 := by nlinarith
  have hBpos (f : V → ℝ) : 0 ≤ dotProduct f (tiltedMatrix A S γ *ᵥ f) := by
    rw [tilted_quadratic_identity]
    exact hpos _
  have hs : ∀ f g : V → ℝ, TiltedOperator.dot f (A.mulVecLin g) =
      TiltedOperator.dot (A.mulVecLin f) g := by
    intro f g
    have ht : A.transpose = A := by
      exact (Matrix.isHermitian_iff_isSymm.mp hA).eq
    simpa only [TiltedOperator.dot, dotProduct, Matrix.mulVecLin_apply, ht,
      mul_comm] using Matrix.dotProduct_transpose_mulVec A f g
  have hg : ∀ h : V → ℝ, TiltedOperator.dot h u = 0 →
      TiltedOperator.dot h (A.mulVecLin h) ≤ (1 - γ) * TiltedOperator.sqNorm h := by
    simpa only [TiltedOperator.dot, TiltedOperator.sqNorm, dotProduct,
      Matrix.mulVecLin_apply] using hgap
  have hupper (f : V → ℝ) : dotProduct f (tiltedMatrix A S γ *ᵥ f) ≤
      (1 - 3 * γ * TiltedOperator.mass S u / 64) * ∑ i, f i ^ 2 := by
    rw [tilted_quadratic_identity]
    simpa only [TiltedOperator.dot, TiltedOperator.sqNorm, dotProduct,
      Matrix.mulVecLin_apply] using
      TiltedOperator.rayleigh_contraction A.mulVecLin u γ hγ hγ1 hu hAu hs hg S f
  exact quadratic_power_bound (tiltedMatrix A S γ) hB _ hc hBpos hupper n v

end Erdos642.QuadraticPower
