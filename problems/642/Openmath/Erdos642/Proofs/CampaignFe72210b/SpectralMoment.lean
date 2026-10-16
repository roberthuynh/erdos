import Openmath.Erdos642.Proofs.CampaignFe72210b.ReversibleMoment
import Openmath.Erdos642.Proofs.CampaignFe72210b.QuadraticPower

/-! Actual finite-path exponential moment from a genuine normalized matrix gap. -/
open scoped Matrix
namespace Erdos642.FiniteMarkov.Chain
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (C : Erdos642.FiniteMarkov.Chain V)

noncomputable def setTilt (S : Finset V) (γ : ℝ) (x : V) : ℝ :=
  exponentialTilt (γ / 16) (fun y => if y ∈ S then 1 else 0) x

omit [Fintype V] in
theorem setTilt_apply (S : Finset V) (γ : ℝ) (x : V) :
    setTilt S γ x = if x ∈ S then Real.exp (-γ / 32) else 1 := by
  by_cases hx : x ∈ S
  · simp only [setTilt, exponentialTilt, hx, if_true, mul_one]
    congr 1
    ring
  · simp [setTilt, exponentialTilt, hx]

theorem similarTilt_setTilt (u : V → ℝ) (S : Finset V) (γ : ℝ) :
    C.similarTilt u (setTilt S γ) =
      Erdos642.QuadraticPower.tiltedMatrix (C.similarTransition u) S γ := by
  ext x y
  simp only [similarTilt, setTilt_apply, Erdos642.QuadraticPower.tiltedMatrix,
    Erdos642.QuadraticPower.diagonalTilt, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem setTilt_norm_le (u : V → ℝ) (S : Finset V) (γ : ℝ) (hγ : 0 ≤ γ)
    (hu : (∑ x, u x ^ 2) = 1) :
    (∑ x, (u x * setTilt S γ x) ^ 2) ≤ 1 := by
  rw [← hu]
  apply Finset.sum_le_sum
  intro x _
  have hd0 : 0 ≤ setTilt S γ x := by
    rw [setTilt_apply]
    split_ifs <;> positivity
  have hd1 : setTilt S γ x ≤ 1 := by
    rw [setTilt_apply]
    split_ifs
    · apply Real.exp_le_one_iff.mpr
      linarith
    · exact le_rfl
  have hdsq : setTilt S γ x ^ 2 ≤ 1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hdsq (sq_nonneg (u x))
  nlinarith

/-- Exponential moment for n transitions and n+1 actual observed positions. -/
theorem spectral_path_moment (u : V → ℝ) (huPos : ∀ x, 0 < u x)
    (hu : (∑ x, u x ^ 2) = 1)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hA : (C.similarTransition u).IsHermitian)
    (hAu : C.similarTransition u *ᵥ u = u)
    (hpos : ∀ f : V → ℝ, 0 ≤ dotProduct f (C.similarTransition u *ᵥ f))
    (hgap : ∀ h : V → ℝ, dotProduct h u = 0 →
      dotProduct h (C.similarTransition u *ᵥ h) ≤ (1 - γ) * ∑ x, h x ^ 2)
    (S : Finset V) (n : ℕ) :
    (∑ x, u x ^ 2 * ∑ p : Erdos642.FiniteMarkov.Path V n,
      C.weight x p * Real.exp (-(γ / 16) *
        vertexSum (fun y => if y ∈ S then 1 else 0) x p)) ≤
      (1 - 3 * γ * Erdos642.TiltedOperator.mass S u / 64) ^ n := by
  have heq := C.weighted_path_moment u (setTilt S γ)
    (fun x => ne_of_gt (huPos x)) n
  have hp (x : V) (p : Erdos642.FiniteMarkov.Path V n) :
      vertexProduct (setTilt S γ) x p = Real.exp (-(γ / 16) *
        vertexSum (fun y => if y ∈ S then 1 else 0) x p) :=
    vertexProduct_exponential (γ / 16) (fun y => if y ∈ S then 1 else 0) x p
  simp_rw [hp] at heq
  rw [heq, C.similarTilt_setTilt]
  have hb := Erdos642.QuadraticPower.tilted_matrix_power_bound
    (C.similarTransition u) hA u γ hγ hγ1 hu hAu hpos hgap S n
    (fun x => u x * setTilt S γ x)
  have hn := setTilt_norm_le u S γ (le_of_lt hγ) hu
  have hm0 := Erdos642.TiltedOperator.mass_nonneg S u
  have hm1 : Erdos642.TiltedOperator.mass S u ≤ 1 := by
    simpa only [Erdos642.TiltedOperator.sqNorm, hu] using
      Erdos642.TiltedOperator.mass_le_sqNorm S u
  have hc : 0 ≤ 1 - 3 * γ * Erdos642.TiltedOperator.mass S u / 64 := by
    have hh := mul_le_mul_of_nonneg_left hm1 (le_of_lt hγ)
    nlinarith
  calc
    _ ≤ |dotProduct (fun x => u x * setTilt S γ x)
      ((Erdos642.QuadraticPower.tiltedMatrix (C.similarTransition u) S γ ^ n) *ᵥ
        (fun x => u x * setTilt S γ x))| := le_abs_self _
    _ ≤ _ := hb
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_left hn (pow_nonneg hc n)

end Erdos642.FiniteMarkov.Chain
