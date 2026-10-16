import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-! Finite Euclidean quadratic contraction for an actual exponential coordinate tilt. -/
namespace Erdos642.TiltedOperator

variable {V : Type*} [Fintype V]

variable [DecidableEq V]

def dot (v w : V → ℝ) : ℝ := ∑ i, v i * w i
def sqNorm (v : V → ℝ) : ℝ := ∑ i, v i ^ 2
def mass (S : Finset V) (v : V → ℝ) : ℝ :=
  ∑ i, if i ∈ S then v i ^ 2 else 0

omit [DecidableEq V] in
@[simp] theorem dot_comm (v w : V → ℝ) : dot v w = dot w v := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq V] in
@[simp] theorem dot_self (v : V → ℝ) : dot v v = sqNorm v := by
  simp [dot, sqNorm, pow_two]

omit [DecidableEq V] in
@[simp] theorem dot_sub_left (v w z : V → ℝ) :
    dot (v - w) z = dot v z - dot w z := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq V] in
@[simp] theorem dot_sub_right (v w z : V → ℝ) :
    dot v (w - z) = dot v w - dot v z := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq V] in
@[simp] theorem dot_smul_left (a : ℝ) (v w : V → ℝ) :
    dot (a • v) w = a * dot v w := by
  simp [dot, mul_assoc, Finset.mul_sum]

omit [DecidableEq V] in
@[simp] theorem dot_smul_right (a : ℝ) (v w : V → ℝ) :
    dot v (a • w) = a * dot v w := by
  simpa only [dot_comm] using dot_smul_left a w v

omit [DecidableEq V] in
theorem sqNorm_nonneg (v : V → ℝ) : 0 ≤ sqNorm v := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (v i)

 theorem mass_nonneg (S : Finset V) (v : V → ℝ) : 0 ≤ mass S v := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> positivity

 theorem mass_le_sqNorm (S : Finset V) (v : V → ℝ) : mass S v ≤ sqNorm v := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

omit [DecidableEq V] in
theorem sqNorm_sub_smul (v u : V → ℝ) (a : ℝ) :
    sqNorm (v - a • u) = sqNorm v - 2 * a * dot v u + a ^ 2 * sqNorm u := by
  rw [← dot_self (v - a • u)]
  simp only [dot_sub_left, dot_sub_right, dot_smul_left, dot_smul_right]
  rw [dot_self, dot_self, dot_comm u v]
  ring

noncomputable def tilt (S : Finset V) (γ : ℝ) (f : V → ℝ) : V → ℝ :=
  fun i => if i ∈ S then Real.exp (-γ / 32) * f i else f i

 theorem exp_tilt_sq (γ : ℝ) : Real.exp (-γ / 32) ^ 2 = Real.exp (-γ / 16) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

 theorem exp_tilt_energy (γ : ℝ) :
    γ / 16 * Real.exp (-γ / 16) ≤ 1 - Real.exp (-γ / 16) := by
  have h := Real.add_one_le_exp (γ / 16)
  have he : Real.exp (γ / 16) * Real.exp (-γ / 16) = 1 := by
    rw [← Real.exp_add]
    have hz : γ / 16 + -γ / 16 = 0 := by ring
    rw [hz, Real.exp_zero]
  have hm := mul_le_mul_of_nonneg_right h (le_of_lt (Real.exp_pos (-γ / 16)))
  nlinarith

 theorem tilt_energy (S : Finset V) (γ : ℝ) (f : V → ℝ) :
    γ / 16 * mass S (tilt S γ f) ≤ sqNorm f - sqNorm (tilt S γ f) := by
  unfold sqNorm
  rw [← Finset.sum_sub_distrib]
  rw [mass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ S
  · simp only [tilt, hi, if_true, mul_pow, exp_tilt_sq]
    have h := mul_le_mul_of_nonneg_right (exp_tilt_energy γ) (sq_nonneg (f i))
    nlinarith
  · simp [tilt, hi]

 theorem tilt_norm_lower (S : Finset V) (γ : ℝ) (hγ : γ ≤ 1) (f : V → ℝ) :
    (15 / 16 : ℝ) * sqNorm f ≤ sqNorm (tilt S γ f) := by
  rw [sqNorm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ S
  · simp only [tilt, hi, if_true, mul_pow, exp_tilt_sq]
    have he := Real.add_one_le_exp (-γ / 16)
    have hex : (15 / 16 : ℝ) ≤ Real.exp (-γ / 16) := by linarith
    exact mul_le_mul_of_nonneg_right hex (sq_nonneg (f i))
  · simp only [tilt, hi, if_false]
    nlinarith [sq_nonneg (f i)]

omit [DecidableEq V] in
theorem quadratic_poincare (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) (u g : V → ℝ)
    (γ : ℝ) (hu : sqNorm u = 1) (hAu : A u = u)
    (hself : ∀ v w, dot v (A w) = dot (A v) w)
    (hgap : ∀ h, dot h u = 0 → dot h (A h) ≤ (1 - γ) * sqNorm h) :
    γ * sqNorm (g - dot g u • u) ≤ sqNorm g - dot g (A g) := by
  let a := dot g u
  have horth : dot (g - a • u) u = 0 := by simp [a, hu]
  have hnorm : sqNorm (g - a • u) = sqNorm g - a ^ 2 := by
    rw [sqNorm_sub_smul, hu]
    dsimp [a]
    ring
  have hcross : dot u (A g) = a := by
    rw [hself, hAu, dot_comm]
  have hquad : dot (g - a • u) (A (g - a • u)) = dot g (A g) - a ^ 2 := by
    simp only [map_sub, map_smul, dot_sub_left, dot_sub_right,
      dot_smul_left, dot_smul_right]
    rw [hAu, dot_self, hu, hcross]
    dsimp [a]
    ring
  have hg := hgap (g - a • u) horth
  rw [hquad, hnorm] at hg
  change γ * sqNorm (g - a • u) ≤ _
  rw [hnorm]
  nlinarith

 theorem young_mass (S : Finset V) (γ : ℝ) (hγ : 0 ≤ γ) (u g : V → ℝ) (a : ℝ) :
    (7 * γ / 128) * mass S u * a ^ 2 + (γ / 2) * sqNorm (g - a • u) ≤
      (γ / 16) * mass S g + γ * sqNorm (g - a • u) := by
  unfold mass sqNorm
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ S
  · simp only [hi, if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hs := mul_nonneg (show 0 ≤ γ / 2 by positivity)
      (sq_nonneg (a * u i / 8 + (g i - a * u i)))
    have hh := mul_nonneg hγ (sq_nonneg (g i - a * u i))
    nlinarith
  · simp only [hi, if_false, mul_zero, zero_mul, zero_add]
    have hh := mul_nonneg hγ (sq_nonneg ((g - a • u) i))
    nlinarith

/-- The actual exponential diagonal tilt contracts every Rayleigh quotient.
    This assumes only the finite quadratic gap, not a concentration or contraction theorem. -/
 theorem rayleigh_contraction (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) (u : V → ℝ)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hu : sqNorm u = 1) (hAu : A u = u)
    (hself : ∀ v w, dot v (A w) = dot (A v) w)
    (hgap : ∀ h, dot h u = 0 → dot h (A h) ≤ (1 - γ) * sqNorm h)
    (S : Finset V) (f : V → ℝ) :
    dot (tilt S γ f) (A (tilt S γ f)) ≤
      (1 - 3 * γ * mass S u / 64) * sqNorm f := by
  let g := tilt S γ f
  let a := dot g u
  let h := g - a • u
  let μ := mass S u
  have hμ0 : 0 ≤ μ := mass_nonneg S u
  have hμ1 : μ ≤ 1 := by simpa [μ, hu] using mass_le_sqNorm S u
  have hp := quadratic_poincare A u g γ hu hAu hself hgap
  have he := tilt_energy S γ f
  have hl := tilt_norm_lower S γ hγ1 f
  have hy := young_mass S γ (le_of_lt hγ) u g a
  have hn : sqNorm g = a ^ 2 + sqNorm h := by
    dsimp [h]
    rw [sqNorm_sub_smul, hu]
    dsimp [a]
    ring
  have hh0 : 0 ≤ sqNorm h := sqNorm_nonneg h
  have hf0 : 0 ≤ sqNorm f := sqNorm_nonneg f
  have hcoeff : (7 * γ / 128) * μ ≤ γ / 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoeff hh0
  have henergy : (7 * γ / 128) * μ * sqNorm g ≤ sqNorm f - dot g (A g) := by
    change γ * sqNorm h ≤ sqNorm g - dot g (A g) at hp
    change γ / 16 * mass S g ≤ sqNorm f - sqNorm g at he
    change (7 * γ / 128) * μ * a ^ 2 + (γ / 2) * sqNorm h ≤
      γ / 16 * mass S g + γ * sqNorm h at hy
    rw [hn]
    nlinarith
  have hc0 : 0 ≤ (7 * γ / 128) * μ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hl hc0
  change (15 / 16 : ℝ) * sqNorm f ≤ sqNorm g at hl
  have hfinal : (3 * γ * μ / 64) * sqNorm f ≤
      (7 * γ / 128) * μ * sqNorm g := by
    have hproduct := mul_nonneg (mul_nonneg (le_of_lt hγ) hμ0) hf0
    nlinarith
  change dot g (A g) ≤ (1 - 3 * γ * μ / 64) * sqNorm f
  nlinarith

/-- Positivity of the original quadratic form survives the diagonal tilt. -/
theorem tilt_quadratic_nonneg (A : (V → ℝ) →ₗ[ℝ] (V → ℝ))
    (hpos : ∀ v, 0 ≤ dot v (A v)) (S : Finset V) (γ : ℝ) (f : V → ℝ) :
    0 ≤ dot (tilt S γ f) (A (tilt S γ f)) := hpos _

end Erdos642.TiltedOperator
