import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralMoment
import Openmath.Erdos642.Proofs.CampaignFe72210b.OccupationTail

/-! Actual finite-chain occupation tails from original normalized spectral premises.
    No exponential-moment or concentration bound is assumed in these statements. -/
namespace Erdos642.FiniteMarkov.Chain

open Matrix Erdos642.OccupationTail

universe u
variable {V : Type u} [Fintype V]
variable (C : Erdos642.FiniteMarkov.Chain V)

/-- Hermitian similarity gives detailed balance for the actual squared weights. -/
theorem similarTransition_detailed_balance (u : V → ℝ) (huPos : ∀ x, 0 < u x)
    (hA : (C.similarTransition u).IsHermitian) (x y : V) :
    u x ^ 2 * C.transition x y = u y ^ 2 * C.transition y x := by
  have he := hA.apply y x
  simp only [star_trivial, similarTransition] at he
  field_simp [ne_of_gt (huPos x), ne_of_gt (huPos y)] at he
  nlinarith

/-- Thus the squared positive weights really are stationary for the given chain. -/
theorem similarTransition_stationary (u : V → ℝ) (huPos : ∀ x, 0 < u x)
    (hA : (C.similarTransition u).IsHermitian) (y : V) :
    (∑ x, u x ^ 2 * C.transition x y) = u y ^ 2 := by
  simp_rw [C.similarTransition_detailed_balance u huPos hA]
  rw [← Finset.mul_sum, C.row_sum, mul_one]

variable [DecidableEq V]

/-- Stationary finite-path occupation tail from the original positive quadratic gap.
    `n` counts observed vertices; the actual path has `n - 1` transitions. -/
theorem stationary_occupation_tail (u : V → ℝ) (huPos : ∀ x, 0 < u x)
    (hu : (∑ x, u x ^ 2) = 1)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hA : (C.similarTransition u).IsHermitian)
    (hAu : C.similarTransition u *ᵥ u = u)
    (hpos : ∀ f : V → ℝ, 0 ≤ dotProduct f (C.similarTransition u *ᵥ f))
    (hgap : ∀ h : V → ℝ, dotProduct h u = 0 →
      dotProduct h (C.similarTransition u *ᵥ h) ≤ (1 - γ) * ∑ x, h x ^ 2)
    (S : Finset V) (n : ℕ) (hn : 1 ≤ n) :
    (∑ x, u x ^ 2 * C.eventMass (n - 1)
      (fun x p => occupation S x p ≤ (n : ℝ) * Erdos642.TiltedOperator.mass S u / 2) x) ≤
      2 * Real.exp (-γ * Erdos642.TiltedOperator.mass S u * (n : ℝ) / 64) := by
  have hμ0 := Erdos642.TiltedOperator.mass_nonneg S u
  have hμ1 : Erdos642.TiltedOperator.mass S u ≤ 1 := by
    simpa only [Erdos642.TiltedOperator.sqNorm, hu] using
      Erdos642.TiltedOperator.mass_le_sqNorm S u
  apply mixture_occupation_tail_from_moment C S (fun x => u x ^ 2)
    (fun x => sq_nonneg (u x)) γ (Erdos642.TiltedOperator.mass S u)
    hγ hγ1 hμ0 hμ1 n hn
  simpa only [occupation] using
    C.spectral_path_moment u huPos hu γ hγ hγ1 hA hAu hpos hgap S (n - 1)

/-- An arbitrary fixed start, with its positive stationary mass retained on the left. -/
theorem point_mass_weighted_occupation_tail (u : V → ℝ) (huPos : ∀ x, 0 < u x)
    (hu : (∑ x, u x ^ 2) = 1)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hA : (C.similarTransition u).IsHermitian)
    (hAu : C.similarTransition u *ᵥ u = u)
    (hpos : ∀ f : V → ℝ, 0 ≤ dotProduct f (C.similarTransition u *ᵥ f))
    (hgap : ∀ h : V → ℝ, dotProduct h u = 0 →
      dotProduct h (C.similarTransition u *ᵥ h) ≤ (1 - γ) * ∑ y, h y ^ 2)
    (S : Finset V) (n : ℕ) (hn : 1 ≤ n) (x : V) :
    u x ^ 2 * C.eventMass (n - 1)
      (fun x p => occupation S x p ≤ (n : ℝ) * Erdos642.TiltedOperator.mass S u / 2) x ≤
      2 * Real.exp (-γ * Erdos642.TiltedOperator.mass S u * (n : ℝ) / 64) := by
  have hdom := C.start_domination (n - 1)
    (fun x p => occupation S x p ≤ (n : ℝ) * Erdos642.TiltedOperator.mass S u / 2)
    (fun x => u x ^ 2) (fun x => sq_nonneg (u x)) x
  exact hdom.trans (C.stationary_occupation_tail u huPos hu γ hγ hγ1 hA hAu hpos hgap S n hn)

/-- Full arbitrary-start occupation bound. The prefactor is the inverse actual
    stationary mass at the chosen starting vertex, not an assumed warm start. -/
theorem point_mass_occupation_tail (u : V → ℝ) (huPos : ∀ x, 0 < u x)
    (hu : (∑ x, u x ^ 2) = 1)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hA : (C.similarTransition u).IsHermitian)
    (hAu : C.similarTransition u *ᵥ u = u)
    (hpos : ∀ f : V → ℝ, 0 ≤ dotProduct f (C.similarTransition u *ᵥ f))
    (hgap : ∀ h : V → ℝ, dotProduct h u = 0 →
      dotProduct h (C.similarTransition u *ᵥ h) ≤ (1 - γ) * ∑ y, h y ^ 2)
    (S : Finset V) (n : ℕ) (hn : 1 ≤ n) (x : V) :
    C.eventMass (n - 1)
      (fun x p => occupation S x p ≤ (n : ℝ) * Erdos642.TiltedOperator.mass S u / 2) x ≤
      (2 / u x ^ 2) * Real.exp (-γ * Erdos642.TiltedOperator.mass S u * (n : ℝ) / 64) := by
  have hbound := C.point_mass_weighted_occupation_tail
    u huPos hu γ hγ hγ1 hA hAu hpos hgap S n hn x
  have hx : 0 < u x ^ 2 := sq_pos_of_pos (huPos x)
  have hdiv : C.eventMass (n - 1)
      (fun x p => occupation S x p ≤ (n : ℝ) * Erdos642.TiltedOperator.mass S u / 2) x ≤
      (2 * Real.exp (-γ * Erdos642.TiltedOperator.mass S u * (n : ℝ) / 64)) /
        u x ^ 2 := by
    apply (le_div_iff₀ hx).2
    simpa only [mul_comm] using hbound
  calc
    _ ≤ (2 * Real.exp (-γ * Erdos642.TiltedOperator.mass S u * (n : ℝ) / 64)) /
        u x ^ 2 := hdiv
    _ = _ := by ring

end Erdos642.FiniteMarkov.Chain
