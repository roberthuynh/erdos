import Openmath.Attempt6.ExponentBudgets

/-! Numerical budgets for the density-power-eight routing candidate.
These declarations do not prove any routing, concentration or graph theorem. -/

namespace Erdos585.Attempt6

open Filter

/-- Exact rational power values for the core exponent 2940. -/
theorem exponent2940_exact :
    (2940 : ℚ) * (1 / 2930) = 294 / 293 ∧
    (2940 : ℚ) * (433 / 7350 - 8 / 2930) = 241978 / 1465 ∧
    (2940 : ℚ) * (433 / 7350 - 15 / 2930) = 231688 / 1465 ∧
    (2940 : ℚ) * (1 - 8 / 2930) = 859068 / 293 ∧
    (2940 : ℚ) * (1 / 2 - 8 * (433 / 7350) + (1 / 2930) / 2) = 124381 / 1465 ∧
    (2940 : ℚ) * ((1 - 1 / 2930) / 2 - 433 / 7350) = 1899077 / 1465 ∧
    (2940 : ℚ) * (1 - 1 / 2930) = 861126 / 293 ∧
    (2941 : ℕ) = 2940 + 1 := by
  norm_num

/-- All specified strict margins and source/density constraints. -/
theorem exponent2940_strict :
    (1 : ℚ) < 2940 * (1 / 2930) ∧
    (82 : ℚ) < 2940 * (433 / 7350 - 8 / 2930) ∧
    (76 : ℚ) < 2940 * (433 / 7350 - 8 / 2930) ∧
    (158 : ℚ) < 2940 * (433 / 7350 - 15 / 2930) ∧
    (83 : ℚ) < 2940 * (1 - 8 / 2930) ∧
    ((167 / 2) : ℚ) < 2940 * (1 / 2 - 8 * (433 / 7350) + (1 / 2930) / 2) ∧
    ((25 / 2) : ℚ) < 2940 * ((1 - 1 / 2930) / 2 - 433 / 7350) ∧
    (13 : ℚ) < 2940 * (1 - 1 / 2930) ∧
    (0 : ℚ) < 433 / 7350 ∧
    (433 / 7350 : ℚ) < 1 / 10 ∧
    (0 : ℚ) < 1 / 2930 ∧
    (1 / 2930 : ℚ) < 1 / 10 ∧
    (1000 : ℚ) ≤ 2940 := by
  norm_num

/-- The localized routing coefficient clears the displayed constant. -/
theorem localized_routing_constant :
    (1 / 10000 : ℚ) ≤ (2 / 3 : ℚ) ^ (8 : ℕ) / 96 := by
  norm_num

/-- Arbitrary fixed coefficients are paid uniformly over all d above L^2940. -/
theorem exponent2940_eventual (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ d : ℝ, L ^ (2940 : ℝ) ≤ d →
      C * L ^ (1 : ℝ) ≤ d ^ ((1 / 2930) : ℝ) ∧
      C * L ^ (82 : ℝ) ≤ d ^ ((433 / 7350 - 8 / 2930) : ℝ) ∧
      C * L ^ (76 : ℝ) ≤ d ^ ((433 / 7350 - 8 / 2930) : ℝ) ∧
      C * L ^ (158 : ℝ) ≤ d ^ ((433 / 7350 - 15 / 2930) : ℝ) ∧
      C * L ^ (83 : ℝ) ≤ d ^ ((1 - 8 / 2930) : ℝ) ∧
      C * L ^ ((167 / 2) : ℝ) ≤ d ^ ((1 / 2 - 8 * (433 / 7350) + (1 / 2930) / 2) : ℝ) ∧
      C * L ^ ((25 / 2) : ℝ) ≤ d ^ (((1 - 1 / 2930) / 2 - 433 / 7350) : ℝ) ∧
      C * L ^ (13 : ℝ) ≤ d ^ ((1 - 1 / 2930) : ℝ) := by
  have h1 := eventually_coefficient_budget
    (E := 2940) (p := ((1 / 2930) : ℝ)) (q := (1 : ℝ))
    (by norm_num) (by norm_num) C
  have h2 := eventually_coefficient_budget
    (E := 2940) (p := ((433 / 7350 - 8 / 2930) : ℝ)) (q := (82 : ℝ))
    (by norm_num) (by norm_num) C
  have h3 := eventually_coefficient_budget
    (E := 2940) (p := ((433 / 7350 - 8 / 2930) : ℝ)) (q := (76 : ℝ))
    (by norm_num) (by norm_num) C
  have h4 := eventually_coefficient_budget
    (E := 2940) (p := ((433 / 7350 - 15 / 2930) : ℝ)) (q := (158 : ℝ))
    (by norm_num) (by norm_num) C
  have h5 := eventually_coefficient_budget
    (E := 2940) (p := ((1 - 8 / 2930) : ℝ)) (q := (83 : ℝ))
    (by norm_num) (by norm_num) C
  have h6 := eventually_coefficient_budget
    (E := 2940) (p := ((1 / 2 - 8 * (433 / 7350) + (1 / 2930) / 2) : ℝ)) (q := ((167 / 2) : ℝ))
    (by norm_num) (by norm_num) C
  have h7 := eventually_coefficient_budget
    (E := 2940) (p := (((1 - 1 / 2930) / 2 - 433 / 7350) : ℝ)) (q := ((25 / 2) : ℝ))
    (by norm_num) (by norm_num) C
  have h8 := eventually_coefficient_budget
    (E := 2940) (p := ((1 - 1 / 2930) : ℝ)) (q := (13 : ℝ))
    (by norm_num) (by norm_num) C
  filter_upwards [h1, h2, h3, h4, h5, h6, h7, h8] with L h1 h2 h3 h4 h5 h6 h7 h8
  intro d hd
  exact ⟨h1 d hd, h2 d hd, h3 d hd, h4 d hd, h5 d hd, h6 d hd, h7 d hd, h8 d hd⟩

/-- The core degree assumption implies the audited source exponent. -/
theorem exponent2940_implies_source {L d : ℝ} (hL : 1 ≤ L)
    (hd : L ^ (2940 : ℝ) ≤ d) : L ^ (1000 : ℝ) ≤ d :=
  (Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1000 : ℝ) ≤ 2940)).trans hd

/-- Arithmetic of the one-logarithm extraction cost. -/
theorem exponent2941_reduction {L D d : ℝ} (hL : 0 < L)
    (hD : 400 * L ^ (2941 : ℕ) ≤ D) (hd : D / (400 * L) ≤ d) :
    L ^ (2940 : ℕ) ≤ d := by
  apply le_trans _ hd
  apply (le_div_iff₀ (by positivity : 0 < (400 : ℝ) * L)).mpr
  calc
    L ^ (2940 : ℕ) * (400 * L) = 400 * L ^ (2941 : ℕ) := by
      rw [pow_succ]
      ring
    _ ≤ D := hD

end Erdos585.Attempt6
