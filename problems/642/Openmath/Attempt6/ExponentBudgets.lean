import Mathlib

/-!
Numerical and asymptotic budgets for the written Attempt6 exponent-6001 candidate.
These declarations prove only inequalities of real numbers. They do not assert
any graph extraction, reservoir, absorption, concentration, or cycle theorem.
-/

namespace Erdos585.Attempt6

open Filter

/-- The exact exponent calculations in ORIGINAL-BOUND.md, including the pool
size and block-size gaps. The core exponent is 6000; the arbitrary-graph
reduction spends one additional logarithmic power. -/
theorem exponent6000_exact :
    (6000 : ℚ) * (1 / 30 - 9 / 5000) = 946 / 5 ∧
    (6000 : ℚ) * (1 / 30 - 17 / 5000) = 898 / 5 ∧
    (6000 : ℚ) * (4991 / 5000) = 29946 / 5 ∧
    (6000 : ℚ) * (1 / 5000) = 6 / 5 ∧
    (6000 : ℚ) * ((4999 / 5000) / 8) = 14997 / 20 ∧
    (6000 : ℚ) * (7 / 10 - (2 / 3) * (4999 / 5000)) = 1004 / 5 ∧
    (6000 : ℚ) * ((1 / 3) * (4999 / 5000) - 1 / 30) = 8998 / 5 ∧
    (6001 : ℕ) = 6000 + 1 := by
  norm_num

/-- Strict rational gaps needed to dominate arbitrary fixed coefficients. -/
theorem exponent6000_strict :
    (82 : ℚ) < 6000 * (1 / 30 - 9 / 5000) ∧
    (158 : ℚ) < 6000 * (1 / 30 - 17 / 5000) ∧
    (83 : ℚ) < 6000 * (4991 / 5000) ∧
    (76 : ℚ) < 6000 * (1 / 30 - 9 / 5000) ∧
    (1 : ℚ) < 6000 * (1 / 5000) ∧
    (12 : ℚ) < 6000 * ((4999 / 5000) / 8) ∧
    (15 : ℚ) < 6000 * (4999 / 5000) ∧
    (77 : ℚ) < 6000 * (251 / 7500) ∧
    (6 : ℚ) < 6000 * (4499 / 15000) := by
  norm_num

/-- All explicit source-exponent thresholds in SOURCE-EXPONENT.md are below
1000. This verifies their arithmetic, not the probabilistic supplier proofs. -/
theorem sourceE1000_strict :
    (10 / 9 : ℚ) < 1000 ∧
    (160 / 3 : ℚ) < 1000 ∧
    (1 : ℚ) < 1000 ∧
    (10 / 3 : ℚ) < 1000 ∧
    (2 : ℚ) < 1000 ∧
    (5 / 3 : ℚ) < 1000 := by
  norm_num

/-- The core lower-degree hypothesis implies the audited source hypothesis
whenever the logarithmic parameter is at least one. -/
theorem core_implies_source_degree {L d : ℝ} (hL : 1 ≤ L)
    (hd : L ^ (6000 : ℝ) ≤ d) : L ^ (1000 : ℝ) ≤ d :=
  (Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1000 : ℝ) ≤ 6000)).trans hd

/-- The arithmetic of spending one logarithmic power in the extraction bound.
The supplier inequality itself is an explicit numerical hypothesis here. -/
theorem reduction_degree_budget {L D d : ℝ} (hL : 0 < L)
    (hD : 400 * L ^ (6001 : ℕ) ≤ D) (hd : D / (400 * L) ≤ d) :
    L ^ (6000 : ℕ) ≤ d := by
  apply le_trans _ hd
  apply (le_div_iff₀ (by positivity : 0 < (400 : ℝ) * L)).mpr
  calc
    L ^ (6000 : ℕ) * (400 * L) = 400 * L ^ (6001 : ℕ) := by
      rw [pow_succ]
      ring
    _ ≤ D := hD

/-- The order bound used for the additive joining term follows from `0 < d ≤ N`.
It is a real inequality, with no assumptions about a graph. -/
theorem joining_order_lower_bound {N d : ℝ} (hd : 0 < d) (hdN : d ≤ N) :
    N ^ ((29 : ℝ) / 30) ≤ N * d ^ (-((1 : ℝ) / 30)) := by
  have hN : 0 < N := hd.trans_le hdN
  have hpow := Real.rpow_le_rpow_of_nonpos hd hdN
    (by norm_num : -((1 : ℝ) / 30) ≤ 0)
  calc
    N ^ ((29 : ℝ) / 30) = N ^ ((1 : ℝ) + -((1 : ℝ) / 30)) := by norm_num
    _ = N * N ^ (-((1 : ℝ) / 30)) := by
      rw [Real.rpow_add hN, Real.rpow_one]
    _ ≤ N * d ^ (-((1 : ℝ) / 30)) := mul_le_mul_of_nonneg_left hpow hN.le

/-- A strict power gap pays any fixed real coefficient, uniformly over all
degrees above the hypothesized power lower bound. No budget is assumed. -/
theorem eventually_coefficient_budget {E p q : ℝ} (hp : 0 ≤ p)
    (hgap : q < E * p) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ d : ℝ, L ^ E ≤ d → C * L ^ q ≤ d ^ p := by
  have hgrow : Tendsto (fun L : ℝ => L ^ (E * p - q)) atTop atTop :=
    tendsto_rpow_atTop (sub_pos.mpr hgap)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hgrow.eventually (eventually_ge_atTop C)] with L hL hC
  intro d hd
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  calc
    C * L ^ q ≤ L ^ (E * p - q) * L ^ q :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hLpos.le q)
    _ = L ^ (E * p) := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    _ = (L ^ E) ^ p := Real.rpow_mul hLpos.le E p
    _ ≤ d ^ p := Real.rpow_le_rpow (Real.rpow_nonneg hLpos.le E) hd hp

/-- Simultaneous eventual budgets for the core exponent 6000. A single arbitrary
coefficient can bound all finitely many fixed coefficients occurring in the
written calculation. Quantification over `d` is uniform, not a hidden assumption
that the desired inequalities already hold. -/
theorem exponent6000_eventual (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ d : ℝ, L ^ (6000 : ℝ) ≤ d →
      C * L ^ (82 : ℝ) ≤ d ^ ((1 : ℝ) / 30 - 9 / 5000) ∧
      C * L ^ (158 : ℝ) ≤ d ^ ((1 : ℝ) / 30 - 17 / 5000) ∧
      C * L ^ (83 : ℝ) ≤ d ^ ((4991 : ℝ) / 5000) ∧
      C * L ^ (76 : ℝ) ≤ d ^ ((1 : ℝ) / 30 - 9 / 5000) ∧
      C * L ^ (1 : ℝ) ≤ d ^ ((1 : ℝ) / 5000) ∧
      C * L ^ (12 : ℝ) ≤ d ^ (((4999 : ℝ) / 5000) / 8) ∧
      C * L ^ (15 : ℝ) ≤ d ^ ((4999 : ℝ) / 5000) ∧
      C * L ^ (77 : ℝ) ≤ d ^ ((251 : ℝ) / 7500) ∧
      C * L ^ (6 : ℝ) ≤ d ^ ((4499 : ℝ) / 15000) := by
  have h1 := eventually_coefficient_budget
    (E := 6000) (p := (1 : ℝ) / 30 - 9 / 5000) (q := 82)
    (by norm_num) (by norm_num) C
  have h2 := eventually_coefficient_budget
    (E := 6000) (p := (1 : ℝ) / 30 - 17 / 5000) (q := 158)
    (by norm_num) (by norm_num) C
  have h3 := eventually_coefficient_budget
    (E := 6000) (p := (4991 : ℝ) / 5000) (q := 83)
    (by norm_num) (by norm_num) C
  have h4 := eventually_coefficient_budget
    (E := 6000) (p := (1 : ℝ) / 30 - 9 / 5000) (q := 76)
    (by norm_num) (by norm_num) C
  have h5 := eventually_coefficient_budget
    (E := 6000) (p := (1 : ℝ) / 5000) (q := 1)
    (by norm_num) (by norm_num) C
  have h6 := eventually_coefficient_budget
    (E := 6000) (p := ((4999 : ℝ) / 5000) / 8) (q := 12)
    (by norm_num) (by norm_num) C
  have h7 := eventually_coefficient_budget
    (E := 6000) (p := (4999 : ℝ) / 5000) (q := 15)
    (by norm_num) (by norm_num) C
  have h8 := eventually_coefficient_budget
    (E := 6000) (p := (251 : ℝ) / 7500) (q := 77)
    (by norm_num) (by norm_num) C
  have h9 := eventually_coefficient_budget
    (E := 6000) (p := (4499 : ℝ) / 15000) (q := 6)
    (by norm_num) (by norm_num) C
  filter_upwards [h1, h2, h3, h4, h5, h6, h7, h8, h9] with L h1 h2 h3 h4 h5 h6 h7 h8 h9
  intro d hd
  exact ⟨h1 d hd, h2 d hd, h3 d hd, h4 d hd, h5 d hd,
    h6 d hd, h7 d hd, h8 d hd, h9 d hd⟩

/-- Eventual real inequalities corresponding to the explicit source constraints.
The first condition supplies terminal neighbors and the ambient union bound;
the remaining conditions pay robustness, categorical errors, expectation errors,
upper-expectation errors, upper-probability corrections, and concentration. -/
theorem sourceE1000_eventual (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ d : ℝ, L ^ (1000 : ℝ) ≤ d →
      C * L ^ (1 : ℝ) ≤ d ^ ((9 : ℝ) / 10) ∧
      C * L ^ (32 : ℝ) ≤ d ^ ((3 : ℝ) / 5) ∧
      C * L ^ (1 : ℝ) ≤ d ^ (1 : ℝ) ∧
      C * L ^ (2 : ℝ) ≤ d ^ ((3 : ℝ) / 5) ∧
      C * L ^ (1 : ℝ) ≤ d ^ ((1 : ℝ) / 2) ∧
      C * L ^ (1 : ℝ) ≤ d ^ ((3 : ℝ) / 5) ∧
      C * L ^ (1 : ℝ) ≤ d ^ ((3 : ℝ) / 10) := by
  have h1 := eventually_coefficient_budget
    (E := 1000) (p := (9 : ℝ) / 10) (q := 1)
    (by norm_num) (by norm_num) C
  have h2 := eventually_coefficient_budget
    (E := 1000) (p := (3 : ℝ) / 5) (q := 32)
    (by norm_num) (by norm_num) C
  have h3 := eventually_coefficient_budget
    (E := 1000) (p := 1) (q := 1)
    (by norm_num) (by norm_num) C
  have h4 := eventually_coefficient_budget
    (E := 1000) (p := (3 : ℝ) / 5) (q := 2)
    (by norm_num) (by norm_num) C
  have h5 := eventually_coefficient_budget
    (E := 1000) (p := (1 : ℝ) / 2) (q := 1)
    (by norm_num) (by norm_num) C
  have h6 := eventually_coefficient_budget
    (E := 1000) (p := (3 : ℝ) / 5) (q := 1)
    (by norm_num) (by norm_num) C
  have h7 := eventually_coefficient_budget
    (E := 1000) (p := (3 : ℝ) / 10) (q := 1)
    (by norm_num) (by norm_num) C
  filter_upwards [h1, h2, h3, h4, h5, h6, h7] with L h1 h2 h3 h4 h5 h6 h7
  intro d hd
  exact ⟨h1 d hd, h2 d hd, h3 d hd, h4 d hd, h5 d hd, h6 d hd, h7 d hd⟩

/-- The additive joining term is negligible compared with `N^(29/30)`, with
the exact base-two logarithm from the written argument and an arbitrary fixed
coefficient. -/
theorem eventually_logb_joining_budget (C : ℝ) :
    ∀ᶠ N : ℝ in atTop, C * (Real.logb 2 N) ^ (6 : ℕ) ≤ N ^ ((29 : ℝ) / 30) := by
  by_cases hC : 0 < C
  · have ha : 0 < (Real.log 2) ^ (6 : ℕ) := pow_pos (Real.log_pos (by norm_num)) _
    have hsmall := (isLittleO_log_rpow_rpow_atTop
      (6 : ℝ) (s := (29 : ℝ) / 30) (by norm_num)).def (div_pos ha hC)
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with N hsmall hN
    have hNpow : 0 ≤ N ^ ((29 : ℝ) / 30) :=
      Real.rpow_nonneg (by linarith) _
    have hsmall' : (Real.log N) ^ (6 : ℕ) ≤
        ((Real.log 2) ^ (6 : ℕ) / C) * N ^ ((29 : ℝ) / 30) := by
      calc
        (Real.log N) ^ (6 : ℕ) ≤ |(Real.log N) ^ (6 : ℕ)| := le_abs_self _
        _ ≤ ((Real.log 2) ^ (6 : ℕ) / C) * N ^ ((29 : ℝ) / 30) := by
          simpa only [Real.rpow_ofNat, Real.norm_eq_abs, abs_of_nonneg hNpow] using hsmall
    calc
      C * (Real.logb 2 N) ^ (6 : ℕ) =
          (C / (Real.log 2) ^ (6 : ℕ)) * (Real.log N) ^ (6 : ℕ) := by
        simp only [Real.logb, div_pow]
        ring
      _ ≤ (C / (Real.log 2) ^ (6 : ℕ)) *
          (((Real.log 2) ^ (6 : ℕ) / C) * N ^ ((29 : ℝ) / 30)) :=
        mul_le_mul_of_nonneg_left hsmall' (div_pos hC ha).le
      _ = N ^ ((29 : ℝ) / 30) := by
        field_simp
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hC) (by positivity))
      (Real.rpow_nonneg hN _)

end Erdos585.Attempt6
