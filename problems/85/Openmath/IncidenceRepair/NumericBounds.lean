import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Scalar endgame only. Geometry and embedding existence are separate obligations. -/
namespace Erdos85.IncidenceRepair

theorem sqrt_le_three_quarters {a : ℝ} (ha : 2 ≤ a) :
    Real.sqrt a ≤ 3 * a / 4 := by
  have ha0 : 0 ≤ a := by linarith
  have hs := Real.sq_sqrt ha0
  have hs0 := Real.sqrt_nonneg a
  have hprod : 0 ≤ a * (a - 2) := mul_nonneg ha0 (by linarith)
  nlinarith [sq_nonneg (Real.sqrt a - 3 * a / 4)]

theorem local_repair_bound {a d N D T : ℝ}
    (ha : 2 ≤ a) (hd : d ≤ 2 * a) (hN : 0 < N)
    (hD : 0 ≤ D) (hsmall : D ≤ N / 20)
    (hgap : (a - Real.sqrt a - d * D / (2 * N)) * D ≤ T) :
    D ≤ 5 * T / a := by
  have ha0 : 0 < a := by linarith
  have hs := sqrt_le_three_quarters ha
  have hden : 0 < 2 * N := by positivity
  have hprod : d * D ≤ a * N / 10 := by
    have h1 := mul_le_mul_of_nonneg_right hd hD
    have h2 := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2 * a by positivity)
    nlinarith
  have hfrac : d * D / (2 * N) ≤ a / 20 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hcoef : a / 5 ≤ a - Real.sqrt a - d * D / (2 * N) := by linarith
  have := mul_le_mul_of_nonneg_right hcoef hD
  apply (le_div_iff₀ ha0).2
  nlinarith

theorem degree_repair_bound {a d T D : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hda : d ≤ 2 * a)
    (hT : 0 ≤ T) (hbound : D ≤ 5 * T / a) :
    D ≤ 10 * T / d := by
  apply hbound.trans
  apply (div_le_div_iff₀ ha hd).2
  nlinarith

theorem coarse_paired_bound {a d q lam B I Z T D : ℝ}
    (ha : 2 ≤ a) (hq : 2 ≤ q) (hd : d ≤ 2 * a)
    (hB : 0 ≤ B) (hZ : 0 ≤ Z) (hT : 0 ≤ T)
    (hlam : lam ≤ a - 1)
    (haffine : (a - a / q) * B ≤ T + d * Z)
    (hinfinity : (a - 1) * I ≤ T + lam * B)
    (hD : D = Z + B + I) : D ≤ 9 * Z + 6 * T / a := by
  have ha0 : 0 < a := by linarith
  have hq0 : 0 < q := by linarith
  have ham : 0 < a - 1 := by linarith
  have hhalf : a / q ≤ a / 2 := by
    apply (div_le_div_iff₀ hq0 (by norm_num : (0:ℝ)<2)).2
    nlinarith
  have hBbound : a * B ≤ 2 * T + 4 * a * Z := by
    have h1 := mul_le_mul_of_nonneg_right hhalf hB
    have h2 := mul_le_mul_of_nonneg_right hd hZ
    nlinarith
  have hIbound : (a - 1) * I ≤ T + (a - 1) * B := by
    have := mul_le_mul_of_nonneg_right hlam hB
    linarith
  have hI : I ≤ B + 2 * T / a := by
    have htdiv : T / (a - 1) ≤ 2 * T / a := by
      apply (div_le_div_iff₀ ham ha0).2
      nlinarith
    have hi : I ≤ B + T / (a - 1) := by
      have hi : I - B ≤ T / (a - 1) := (le_div_iff₀ ham).2 (by nlinarith)
      linarith
    linarith
  have hB' : B ≤ 2 * T / a + 4 * Z := by
    have hb : B - 4 * Z ≤ 2 * T / a := (le_div_iff₀ ha0).2 (by nlinarith)
    linarith
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem coarse_proximity {N D Z T a delta : ℝ}
    (hN : 0 < N) (hZ : Z ≤ 971 / 10000000 * N)
    (hT : T / a ≤ 2 * delta * N)
    (hdelta : delta ≤ 1 / 4000000000)
    (hD : D ≤ 9 * Z + 6 * T / a) : D < N / 1000 := by
  have h1 := mul_le_mul_of_nonneg_right hdelta (le_of_lt hN)
  simp only [div_eq_mul_inv] at *
  nlinarith

/-- Complete scalar endgame from the explicit geometric inequalities (7.1),
(7.2), (6.4) and (8.2). This is not the embedding-existence theorem. -/
theorem numeric_endgame {a d q lam B I Z T D N delta : ℝ}
    (ha : 2 ≤ a) (hq : 2 ≤ q) (hd : 0 < d) (hda : d ≤ 2 * a)
    (hN : 0 < N) (hB : 0 ≤ B) (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hD0 : 0 ≤ D)
    (hlam : lam ≤ a - 1)
    (haffine : (a - a / q) * B ≤ T + d * Z)
    (hinfinity : (a - 1) * I ≤ T + lam * B)
    (hD : D = Z + B + I)
    (hZsmall : Z ≤ 971 / 10000000 * N)
    (hTsmall : T / a ≤ 2 * delta * N)
    (hdelta : delta ≤ 1 / 4000000000)
    (hgap : (a - Real.sqrt a - d * D / (2 * N)) * D ≤ T) :
    D ≤ 5 * T / a ∧ 5 * T / a ≤ 10 * T / d := by
  have hc := coarse_paired_bound ha hq hda hB hZ hT hlam haffine hinfinity hD
  have hp := coarse_proximity hN hZsmall hTsmall hdelta hc
  have hsmall : D ≤ N / 20 := by linarith
  exact ⟨local_repair_bound ha hda hN hD0 hsmall hgap,
    degree_repair_bound (by linarith) hd hda hT le_rfl⟩

end Erdos85.IncidenceRepair
