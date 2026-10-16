import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentSelfAvoidance
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.CoordinateGrid
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Actual natural family coefficients absorbed under genuine moment-host scalar
conditions. The floor alphabet and natural level ceiling are not replaced by a net. -/
namespace Erdos642.CampaignFe72210bContinuation3.MomentOccupationAbsorption
open MomentSAParameters
open scoped BigOperators

noncomputable def mu0 : ℝ := 1 / (10 : ℝ)^15

theorem mu0_pos : 0 < mu0 := by norm_num [mu0]

/-- Literal host constants, not a supplied large-constant assumption. -/
theorem aA_large : (10 : ℝ)^40 ≤ a * A := by
  have hA : (10 : ℝ)^250 ≤ A :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) (by norm_num : (250 : ℕ) ≤ 1000)
  have ha : (10 : ℝ)^40 ≤ a * (10 : ℝ)^250 := by norm_num [a, beta]
  exact ha.trans (mul_le_mul_of_nonneg_left hA a_pos.le)

private theorem log_ten_le_three : Real.log (10 : ℝ) ≤ 3 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 10)).mpr
  have hb : (5 / 2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  calc
    (10 : ℝ) ≤ (5 / 2 : ℝ)^3 := by norm_num
    _ ≤ (Real.exp 1)^3 := by gcongr
    _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num

private theorem coefficient_exp_le (C R B : ℝ) (hC : 0 < C)
    (hlog : Real.log C ≤ R - B) : C * Real.exp (-R) ≤ Real.exp (-B) := by
  calc
    _ = Real.exp (Real.log C - R) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hC]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hlog])

theorem fast_rate (t n r : ℕ) (ell μ : ℝ) (hell : 0 < ell)
    (hr : 1 ≤ r) (hrcap : (r : ℝ) ≤ 100 * ell)
    (hn : (t : ℝ) / 3 ≤ n) (hμ : mu0 ≤ μ) :
    (t : ℝ) / ((10 : ℝ)^35 * ell) ≤ μ^2 * n / (256 * r) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hμpos : 0 < μ := mu0_pos.trans_le hμ
  have hsq : mu0^2 ≤ μ^2 := (sq_le_sq₀ mu0_pos.le hμpos.le).mpr hμ
  have hc : (76800 : ℝ) ≤ μ^2 * (10 : ℝ)^35 := by
    have hh := mul_le_mul_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ (10 : ℝ)^35)
    norm_num [mu0] at hh
    linarith only [hh]
  apply (div_le_div_iff₀ (by positivity : 0 < (10 : ℝ)^35 * ell)
    (by positivity : 0 < 256 * (r : ℝ))).mpr
  calc
    (t : ℝ) * (256 * r) ≤ (3 * n) * (256 * (100 * ell)) := by
      gcongr
      · linarith only [hn]
    _ = 76800 * ((n : ℝ) * ell) := by ring
    _ ≤ (μ^2 * (10 : ℝ)^35) * ((n : ℝ) * ell) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (μ^2 * n) * ((10 : ℝ)^35 * ell) := by ring

theorem fast_budget (N k t m : ℕ) (ell d : ℝ)
    (hell : 1 < ell) (hk : ell ≤ k)
    (hdegree : A * k * ell ≤ d) (horder : A * (k : ℝ)^2 * ell ≤ N)
    (ht : a * N / (32 * k) ≤ (t : ℝ)) (hm : (m : ℝ) ≤ (N : ℝ) / d) :
    (m : ℝ) ≤ ((t : ℝ) / ((10 : ℝ)^35 * ell)) / 4 ∧
      8 * ell ≤ (t : ℝ) / ((10 : ℝ)^35 * ell) := by
  have hellpos : 0 < ell := by linarith
  have hkpos : (0 : ℝ) < k := hellpos.trans_le hk
  have hd : 0 < d := (mul_pos (mul_pos A_pos hkpos) hellpos).trans_le hdegree
  have ht' : a * N ≤ (t : ℝ) * (32 * k) := (div_le_iff₀ (by positivity)).mp ht
  have hm' : (m : ℝ) * d ≤ N := (le_div_iff₀ hd).mp hm
  have hc : (256 : ℝ) * (10 : ℝ)^35 ≤ a * A := by
    exact (by norm_num : (256 : ℝ) * (10 : ℝ)^35 ≤ (10 : ℝ)^40).trans aA_large
  constructor
  · have hprod : (32 * (k : ℝ)) * (4 * (10 : ℝ)^35 * ell * m) ≤ (32 * k) * t := by
      calc
        _ = (128 * (10 : ℝ)^35) * ((m : ℝ) * k * ell) := by ring
        _ ≤ (a * A) * ((m : ℝ) * k * ell) :=
          mul_le_mul_of_nonneg_right (by linarith only [hc]) (by positivity)
        _ = a * ((m : ℝ) * (A * k * ell)) := by ring
        _ ≤ a * ((m : ℝ) * d) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdegree (Nat.cast_nonneg m)) a_pos.le
        _ ≤ a * N := mul_le_mul_of_nonneg_left hm' a_pos.le
        _ ≤ _ := by simpa only [mul_comm] using ht'
    have hcancel := le_of_mul_le_mul_left hprod (by positivity : 0 < 32 * (k : ℝ))
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    apply (le_div_iff₀ (by positivity : 0 < (10 : ℝ)^35 * ell)).mpr
    nlinarith only [hcancel]
  · have hprod : (32 * (k : ℝ)) * ((8 * ell) * ((10 : ℝ)^35 * ell)) ≤
        (32 * k) * t := by
      calc
        _ = (256 * (10 : ℝ)^35) * ((k : ℝ) * ell * ell) := by ring
        _ ≤ (256 * (10 : ℝ)^35) * ((k : ℝ) * k * ell) := by gcongr
        _ = (256 * (10 : ℝ)^35) * ((k : ℝ)^2 * ell) := by ring
        _ ≤ (a * A) * ((k : ℝ)^2 * ell) := mul_le_mul_of_nonneg_right hc (by positivity)
        _ = a * (A * (k : ℝ)^2 * ell) := by ring
        _ ≤ a * N := mul_le_mul_of_nonneg_left horder a_pos.le
        _ ≤ _ := by simpa only [mul_comm] using ht'
    have hcancel := le_of_mul_le_mul_left hprod (by positivity : 0 < 32 * (k : ℝ))
    exact (le_div_iff₀ (by positivity : 0 < (10 : ℝ)^35 * ell)).mpr hcancel

/-- Actual natural forest-family fast term, with no assumed entropy budget. -/
theorem fast_family_absorbed (N k t n r qF m : ℕ) (d μ : ℝ)
    (hN : 3 ≤ N) (hell : 1 < Real.log (N : ℝ)) (hk : Real.log (N : ℝ) ≤ k)
    (hdegree : A * k * Real.log (N : ℝ) ≤ d)
    (horder : A * (k : ℝ)^2 * Real.log (N : ℝ) ≤ N)
    (ht : a * N / (32 * k) ≤ (t : ℝ)) (hn : (t : ℝ) / 3 ≤ n)
    (hr : 1 ≤ r) (hrcap : (r : ℝ) ≤ 100 * Real.log (N : ℝ))
    (hμ : mu0 ≤ μ) (hμcap : μ ≤ 1 / 50)
    (hq : qF ≤ N) (hm : (m : ℝ) ≤ (N : ℝ) / d) :
    (qF : ℝ) * (2 : ℝ)^m * (1 + μ / 16) * Real.exp (-μ^2 * n / (256 * r)) ≤
      Real.exp (-(t : ℝ) / (2 * (10 : ℝ)^35 * Real.log (N : ℝ))) := by
  have hμpos : 0 < μ := mu0_pos.trans_le hμ
  have hF := fast_budget N k t m (Real.log N) d hell hk hdegree horder ht hm
  have hrate := fast_rate t n r (Real.log N) μ (by linarith) hr hrcap hn hμ
  by_cases hq0 : qF = 0
  · simp only [hq0, Nat.cast_zero, zero_mul]
    exact (Real.exp_pos _).le
  · have hqpos : (0 : ℝ) < qF := by exact_mod_cast (Nat.pos_of_ne_zero hq0)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    let F := (t : ℝ) / ((10 : ℝ)^35 * Real.log (N : ℝ))
    let C := (2 * (qF : ℝ)) * (2 : ℝ)^m
    have hC : 0 < C := by dsimp [C]; positivity
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh ⊢
      exact hh
    have hlogq : Real.log (2 * (qF : ℝ)) ≤ 2 * Real.log (N : ℝ) := by
      calc
        _ ≤ Real.log (2 * (N : ℝ)) := Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left (by exact_mod_cast hq) (by norm_num))
        _ = Real.log 2 + Real.log (N : ℝ) := Real.log_mul (by norm_num) (ne_of_gt hNpos)
        _ ≤ _ := by linarith only [hlog2, hell]
    have hlogC : Real.log C ≤ F / 2 := by
      dsimp [C]
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have hmLog := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
      dsimp [F]
      nlinarith only [hlogq, hmLog, hF.1, hF.2]
    let R := μ^2 * n / (256 * r)
    change F ≤ R at hrate
    have hbound : C * Real.exp (-R) ≤ Real.exp (-(F / 2)) :=
      coefficient_exp_le C R (F / 2) hC (by linarith only [hlogC, hrate])
    calc
      _ = ((qF : ℝ) * (2 : ℝ)^m * Real.exp (-R)) * (1 + μ / 16) := by dsimp [R]; simp only [neg_mul, neg_div]; ring
      _ ≤ ((qF : ℝ) * (2 : ℝ)^m * Real.exp (-R)) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith only [hμcap] : 1 + μ / 16 ≤ 2) (by positivity)
      _ = C * Real.exp (-R) := by dsimp [C]; ring
      _ ≤ Real.exp (-(F / 2)) := hbound
      _ = _ := by congr 1; dsimp [F]; field_simp

/-- The literal floor alphabet has a logarithmic cost; no covering bound is assumed. -/
theorem alphabet_log_bound (N : ℕ) (μ : ℝ) (hN : 3 ≤ N)
    (hell : 1 < Real.log (N : ℝ)) (hμ : mu0 ≤ μ) (hμcap : μ ≤ 1 / 50) :
    0 < (CoordinateGrid.alphabet N μ : ℝ) ∧
      Real.log (CoordinateGrid.alphabet N μ : ℝ) ≤ 100 * Real.log (N : ℝ) := by
  have hμpos : 0 < μ := mu0_pos.trans_le hμ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hapos : 0 < (CoordinateGrid.alphabet N μ : ℝ) := by
    exact_mod_cast (show 0 < CoordinateGrid.alphabet N μ by unfold CoordinateGrid.alphabet; omega)
  have hab := (CoordinateGrid.alphabet_bound (show 1 ≤ N by omega) hμpos (by linarith : μ ≤ 1))
  have hup : (CoordinateGrid.alphabet N μ : ℝ) ≤ (10 : ℝ)^20 * N := by
    calc
      _ ≤ 24000 * (N : ℝ) / μ := hab.1.trans hab.2
      _ ≤ 24000 * (N : ℝ) / mu0 :=
        div_le_div_of_nonneg_left (by positivity) mu0_pos hμ
      _ ≤ _ := by norm_num [mu0]; nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  refine ⟨hapos, ?_⟩
  have hl := Real.log_le_log hapos hup
  rw [Real.log_mul (by positivity) (ne_of_gt hNpos), Real.log_pow] at hl
  have ht := log_ten_le_three
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl, ht, hell]

noncomputable def levelCount (μ : ℝ) : ℕ := ⌈2048 / μ⌉₊

/-- The genuine natural ceiling retains the extra endpoint in its bound. -/
theorem levelCount_log_bound (μ ell : ℝ) (hell : 1 < ell)
    (hμ : mu0 ≤ μ) (hμcap : μ ≤ 1 / 50) :
    0 < (levelCount μ : ℝ) ∧ Real.log (levelCount μ : ℝ) ≤ 57 * ell := by
  have hμpos : 0 < μ := mu0_pos.trans_le hμ
  have hJ : 1 ≤ levelCount μ := Nat.one_le_ceil_iff.mpr (by positivity)
  have hJpos : 0 < (levelCount μ : ℝ) := by exact_mod_cast (show 0 < levelCount μ by omega)
  have hceil : (levelCount μ : ℝ) ≤ 2048 / μ + 1 :=
    (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2048 / μ)).le
  have hstep : 2048 / μ + 1 ≤ 2049 / μ := by
    apply (le_div_iff₀ hμpos).mpr
    have hcancel := div_mul_cancel₀ (2048 : ℝ) (ne_of_gt hμpos)
    nlinarith only [hcancel, hμcap]
  have hup : (levelCount μ : ℝ) ≤ (10 : ℝ)^19 := by
    calc
      _ ≤ 2049 / μ := hceil.trans hstep
      _ ≤ 2049 / mu0 := div_le_div_of_nonneg_left (by norm_num) mu0_pos hμ
      _ ≤ _ := by norm_num [mu0]
  refine ⟨hJpos, ?_⟩
  have hl := Real.log_le_log hJpos hup
  rw [Real.log_pow] at hl
  have ht := log_ten_le_three
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl, ht, hell]

/-- Full actual coordinate-alphabet and level-count coefficient, including 100N. -/
theorem slow_coefficient_log (N D : ℕ) (μ Λ d : ℝ)
    (hN : 3 ≤ N) (hell : 1 < Real.log (N : ℝ))
    (hμ : mu0 ≤ μ) (hμcap : μ ≤ 1 / 50) (hD : 1 ≤ D)
    (hrank : (D : ℝ) ≤ 16 * Λ * N / d^2) :
    0 < (CoordinateGrid.alphabet N μ : ℝ)^D * levelCount μ * (100 * N) ∧
    Real.log ((CoordinateGrid.alphabet N μ : ℝ)^D * levelCount μ * (100 * N)) ≤
      4800 * Λ * N * Real.log (N : ℝ) / d^2 := by
  have ha := alphabet_log_bound N μ hN hell hμ hμcap
  have hJ := levelCount_log_bound μ (Real.log N) hell hμ hμcap
  have hapos := ha.1
  have hJpos := hJ.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hNlog : Real.log (100 * (N : ℝ)) ≤ 100 * Real.log (N : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 100)
    linarith only [hh, hell]
  refine ⟨by positivity, ?_⟩
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (ne_of_gt hJ.1), Real.log_pow]
  have hlog : (D : ℝ) * Real.log (CoordinateGrid.alphabet N μ : ℝ) +
      Real.log (levelCount μ : ℝ) + Real.log (100 * (N : ℝ)) ≤
      300 * D * Real.log (N : ℝ) := by
    have hdlog := mul_le_mul_of_nonneg_left ha.2 (Nat.cast_nonneg D)
    have hellpos : 0 < Real.log (N : ℝ) := by linarith only [hell]
    have hDscale := mul_le_mul_of_nonneg_right hDreal hellpos.le
    nlinarith only [hdlog, hJ.2, hNlog, hDscale, hellpos]
  calc
    _ ≤ 300 * D * Real.log (N : ℝ) := hlog
    _ ≤ 4800 * Λ * N * Real.log (N : ℝ) / d^2 := by
      have hh := mul_le_mul_of_nonneg_right hrank (by positivity : 0 ≤ 300 * Real.log (N : ℝ))
      calc
        _ = (D : ℝ) * (300 * Real.log (N : ℝ)) := by ring
        _ ≤ (16 * Λ * N / d^2) * (300 * Real.log (N : ℝ)) := hh
        _ = _ := by ring

theorem slow_rate (t n : ℕ) (γ μ : ℝ) (hγ : 0 < γ)
    (hn : (t : ℝ) / 3 ≤ n) (hμ : mu0 ≤ μ) :
    γ * t / (10 : ℝ)^21 ≤ γ * μ * n / 65536 := by
  have hμpos : 0 < μ := mu0_pos.trans_le hμ
  have hc : (196608 : ℝ) ≤ μ * (10 : ℝ)^21 := by
    have hh := mul_le_mul_of_nonneg_right hμ (by norm_num : (0 : ℝ) ≤ (10 : ℝ)^21)
    norm_num [mu0] at hh
    linarith only [hh]
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < (10 : ℝ)^21)
    (by norm_num : (0 : ℝ) < 65536)).mpr
  calc
    (γ * t) * 65536 ≤ (γ * (3 * n)) * 65536 := by gcongr; linarith only [hn]
    _ = 196608 * (γ * n) := by ring
    _ ≤ (μ * (10 : ℝ)^21) * (γ * n) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (γ * μ * n) * (10 : ℝ)^21 := by ring

/-- Strong actual moment criterion pays all alphabet/level/initial-law cost. -/
theorem slow_budget (N k t : ℕ) (ell d γ Λ : ℝ) (hell : 0 < ell)
    (hk : 0 < k) (hd : 0 < d) (hγ : 0 < γ) (hΛ : 0 ≤ Λ)
    (hmoment : A * Λ * k * ell ≤ d^2 * γ)
    (ht : a * N / (32 * k) ≤ (t : ℝ)) :
    4800 * Λ * N * ell / d^2 ≤ γ * t / (2 * (10 : ℝ)^21) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have ht' : a * N ≤ (t : ℝ) * (32 * k) := (div_le_iff₀ (by positivity)).mp ht
  have hc : (307200 : ℝ) * (10 : ℝ)^21 ≤ a * A :=
    (by norm_num : (307200 : ℝ) * (10 : ℝ)^21 ≤ (10 : ℝ)^40).trans aA_large
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) (by positivity : 0 < 2 * (10 : ℝ)^21)).mpr
  have hprod : (32 * (k : ℝ)) * ((4800 * Λ * N * ell) * (2 * (10 : ℝ)^21)) ≤
      (32 * k) * ((γ * t) * d^2) := by
    calc
      _ = (307200 * (10 : ℝ)^21) * ((Λ * k * ell) * N) := by ring
      _ ≤ (a * A) * ((Λ * k * ell) * N) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (a * (A * Λ * k * ell)) * N := by ring
      _ ≤ (a * (d^2 * γ)) * N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmoment a_pos.le) (Nat.cast_nonneg N)
      _ = (a * N) * (d^2 * γ) := by ring
      _ ≤ ((t : ℝ) * (32 * k)) * (d^2 * γ) :=
        mul_le_mul_of_nonneg_right ht' (by positivity)
      _ = _ := by ring
  exact le_of_mul_le_mul_left hprod (by positivity : 0 < 32 * (k : ℝ))

/-- Literal natural alphabet and ceiling slow term, with no assumed absorbed bound. -/
theorem slow_family_absorbed (N k t n D : ℕ) (d γ Λ μ : ℝ)
    (hN : 3 ≤ N) (hell : 1 < Real.log (N : ℝ)) (hk : Real.log (N : ℝ) ≤ k)
    (hdegree : A * k * Real.log (N : ℝ) ≤ d)
    (hγ : 0 < γ) (hmoment : A * Λ * k * Real.log (N : ℝ) ≤ d^2 * γ)
    (ht : a * N / (32 * k) ≤ (t : ℝ)) (hn : (t : ℝ) / 3 ≤ n)
    (hμ : mu0 ≤ μ) (hμcap : μ ≤ 1 / 50) (hD : 1 ≤ D)
    (hrank : (D : ℝ) ≤ 16 * Λ * N / d^2) :
    (CoordinateGrid.alphabet N μ : ℝ)^D * (⌈2048 / μ⌉₊ : ℝ) * 100 * N *
        Real.exp (-γ * μ * n / 65536) ≤
      Real.exp (-γ * t / (2 * (10 : ℝ)^21)) := by
  have hellpos : 0 < Real.log (N : ℝ) := by linarith only [hell]
  have hkpos : (0 : ℝ) < k := hellpos.trans_le hk
  have hkNat : 0 < k := by exact_mod_cast hkpos
  have hd : 0 < d := (mul_pos (mul_pos A_pos hkpos) hellpos).trans_le hdegree
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hΛ : 0 ≤ Λ := by
    have hpos : 0 < 16 * Λ * N / d^2 := lt_of_lt_of_le (by linarith : (0 : ℝ) < D) hrank
    have hnum := (div_pos_iff_of_pos_right (sq_pos_of_pos hd)).mp hpos
    by_contra hbad
    have hneg : Λ < 0 := lt_of_not_ge hbad
    have hnonpos : 16 * Λ * N ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hneg.le) hNpos.le
    linarith only [hnum, hnonpos]
  have hcoeff := slow_coefficient_log N D μ Λ d hN hell hμ hμcap hD hrank
  have hbudget := slow_budget N k t (Real.log N) d γ Λ hellpos hkNat hd hγ hΛ hmoment ht
  have hrate := slow_rate t n γ μ hγ hn hμ
  let C := (CoordinateGrid.alphabet N μ : ℝ)^D * levelCount μ * (100 * N)
  let R := γ * μ * n / 65536
  let S := γ * t / (10 : ℝ)^21
  have hlog : Real.log C ≤ S / 2 := by
    dsimp [C, S]
    calc
      _ ≤ 4800 * Λ * N * Real.log (N : ℝ) / d^2 := hcoeff.2
      _ ≤ γ * t / (2 * (10 : ℝ)^21) := hbudget
      _ = _ := by ring
  have hSR : S ≤ R := hrate
  have hbound : C * Real.exp (-R) ≤ Real.exp (-(S / 2)) :=
    coefficient_exp_le C R (S / 2) hcoeff.1 (by linarith only [hlog, hSR])
  calc
    _ = C * Real.exp (-R) := by dsimp [C, R, levelCount]; simp only [neg_mul, neg_div]; ring
    _ ≤ Real.exp (-(S / 2)) := hbound
    _ = _ := by congr 1; dsimp [S]; ring

end Erdos642.CampaignFe72210bContinuation3.MomentOccupationAbsorption
