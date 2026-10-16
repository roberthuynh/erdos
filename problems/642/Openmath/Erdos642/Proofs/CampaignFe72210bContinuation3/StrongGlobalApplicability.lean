import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.OldGlobalApplicability

/-! Uniform payment of the strong moment-host scalar criteria.

The actual-host P8 inequality is an input; polynomial host order is derived.
No extraction theorem, actual return bound, or desired host criterion is assumed.
-/
namespace Erdos642.CampaignFe72210bContinuation3.StrongGlobalApplicability

def Q : ℝ := 2 * 32 ^ 8

def hostConstant : ℝ := 10 ^ 1000

theorem Q_pos : 0 < Q := by norm_num [Q]

/-- A universal quarter-root certificate, rather than an assumed tail estimate. -/
theorem log_eighth_quarter_certificate (x : ℝ) (hx : 1 ≤ x) :
    ∃ u : ℝ, 0 < u ∧ u ^ 4 = x ∧ (Real.log (2 * x)) ^ 8 ≤ Q * u := by
  let r : ℝ := (2 * x) ^ ((32 : ℝ)⁻¹)
  let u : ℝ := x ^ ((4 : ℝ)⁻¹)
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have h2x : 0 < 2 * x := by positivity
  have hr : 0 < r := Real.rpow_pos_of_pos h2x _
  have hu : 0 < u := Real.rpow_pos_of_pos hxpos _
  have hu4 : u ^ 4 = x :=
    Real.rpow_inv_natCast_pow hxpos.le (by norm_num : (4 : ℕ) ≠ 0)
  have hlogr : Real.log r = (32 : ℝ)⁻¹ * Real.log (2 * x) :=
    Real.log_rpow h2x _
  have hlog := Real.log_le_sub_one_of_pos hr
  have hupper : Real.log (2 * x) ≤ 32 * r := by norm_num at hlogr; linarith
  have heighth := pow_le_pow_left₀
    (Real.log_nonneg (show (1 : ℝ) ≤ 2 * x by linarith)) hupper 8
  have hr8 : r ^ 8 = (2 * x) ^ ((4 : ℝ)⁻¹) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2x.le]
    norm_num
  have htwo4 : ((2 : ℝ) ^ ((4 : ℝ)⁻¹)) ^ 4 = 2 :=
    Real.rpow_inv_natCast_pow (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
  have htwo : (2 : ℝ) ^ ((4 : ℝ)⁻¹) ≤ 2 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by norm_num)
    rw [htwo4]
    norm_num
  have hr8prod : r ^ 8 = (2 : ℝ) ^ ((4 : ℝ)⁻¹) * u := by
    rw [hr8, Real.mul_rpow (by norm_num) hxpos.le]
  refine ⟨u, hu, hu4, ?_⟩
  calc
    (Real.log (2 * x)) ^ 8 ≤ (32 * r) ^ 8 := heighth
    _ = (32 : ℝ) ^ 8 * r ^ 8 := by ring
    _ = (32 : ℝ) ^ 8 * ((2 : ℝ) ^ ((4 : ℝ)⁻¹) * u) := by rw [hr8prod]
    _ ≤ (32 : ℝ) ^ 8 * (2 * u) := by gcongr
    _ = Q * u := by dsimp [Q]; ring

/-- Authentic host P8 implies polynomial order; the polynomial bound is not a premise. -/
theorem density_fourth_order (x d C0 : ℝ) (hx : 1 ≤ x) (hd : 0 ≤ d)
    (hC0 : 0 < C0) (hdensity : d ≤ 2 * C0 * (Real.log (2 * x)) ^ 8) :
    d ^ 4 ≤ (2 * C0 * Q) ^ 4 * x := by
  obtain ⟨u, hu, hu4, hlog⟩ := log_eighth_quarter_certificate x hx
  have hdu : d ≤ (2 * C0 * Q) * u := by
    calc
      _ ≤ 2 * C0 * (Real.log (2 * x)) ^ 8 := hdensity
      _ ≤ 2 * C0 * (Q * u) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring
  have hh := pow_le_pow_left₀ hd hdu 4
  simpa only [mul_pow, hu4] using hh

theorem moment_scale (L C W d u : ℝ) (hL : 1 ≤ L) (hC : 1 ≤ C)
    (hWC : W ≤ C) (hd : C * L ^ 4 ≤ d) (hu : 0 < u) (hu4 : u ^ 4 = d) :
    W * L ^ 6 * u ≤ d ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hL4 : L ^ 4 ≤ d := by
    calc
      _ = 1 * L ^ 4 := by ring
      _ ≤ C * L ^ 4 := mul_le_mul_of_nonneg_right hC (pow_nonneg hL0 4)
      _ ≤ d := hd
  have hLu : L ≤ u := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hu.le
    simpa only [hu4] using hL4
  have hd0 : 0 ≤ d := (by positivity : 0 ≤ C * L ^ 4).trans hd
  have h67 : L ^ 6 ≤ L ^ 7 := pow_le_pow_right₀ hL (by norm_num)
  calc
    W * L ^ 6 * u ≤ C * L ^ 6 * u := by gcongr
    _ ≤ C * L ^ 7 * u := by gcongr
    _ = (C * L ^ 4) * u * L ^ 3 := by ring
    _ ≤ d * u * L ^ 3 := by gcongr
    _ ≤ d * u * u ^ 3 := by gcongr
    _ = d ^ 2 := by rw [← hu4]; ring

theorem order_scale (x d L C P M : ℝ) (hL : 1 ≤ L) (hP : 0 < P)
    (hM : 1 ≤ M) (hC : P * M ≤ C) (hd : C * L ^ 4 ≤ d)
    (hp8 : d ^ 4 ≤ P ^ 4 * x) : M * L ^ 7 ≤ x := by
  have hL0 : 0 ≤ L := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hC0 : 0 ≤ C := (mul_nonneg hP.le hM0).trans hC
  have hMfour : M ≤ M ^ 4 := by
    calc
      _ = 1 * M := by ring
      _ ≤ M ^ 3 * M := mul_le_mul_of_nonneg_right (one_le_pow₀ hM) hM0
      _ = _ := by ring
  have hlower : P ^ 4 * (M * L ^ 16) ≤ d ^ 4 := by
    calc
      _ ≤ P ^ 4 * (M ^ 4 * L ^ 16) := by gcongr
      _ = (P * M) ^ 4 * L ^ 16 := by ring
      _ ≤ C ^ 4 * L ^ 16 := by gcongr
      _ = (C * L ^ 4) ^ 4 := by ring
      _ ≤ d ^ 4 := pow_le_pow_left₀ (by positivity) hd 4
  have hcancel : M * L ^ 16 ≤ x :=
    (mul_le_mul_iff_right₀ (pow_pos hP 4)).mp (hlower.trans hp8)
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by norm_num : (7 : ℕ) ≤ 16)) hM0).trans hcancel

/-- Exact uniform applicability of all three strengthened moment-host criteria.
K and n0 precede the quantifiers over the actual orders and degree. -/
theorem exists_uniform_strong_applicability (c b C0 C1 : ℝ)
    (hc : 0 < c) (hb : 0 < b) (hb1 : b ≤ 1) (hC0 : 0 < C0) (hC1 : 0 < C1) :
    ∃ K : ℝ, 0 < K ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
      ∀ (n N : ℕ) (D d Lambda : ℝ), n0 ≤ n → 3 ≤ N → N ≤ n →
        K * (Real.log (n : ℝ)) ^ 5 ≤ D →
        c * D / Real.log (n : ℝ) ≤ d →
        d ≤ 2 * C0 * (Real.log (2 * (N : ℝ))) ^ 8 →
        1 ≤ Lambda → Lambda ≤ C1 * (Real.log (2 * d)) ^ 8 →
        let gamma := b / (Real.log (n : ℝ)) ^ 2
        let k := ⌈(2 : ℝ) + Real.log (N : ℝ) / gamma⌉₊
        1 ≤ d ∧ 0 < gamma ∧ gamma ≤ 1 ∧ 2 ≤ k ∧
          (10 : ℝ) ^ 1000 * (k : ℝ) * Real.log (N : ℝ) ≤ d ∧
          (10 : ℝ) ^ 1000 * Lambda * (k : ℝ) * Real.log (N : ℝ) ≤ d ^ 2 * gamma ∧
          (10 : ℝ) ^ 1000 * (k : ℝ) ^ 2 * Real.log (N : ℝ) ≤ (N : ℝ) := by
  let A : ℝ := hostConstant
  let P : ℝ := 2 * C0 * Q
  let T : ℝ := C1 * Q
  let M : ℝ := 16 * A / b ^ 2
  let W : ℝ := 4 * A * T / b ^ 2
  let C : ℝ := 1 + 4 * A / b + W + P * M
  let K : ℝ := C / c
  let L0 : ℝ := max 1 (1 / Real.log 3)
  let n0 : ℕ := max 3 (⌈Real.exp L0⌉₊ + 1)
  have hA : 1 ≤ A := one_le_pow₀ (by norm_num)
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hA
  have hP : 0 < P := by dsimp [P]; exact mul_pos (by positivity) Q_pos
  have hT : 0 < T := mul_pos hC1 Q_pos
  have hb2pos : 0 < b ^ 2 := sq_pos_of_pos hb
  have hb2le : b ^ 2 ≤ 1 := by nlinarith
  have hM : 1 ≤ M := by
    apply (le_div_iff₀ hb2pos).mpr
    calc
      1 * b ^ 2 ≤ 1 := by simpa using hb2le
      _ ≤ A := hA
      _ ≤ 16 * A := le_mul_of_one_le_left hApos.le (by norm_num)
  have hW : 0 < W := by dsimp [W]; positivity
  have hPM : 0 < P * M := mul_pos hP (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hM)
  have hcoef : 0 < 4 * A / b := by positivity
  have hC : 1 ≤ C := by
    calc
      1 ≤ 1 + 4 * A / b := le_add_of_nonneg_right hcoef.le
      _ ≤ 1 + 4 * A / b + W := le_add_of_nonneg_right hW.le
      _ ≤ C := le_add_of_nonneg_right hPM.le
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hC
  have hCdegree : 4 * A / b ≤ C := by
    calc
      _ ≤ 1 + 4 * A / b := le_add_of_nonneg_left (by norm_num)
      _ ≤ 1 + 4 * A / b + W := le_add_of_nonneg_right hW.le
      _ ≤ C := le_add_of_nonneg_right hPM.le
  have hCmoment : W ≤ C := by
    calc
      _ ≤ 1 + 4 * A / b + W := le_add_of_nonneg_left (add_nonneg zero_le_one hcoef.le)
      _ ≤ C := le_add_of_nonneg_right hPM.le
  have hCorder : P * M ≤ C :=
    le_add_of_nonneg_left (add_nonneg (add_nonneg zero_le_one hcoef.le) hW.le)
  have hcK : c * K = C := by dsimp [K]; field_simp [hc.ne']
  refine ⟨K, div_pos hCpos hc, n0, Nat.le_max_left _ _, ?_⟩
  intro n N D d Lambda hn hN3 hNn hD hExtract hP8 hLambda1 hLambda
  let L : ℝ := Real.log (n : ℝ)
  let z : ℝ := Real.log (N : ℝ)
  let gamma : ℝ := b / L ^ 2
  let a : ℝ := L ^ 2 * z / b
  let k : ℕ := ⌈(2 : ℝ) + z / gamma⌉₊
  change 1 ≤ d ∧ 0 < gamma ∧ gamma ≤ 1 ∧ 2 ≤ k ∧
    A * (k : ℝ) * z ≤ d ∧ A * Lambda * (k : ℝ) * z ≤ d ^ 2 * gamma ∧
    A * (k : ℝ) ^ 2 * z ≤ (N : ℝ)
  have hceiln : ⌈Real.exp L0⌉₊ < n := by
    have hh : ⌈Real.exp L0⌉₊ + 1 ≤ n := (Nat.le_max_right _ _).trans hn
    omega
  have hexpn : Real.exp L0 < (n : ℝ) :=
    (Nat.le_ceil (Real.exp L0)).trans_lt (by exact_mod_cast hceiln)
  have hL0 : L0 ≤ L := by
    have hh := Real.log_le_log (Real.exp_pos L0) hexpn.le
    simpa only [Real.log_exp] using hh
  have hL : 1 ≤ L := (le_max_left _ _).trans hL0
  have hLpos : 0 < L := by linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hLg3 : 1 ≤ L * Real.log 3 :=
    (div_le_iff₀ hlog3).mp ((le_max_right _ _).trans hL0)
  have hNreal : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < N := by linarith
  have hz3 : Real.log 3 ≤ z := Real.log_le_log (by norm_num) hNreal
  have hzpos : 0 < z := hlog3.trans_le hz3
  have hzL : z ≤ L := Real.log_le_log hNpos (by exact_mod_cast hNn)
  have hgammapos : 0 < gamma := div_pos hb (sq_pos_of_pos hLpos)
  have hgamma1 : gamma ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hLpos)).mpr
    nlinarith
  have ha : 1 ≤ a := by
    apply (le_div_iff₀ hb).mpr
    have hLsq : L ≤ L ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hz3 (sq_nonneg L)
    have hh' := mul_le_mul_of_nonneg_right hLsq hlog3.le
    nlinarith
  have hzdiv : z / gamma = a := by
    dsimp [gamma, a]
    field_simp [hb.ne', hLpos.ne']
  have hk : (k : ℝ) ≤ 4 * a := by
    simpa only [k, hzdiv] using OldGlobalApplicability.ceil_block_le a ha
  have hk2 : 2 ≤ k := by
    have hh : 2 + a ≤ (k : ℝ) := by simpa only [k, hzdiv] using Nat.le_ceil (2 + a)
    exact_mod_cast (show (2 : ℝ) ≤ k by linarith)
  have hdC : C * L ^ 4 ≤ d := by
    calc
      _ = c * (K * L ^ 5) / L := by rw [← hcK]; field_simp [hLpos.ne']
      _ ≤ c * D / L := by gcongr
      _ ≤ d := hExtract
  have hd1 : 1 ≤ d := by
    have hp : 1 ≤ L ^ 4 := one_le_pow₀ hL
    have hh : 1 ≤ C * L ^ 4 := one_le_mul_of_one_le_of_one_le hC hp
    exact hh.trans hdC
  have hdpos : 0 < d := by linarith
  obtain ⟨u, hu, hu4, hlogd⟩ := log_eighth_quarter_certificate d hd1
  have hLambdau : Lambda ≤ T * u := by
    calc
      _ ≤ C1 * (Real.log (2 * d)) ^ 8 := hLambda
      _ ≤ C1 * (Q * u) := mul_le_mul_of_nonneg_left hlogd hC1.le
      _ = _ := by dsimp [T]; ring
  have hmoment_scale : W * L ^ 6 * u ≤ d ^ 2 :=
    moment_scale L C W d u hL hC hCmoment hdC hu hu4
  have hp8order : d ^ 4 ≤ P ^ 4 * (N : ℝ) :=
    density_fourth_order (N : ℝ) d C0 (by linarith) hdpos.le hC0 hP8
  have horder_scale : M * L ^ 7 ≤ (N : ℝ) :=
    order_scale (N : ℝ) d L C P M hL hP hM hCorder hdC hp8order
  have hdegree : A * (k : ℝ) * z ≤ d := by
    calc
      _ ≤ A * (4 * a) * z := by gcongr
      _ = (4 * A / b) * L ^ 2 * z ^ 2 := by dsimp [a]; ring
      _ ≤ (4 * A / b) * L ^ 2 * L ^ 2 := by gcongr
      _ = (4 * A / b) * L ^ 4 := by ring
      _ ≤ C * L ^ 4 := mul_le_mul_of_nonneg_right hCdegree (by positivity)
      _ ≤ d := hdC
  have hmoment : A * Lambda * (k : ℝ) * z ≤ d ^ 2 * gamma := by
    apply (div_le_iff₀ hgammapos).mp
    calc
      _ ≤ A * (T * u) * (4 * a) * z / gamma := by gcongr
      _ = W * u * L ^ 4 * z ^ 2 := by
        dsimp [W, a, gamma]
        field_simp [hb.ne', hLpos.ne']
      _ ≤ W * u * L ^ 4 * L ^ 2 := by gcongr
      _ = W * L ^ 6 * u := by ring
      _ ≤ d ^ 2 := hmoment_scale
  have horder : A * (k : ℝ) ^ 2 * z ≤ (N : ℝ) := by
    calc
      _ ≤ A * (4 * a) ^ 2 * z := by gcongr
      _ = M * L ^ 4 * z ^ 3 := by
        dsimp [M, a]
        field_simp [hb.ne']
        ring
      _ ≤ M * L ^ 4 * L ^ 3 := by gcongr
      _ = M * L ^ 7 := by ring
      _ ≤ (N : ℝ) := horder_scale
  exact ⟨hd1, hgammapos, hgamma1, hk2, hdegree, hmoment, horder⟩

end Erdos642.CampaignFe72210bContinuation3.StrongGlobalApplicability
