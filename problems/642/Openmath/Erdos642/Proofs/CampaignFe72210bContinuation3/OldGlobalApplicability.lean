import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! Uniform scalar applicability of the old spectral host theorem.

The actual host order ranges over every `3 ≤ N ≤ n`. No extraction, moment,
desired logarithmic estimate, or old applicability conclusion is assumed.
-/
namespace Erdos642.CampaignFe72210bContinuation3.OldGlobalApplicability

/-- An elementary certificate for the logarithm bound at every x≥1. -/
theorem log_square_root_certificate (x : ℝ) (hx : 1 ≤ x) :
    ∃ y : ℝ, 0 ≤ y ∧ y ^ 5 = x ∧ (Real.log x) ^ 2 ≤ 100 * y := by
  let u : ℝ := x ^ ((10 : ℝ)⁻¹)
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hu : 0 < u := Real.rpow_pos_of_pos hxpos _
  have hpow : u ^ 10 = x :=
    Real.rpow_inv_natCast_pow hxpos.le (by norm_num : (10 : ℕ) ≠ 0)
  have hlogu : Real.log u = (10 : ℝ)⁻¹ * Real.log x := Real.log_rpow hxpos _
  have hlog := Real.log_le_sub_one_of_pos hu
  have hupper : Real.log x ≤ 10 * u := by norm_num at hlogu; linarith
  have hsq := pow_le_pow_left₀ (Real.log_nonneg hx) hupper 2
  refine ⟨u ^ 2, sq_nonneg u, ?_, ?_⟩
  · calc
      (u ^ 2) ^ 5 = u ^ 10 := by ring
      _ = x := hpow
  · nlinarith only [hsq]

/-- The coarse root estimate pays the order condition uniformly in x. -/
theorem order_from_fifth_scale (x L M : ℝ) (hx : 1 ≤ x)
    (hL : 0 ≤ L) (hM : 1 ≤ M)
    (hscale : (100 * M) ^ 5 * L ^ 5 ≤ x) :
    M * L ^ 4 * (Real.log x) ^ 2 ≤ x := by
  obtain ⟨y, hy, hyfive, hlog⟩ := log_square_root_certificate x hx
  have hbig : 1 ≤ 100 * M := by linarith
  have hbig0 : 0 ≤ 100 * M := by linarith
  have hroot : 100 * M * L ≤ y := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0) hy
    rw [hyfive, mul_pow]
    exact hscale
  have hfour := pow_le_pow_left₀ (mul_nonneg hbig0 hL) hroot 4
  have hcoefficient : 100 * M ≤ (100 * M) ^ 4 := by
    calc
      _ = 1 * (100 * M) := by ring
      _ ≤ (100 * M) ^ 3 * (100 * M) :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hbig) hbig0
      _ = _ := by ring
  have hfourlower : 100 * M * L ^ 4 ≤ y ^ 4 := by
    calc
      _ ≤ (100 * M) ^ 4 * L ^ 4 :=
        mul_le_mul_of_nonneg_right hcoefficient (pow_nonneg hL 4)
      _ = (100 * M * L) ^ 4 := by ring
      _ ≤ y ^ 4 := hfour
  calc
    M * L ^ 4 * (Real.log x) ^ 2 ≤ M * L ^ 4 * (100 * y) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = y * (100 * M * L ^ 4) := by ring
    _ ≤ y * y ^ 4 := mul_le_mul_of_nonneg_left hfourlower hy
    _ = x := by nlinarith only [hyfive]

theorem ceil_block_le (a : ℝ) (ha : 1 ≤ a) :
    (⌈2 + a⌉₊ : ℝ) ≤ 4 * a := by
  have hh := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 + a by linarith)
  linarith

/-- Fully quantified old-host scalar applicability with fixed positive c,b.
Both the degree and actual-order conditions are derived, not supplied. -/
theorem exists_uniform_old_applicability (c b : ℝ) (hc : 0 < c)
    (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
      ∀ (n N : ℕ) (d : ℝ), n0 ≤ n → 3 ≤ N → N ≤ n →
        c * K * (Real.log (n : ℝ)) ^ 5 ≤ d → d + 1 ≤ (N : ℝ) →
        let gamma := b / (Real.log (n : ℝ)) ^ 2
        let k := ⌈(2 : ℝ) + Real.log (N : ℝ) / gamma⌉₊
        0 < gamma ∧ gamma ≤ 1 ∧
          (10 : ℝ) ^ 100 * (k : ℝ) / gamma ≤ d ∧
          (10 : ℝ) ^ 100 * (k : ℝ) ^ 2 ≤ (N : ℝ) := by
  let A : ℝ := 10 ^ 100
  let M : ℝ := 16 * A / b ^ 2
  let C : ℝ := (100 * M) ^ 5
  let K : ℝ := C / c
  let L0 : ℝ := max 1 (1 / Real.log 3)
  let n0 : ℕ := max 3 (⌈Real.exp L0⌉₊ + 1)
  have hA : 1 ≤ A := by norm_num [A]
  have hApos : 0 < A := by linarith
  have hb2pos : 0 < b ^ 2 := sq_pos_of_pos hb
  have hb2le : b ^ 2 ≤ 1 := by nlinarith
  have hM : 1 ≤ M := by
    apply (le_div_iff₀ hb2pos).mpr
    nlinarith
  have hbig : 1 ≤ 100 * M := by linarith
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hCbig : 100 * M ≤ C := by
    calc
      _ = 1 * (100 * M) := by ring
      _ ≤ (100 * M) ^ 4 * (100 * M) :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hbig) (by linarith)
      _ = C := by dsimp [C]; ring
  have hCM : M / 4 ≤ C := by linarith
  have hcK : c * K = C := by dsimp [K]; field_simp [hc.ne']
  refine ⟨K, div_pos hCpos hc, n0, Nat.le_max_left _ _, ?_⟩
  intro n N d hn hN3 hNn hd hNd
  let L : ℝ := Real.log (n : ℝ)
  let z : ℝ := Real.log (N : ℝ)
  let gamma : ℝ := b / L ^ 2
  let a : ℝ := L ^ 2 * z / b
  let k : ℕ := ⌈(2 : ℝ) + z / gamma⌉₊
  change 0 < gamma ∧ gamma ≤ 1 ∧ A * (k : ℝ) / gamma ≤ d ∧
    A * (k : ℝ) ^ 2 ≤ (N : ℝ)
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
  have hLg3 : 1 ≤ L * Real.log 3 := by
    apply (div_le_iff₀ hlog3).mp
    exact (le_max_right _ _).trans hL0
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
    simpa only [k, hzdiv] using ceil_block_le a ha
  have hdC : C * L ^ 5 ≤ d := by simpa only [hcK] using hd
  have hscale : (100 * M) ^ 5 * L ^ 5 ≤ (N : ℝ) := by
    change C * L ^ 5 ≤ (N : ℝ)
    linarith
  have horderbound : M * L ^ 4 * z ^ 2 ≤ (N : ℝ) :=
    order_from_fifth_scale (N : ℝ) L M (by linarith) hLpos.le hM hscale
  have hdegree : A * (k : ℝ) / gamma ≤ d := by
    calc
      _ ≤ A * (4 * a) / gamma := by gcongr
      _ = (M / 4) * L ^ 4 * z := by
        dsimp [M, a, gamma]
        field_simp [hb.ne', hLpos.ne']
        ring
      _ ≤ (M / 4) * L ^ 4 * L :=
        mul_le_mul_of_nonneg_left hzL (by positivity)
      _ = (M / 4) * L ^ 5 := by ring
      _ ≤ C * L ^ 5 := mul_le_mul_of_nonneg_right hCM (pow_nonneg hLpos.le 5)
      _ ≤ d := hdC
  have horder : A * (k : ℝ) ^ 2 ≤ (N : ℝ) := by
    calc
      _ ≤ A * (4 * a) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg k) hk 2) hApos.le
      _ = M * L ^ 4 * z ^ 2 := by
        dsimp [M, a]
        field_simp [hb.ne']
        ring
      _ ≤ (N : ℝ) := horderbound
  exact ⟨hgammapos, hgamma1, hdegree, horder⟩

end Erdos642.CampaignFe72210bContinuation3.OldGlobalApplicability
