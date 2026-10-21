import Openmath.Erdos642.Proofs.DenseMask20261019.AvoidanceOrder

/-! Uniform finite-order constants for the avoidance-amplified sampler. -/
noncomputable section
namespace Erdos642.DenseMask20261019.SamplingParameters
open Real
open Erdos642.DenseMask20261019.AvoidanceOrder

private lemma order_growth (C c a B L p d : ℝ) (hC : 0 < C) (hc : 0 < c)
    (ha : 0 < a) (hB : 1 ≤ B) (hBa : 200*(Nat.factorial 12 : ℝ)/(c*a) ≤ B)
    (hL : 0 < L) (hpd : 128*C*B*L ≤ p*d) :
    100*L^3/(c*a) ≤ orderLower C (p*d/64) := by
  let x := p*d/(128*C)
  have hx : B*L ≤ x := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 128*C)).mpr
    nlinarith only [hpd]
  have hx0 : 0 ≤ x := (by positivity : 0 ≤ B*L).trans hx
  let t := x ^ (4 : ℝ)⁻¹
  have ht0 : 0 ≤ t := rpow_nonneg hx0 _
  have ht4 : t^4 = x := rpow_inv_natCast_pow hx0 (by decide : (4 : ℕ) ≠ 0)
  have ht12 : t^12 = x^3 := by rw [show (12 : ℕ) = 4*3 by decide, pow_mul, ht4]
  have hexp := pow_div_factorial_le_exp t ht0 12
  rw [ht12] at hexp
  have hB3 : B ≤ B^3 := by
    calc
      B = B^1 := by ring
      _ ≤ B^3 := pow_le_pow_right₀ hB (by decide : (1 : ℕ) ≤ 3)
  have hcube : (200*(Nat.factorial 12 : ℝ)/(c*a))*L^3 ≤ x^3 := by
    calc
      _ ≤ B*L^3 := mul_le_mul_of_nonneg_right hBa (by positivity)
      _ ≤ B^3*L^3 := mul_le_mul_of_nonneg_right hB3 (by positivity)
      _ = (B*L)^3 := by ring
      _ ≤ x^3 := pow_le_pow_left₀ (by positivity) hx 3
  have hfac : (0 : ℝ) < Nat.factorial 12 := by positivity
  have hlow : 100*L^3/(c*a) ≤ (1/2 : ℝ)*(x^3/(Nat.factorial 12 : ℝ)) := by
    calc
      _ ≤ x^3/(2*(Nat.factorial 12 : ℝ)) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*(Nat.factorial 12 : ℝ))).mpr
        calc
          _ = (200*(Nat.factorial 12 : ℝ)/(c*a))*L^3 := by ring
          _ ≤ x^3 := hcube
      _ = _ := by ring
  have hid : (p*d/64)/(2*C) = x := by dsimp [x]; field_simp; ring
  unfold orderLower
  rw [hid]
  exact hlow.trans (mul_le_mul_of_nonneg_left hexp (by norm_num))

/-- Constants depend only on C,D,a. All finite orders and all admissible
parameters satisfy the growth, entropy and polynomial normalization bounds. -/
theorem exists_sampling_parameters (C D a : ℝ) (hC : 0 < C) (hD : 1 ≤ D) (ha : 0 < a) :
    ∃ K epsilon : ℝ, 1000000 ≤ K ∧ 0 < epsilon ∧
      16*D*epsilon ≤ 1/10 ∧
      (1+16*D)*epsilon*log 2 ≤ (1/(64000*D))/8 ∧
      ∀ (n : ℕ) (L p d lam : ℝ), 2 ≤ n → log (2*n) ≤ L →
        0 < p → p ≤ 1 → 0 < d → 0 < lam → lam ≤ 1 →
        K*L ≤ p*d → a/L^2 ≤ p*lam →
        let m := orderLower C (p*d/64)
        0 < m ∧ 100*L/(1/(64000*D)) ≤ m*p*lam ∧
        2*log n/m ≤ (1/(64000*D))*p*lam/50 ∧
        ∀ k : ℝ, m ≤ k → exp (-((1/(64000*D))/4)*p*lam*k) ≤
          (1/(4*(n : ℝ)^5))*exp (-(1+16*D)*(epsilon*p*lam*k)*log 2) := by
  let c : ℝ := 1/(64000*D)
  have hD0 : 0 < D := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  let B := max (1 : ℝ) (200*(Nat.factorial 12 : ℝ)/(c*a))
  let K := max (1000000 : ℝ) (128*C*B)
  let eps := min (1/(160*D)) (c/(8*(1+16*D)*log 2))
  have heps : 0 < eps := by dsimp [eps]; apply lt_min <;> positivity
  have he1 : 16*D*eps ≤ 1/10 := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 160*D)).mp (min_le_left _ _ : eps ≤ _)
    nlinarith
  have he2 : (1+16*D)*eps*log 2 ≤ c/8 := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 8*(1+16*D)*log 2)).mp
      (min_le_right _ _ : eps ≤ _)
    nlinarith
  refine ⟨K,eps,le_max_left _ _,heps,he1,he2,?_⟩
  intro n L p d lam hn hL hp _hp1 hd hlam _hlam1 hpd hpl
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL0 : 0 < L := (log_pos (by linarith : (1 : ℝ) < 2*n)).trans_le hL
  have hBL : 128*C*B*L ≤ p*d :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _ : 128*C*B ≤ K) hL0.le).trans hpd
  let m := orderLower C (p*d/64)
  have hm0 : 0 < m := by dsimp [m,orderLower]; positivity
  have hmg : 100*L^3/(c*a) ≤ m :=
    order_growth C c a B L p d hC hc ha (le_max_left _ _) (le_max_right _ _) hL0 hBL
  have hmass : 100*L/c ≤ m*p*lam := by
    calc
      _ = (100*L^3/(c*a))*(a/L^2) := by field_simp [hc.ne',ha.ne',hL0.ne']
      _ ≤ m*(p*lam) := mul_le_mul hmg hpl (by positivity) hm0.le
      _ = _ := by ring
  have hlogn : log (n : ℝ) ≤ L := (log_le_log hn0 (by linarith)).trans hL
  have hmassC : 100*L ≤ c*(m*p*lam) := by
    have hh := (div_le_iff₀ hc).mp hmass
    nlinarith
  have hentropy : 2*log (n : ℝ)/m ≤ c*p*lam/50 := by
    apply (div_le_iff₀ hm0).mpr
    nlinarith
  refine ⟨hm0,hmass,hentropy,?_⟩
  intro k hmk
  have hk0 : 0 < k := hm0.trans_le hmk
  have hck : 100*L ≤ c*p*lam*k := by
    have hh := mul_le_mul_of_nonneg_left hmk (show 0 ≤ c*p*lam by positivity)
    nlinarith
  have hcost : (1+16*D)*(eps*p*lam*k)*log 2 ≤ c*p*lam*k/8 := by
    have hh := mul_le_mul_of_nonneg_right he2 (show 0 ≤ p*lam*k by positivity)
    nlinarith only [hh]
  have hlog4 : log (4 : ℝ) ≤ L :=
    (log_le_log (by norm_num) (by linarith : (4 : ℝ) ≤ 2*n)).trans hL
  have hlogpoly : log (4*(n : ℝ)^5) ≤ 6*L := by
    rw [log_mul (by norm_num) (pow_ne_zero 5 hn0.ne'), log_pow]
    norm_num
    linarith
  have hexponent : -(c/4)*p*lam*k ≤
      -log (4*(n : ℝ)^5) + (-(1+16*D)*(eps*p*lam*k)*log 2) := by
    nlinarith
  calc
    _ ≤ exp (-log (4*(n : ℝ)^5) + (-(1+16*D)*(eps*p*lam*k)*log 2)) :=
      exp_le_exp.mpr hexponent
    _ = _ := by
      rw [exp_add,exp_neg,exp_log (by positivity)]
      simp only [one_div]

end Erdos642.DenseMask20261019.SamplingParameters
