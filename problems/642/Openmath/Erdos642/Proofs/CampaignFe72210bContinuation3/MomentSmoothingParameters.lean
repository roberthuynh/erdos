import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentSelfAvoidance

/-! Exact finite smoothing time, with both signs of the logarithm retained. -/
namespace Erdos642.CampaignFe72210bContinuation3.MomentSmoothingParameters
open Erdos642.CampaignFe72210b
noncomputable def mu0 : ℝ := 1/(10:ℝ)^15
noncomputable def scale (N : ℕ) (d Λ : ℝ) : ℝ := Real.sqrt (50*Λ*(N:ℝ))/d
noncomputable def argument (N : ℕ) (d Λ : ℝ) : ℝ := 1024*scale N d Λ/mu0
noncomputable def smoothingTime (N : ℕ) (d Λ : ℝ) : ℕ :=
  1+⌈Real.log (argument N d Λ)/Real.log 4⌉₊

theorem mu0_pos : 0 < mu0 := by norm_num [mu0]
theorem log_four_gt_one : 1 < Real.log 4 := by
  have hh := Real.log_le_log (by norm_num : (0:ℝ)<3) (by norm_num : (3:ℝ)≤4)
  nlinarith [Real.log_three_gt_d9]
theorem log_ten_lt_three : Real.log 10 < 3 := by
  rw [Real.log_ten_eq]
  nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

theorem smoothingTime_ge_one (N : ℕ) (d Λ : ℝ) : 1 ≤ smoothingTime N d Λ := by
  unfold smoothingTime
  omega

theorem argument_pos (N : ℕ) (hN : 3 ≤ N) (d Λ : ℝ) (hd : 0 < d) (hΛ : 1 ≤ Λ) :
    0 < argument N d Λ := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  unfold argument scale
  have hm := mu0_pos
  positivity

/-- Natural ceiling handles the nonpositive log branch without an omitted dense case. -/
theorem smoothingTime_tail (N : ℕ) (hN : 3 ≤ N) (d Λ : ℝ) (hd : 0 < d) (hΛ : 1 ≤ Λ) :
    scale N d Λ*(1/4:ℝ)^(smoothingTime N d Λ-1) ≤ mu0/1024 := by
  have ha := argument_pos N hN d Λ hd hΛ
  have hl4 : 0 < Real.log 4 := lt_trans zero_lt_one log_four_gt_one
  by_cases hsign : Real.log (argument N d Λ) ≤ 0
  · have hceil : ⌈Real.log (argument N d Λ)/Real.log 4⌉₊ = 0 :=
      Nat.ceil_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg hsign hl4.le)
    have harg : argument N d Λ ≤ 1 := by
      apply (Real.log_le_log_iff ha zero_lt_one).mp
      simpa only [Real.log_one] using hsign
    have hm := (div_le_iff₀ mu0_pos).mp harg
    simp only [smoothingTime,hceil,Nat.add_zero,Nat.sub_self,pow_zero,mul_one]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<1024)).mpr
    nlinarith
  · let j : ℕ := ⌈Real.log (argument N d Λ)/Real.log 4⌉₊
    have hj := Nat.le_ceil (Real.log (argument N d Λ)/Real.log 4)
    have hlog : Real.log (argument N d Λ) ≤ Real.log ((4:ℝ)^j) := by
      rw [Real.log_pow]
      exact (div_le_iff₀ hl4).mp hj
    have harg : argument N d Λ ≤ (4:ℝ)^j :=
      (Real.log_le_log_iff ha (pow_pos (by norm_num) _)).mp hlog
    have hm := (div_le_iff₀ mu0_pos).mp harg
    have hpow : 0 < (4:ℝ)^j := pow_pos (by norm_num) _
    have he : smoothingTime N d Λ-1=j := by dsimp [smoothingTime,j]; omega
    rw [he,one_div_pow]
    have heq : scale N d Λ * (1 / (4:ℝ)^j) = scale N d Λ / (4:ℝ)^j := by ring
    rw [heq]
    apply (div_le_div_iff₀ hpow (by norm_num : (0:ℝ)<1024)).mpr
    nlinarith

/-- Actual Lambda<=d² pays the numeric logarithmic numerator bound. -/
theorem argument_le_power_sqrt (N : ℕ) (hN : 3 ≤ N) (d Λ : ℝ)
    (hd : 0 < d) (_hΛ : 1 ≤ Λ) (hΛd : Λ ≤ d^2) :
    argument N d Λ ≤ (10:ℝ)^19*Real.sqrt (N:ℝ) := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hs : 0 ≤ Real.sqrt (N:ℝ) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt hn.le
  have hmul := mul_le_mul_of_nonneg_right hΛd (show 0≤50*(N:ℝ) by positivity)
  have hsqrt : Real.sqrt (50*Λ*(N:ℝ)) ≤ 8*d*Real.sqrt (N:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have heq := congrArg (fun z : ℝ => 64*d^2*z) hsq
      have hnon := mul_nonneg (sq_nonneg d) hn.le
      nlinarith
  unfold argument scale
  apply (div_le_iff₀ mu0_pos).mpr
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hd).mpr
  have hc : (8192:ℝ) ≤ (10:ℝ)^19*mu0 := by norm_num [mu0]
  have hh := mul_le_mul_of_nonneg_right hc (show 0≤d*Real.sqrt (N:ℝ) by positivity)
  nlinarith

theorem smoothingTime_le_log (N : ℕ) (hN : 3 ≤ N) (d Λ : ℝ)
    (hd : 0 < d) (hΛ : 1 ≤ Λ) (hΛd : Λ ≤ d^2) :
    (smoothingTime N d Λ:ℝ) ≤ 100*Real.log (N:ℝ) := by
  have hell := IntegrationParameters.log_order_gt_one N hN
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have ha := argument_pos N hN d Λ hd hΛ
  have hl4 : 0 < Real.log 4 := lt_trans zero_lt_one log_four_gt_one
  by_cases hsign : Real.log (argument N d Λ) ≤ 0
  · have hceil : ⌈Real.log (argument N d Λ)/Real.log 4⌉₊ = 0 :=
      Nat.ceil_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg hsign hl4.le)
    simp only [smoothingTime,hceil,Nat.add_zero,Nat.cast_one]
    linarith
  · have hlogpos : 0 < Real.log (argument N d Λ) := lt_of_not_ge hsign
    have hb := Real.log_le_log ha (argument_le_power_sqrt N hN d Λ hd hΛ hΛd)
    rw [Real.log_mul (by positivity : (10:ℝ)^19 ≠ 0)
      (ne_of_gt (Real.sqrt_pos.mpr hn)), Real.log_pow, Real.log_sqrt hn.le] at hb
    have hupper : Real.log (argument N d Λ) < 57+Real.log (N:ℝ)/2 := by
      nlinarith [log_ten_lt_three]
    have hdiv : Real.log (argument N d Λ)/Real.log 4 ≤ Real.log (argument N d Λ) := by
      apply (div_le_iff₀ hl4).mpr
      nlinarith [log_four_gt_one]
    have hc := Nat.ceil_lt_add_one (div_nonneg hlogpos.le hl4.le)
    simp only [smoothingTime,Nat.cast_add,Nat.cast_one]
    linarith

theorem smoothingTime_bounds (N : ℕ) (hN : 3 ≤ N) (d Λ : ℝ)
    (hd : 0 < d) (hΛ : 1 ≤ Λ) (hΛd : Λ ≤ d^2) :
    1 ≤ smoothingTime N d Λ ∧
    scale N d Λ*(1/4:ℝ)^(smoothingTime N d Λ-1) ≤ mu0/1024 ∧
    (smoothingTime N d Λ:ℝ) ≤ 100*Real.log (N:ℝ) :=
  ⟨smoothingTime_ge_one N d Λ,smoothingTime_tail N hN d Λ hd hΛ,
    smoothingTime_le_log N hN d Λ hd hΛ hΛd⟩
end Erdos642.CampaignFe72210bContinuation3.MomentSmoothingParameters
