import Openmath.Erdos642.Proofs.Joint20261019.Parameters

namespace Erdos642.Joint20261019.Absorption
open Erdos642.CampaignFe72210bContinuation3
open MomentSAParameters MomentOccupationAbsorption Parameters

theorem aAnew_large : (10 : ℝ)^45 ≤ a*Anew := by
  have hp : (10 : ℝ)^250 ≤ Anew :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) (by norm_num : (250 : ℕ) ≤ 3000)
  exact (by norm_num [a,beta] : (10 : ℝ)^45 ≤ a*(10 : ℝ)^250).trans
    (mul_le_mul_of_nonneg_left hp a_pos.le)

theorem coefficient_exp_le (C R B : ℝ) (hC : 0 < C)
    (hlog : Real.log C ≤ R-B) : C*Real.exp (-R) ≤ Real.exp (-B) := by
  calc
    _ = Real.exp (Real.log C-R) := by
      rw [sub_eq_add_neg,Real.exp_add,Real.exp_log hC]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem fast_budget (N k t m : ℕ) (ell d : ℝ)
    (hell : 1 < ell) (hk : ell ≤ k)
    (hdegree : Anew*k ≤ d) (horder : Anew*(k:ℝ)^2*ell ≤ N)
    (ht : a*N/(32*k) ≤ (t:ℝ)) (hm : (m:ℝ) ≤ (N:ℝ)/d) :
    (m:ℝ) ≤ (t:ℝ)/(4*(10:ℝ)^35) ∧ 51*ell ≤ (t:ℝ)/(4*(10:ℝ)^35) := by
  have hellpos : 0 < ell := by linarith
  have ha := a_pos
  have hkpos : (0:ℝ) < k := hellpos.trans_le hk
  have hk1 : (1:ℝ) ≤ k := by linarith
  have hd : 0 < d := (mul_pos Anew_pos hkpos).trans_le hdegree
  have ht' := (div_le_iff₀ (by positivity : (0:ℝ)<32*k)).mp ht
  have hm' := (le_div_iff₀ hd).mp hm
  have hc : (6528:ℝ)*(10:ℝ)^35 ≤ a*Anew :=
    (by norm_num : (6528:ℝ)*(10:ℝ)^35 ≤ (10:ℝ)^45).trans aAnew_large
  constructor
  · have hp : (32*(k:ℝ))*(4*(10:ℝ)^35*m) ≤ (32*k)*t := calc
      _ = (128*(10:ℝ)^35)*((m:ℝ)*k) := by ring
      _ ≤ (a*Anew)*((m:ℝ)*k) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = a*((m:ℝ)*(Anew*k)) := by ring
      _ ≤ a*((m:ℝ)*d) := by gcongr
      _ ≤ a*N := mul_le_mul_of_nonneg_left hm' a_pos.le
      _ ≤ _ := by simpa only [mul_comm] using ht'
    have hh := le_of_mul_le_mul_left hp (by positivity : (0:ℝ)<32*k)
    apply (le_div_iff₀ (by positivity : (0:ℝ)<4*(10:ℝ)^35)).mpr
    nlinarith only [hh]
  · have hp : (32*(k:ℝ))*((51*ell)*(4*(10:ℝ)^35)) ≤ (32*k)*t := calc
      _ = (6528*(10:ℝ)^35)*((k:ℝ)*ell) := by ring
      _ ≤ (a*Anew)*((k:ℝ)*ell) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ (a*Anew)*((k:ℝ)^2*ell) := by gcongr; nlinarith
      _ = a*(Anew*(k:ℝ)^2*ell) := by ring
      _ ≤ a*N := mul_le_mul_of_nonneg_left horder a_pos.le
      _ ≤ _ := by simpa only [mul_comm] using ht'
    exact (le_div_iff₀ (by positivity : (0:ℝ)<4*(10:ℝ)^35)).mpr
      (le_of_mul_le_mul_left hp (by positivity : (0:ℝ)<32*k))

theorem fast_raw_absorbed (N k t q m : ℕ) (d : ℝ)
    (hN : 3 ≤ N) (hk : Real.log (N:ℝ) ≤ k)
    (hdegree : Anew*k ≤ d) (horder : Anew*(k:ℝ)^2*Real.log (N:ℝ) ≤ N)
    (ht : a*N/(32*k) ≤ (t:ℝ)) (hq : q ≤ N) (hm : (m:ℝ) ≤ (N:ℝ)/d) :
    (50*(N:ℝ)*(q:ℝ)*2^m)*Real.exp (-(t:ℝ)/(10:ℝ)^35) ≤
      Real.exp (-(t:ℝ)/(2*(10:ℝ)^35)) := by
  have hell := Erdos642.CampaignFe72210b.IntegrationParameters.log_order_gt_one N hN
  have hb := fast_budget N k t m (Real.log N) d hell hk hdegree horder ht hm
  by_cases hq0 : q=0
  · simp only [hq0,Nat.cast_zero,mul_zero,zero_mul]
    exact (Real.exp_pos _).le
  have hqp : (0:ℝ)<q := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlog50 : Real.log (50:ℝ) ≤ 49 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<50)
    norm_num at hh ⊢; exact hh
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢; exact hh
  have hlogq := Real.log_le_log hqp (show (q:ℝ)≤N by exact_mod_cast hq)
  have hlog : Real.log (50*(N:ℝ)*(q:ℝ)*2^m) ≤ (t:ℝ)/(2*(10:ℝ)^35) := by
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) hqp.ne',
      Real.log_mul (by norm_num) hNp.ne',Real.log_pow]
    have hh := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    nlinarith only [hb.1,hb.2,hlog50,hlogq,hh,hell]
  have hh := coefficient_exp_le (50*(N:ℝ)*(q:ℝ)*2^m)
    ((t:ℝ)/(10:ℝ)^35) ((t:ℝ)/(2*(10:ℝ)^35)) (by positivity) (by linarith)
  simpa only [neg_div] using hh

theorem slow_budget (N k t D : ℕ) (ell d γ Λ : ℝ)
    (hell : 1 < ell) (hk : ell ≤ k) (hd : 0<d) (hγ : 0<γ) (hΛ : 0≤Λ)
    (horder : Anew*(k:ℝ)^2*ell ≤ N) (hgap : ell ≤ γ*k)
    (hmoment : Anew*Λ*k ≤ d^2*γ) (ht : a*N/(32*k) ≤ (t:ℝ))
    (hrank : (D:ℝ) ≤ 16*Λ*N/d^2) :
    51*ell + 200*D ≤ γ*t/(2*(10:ℝ)^35) := by
  have hellpos : 0<ell := by linarith
  have ha := a_pos
  have hkpos : (0:ℝ)<k := hellpos.trans_le hk
  have ht' := (div_le_iff₀ (by positivity : (0:ℝ)<32*k)).mp ht
  have hc : (409600:ℝ)*(10:ℝ)^35 ≤ a*Anew :=
    (by norm_num : (409600:ℝ)*(10:ℝ)^35 ≤ (10:ℝ)^45).trans aAnew_large
  have hsmall : 51*ell ≤ γ*t/(4*(10:ℝ)^35) := by
    have hp : (32*(k:ℝ))*((51*ell)*(4*(10:ℝ)^35)) ≤ (32*k)*(γ*t) := calc
      _ = (6528*(10:ℝ)^35)*((k:ℝ)*ell) := by ring
      _ ≤ (a*Anew)*((k:ℝ)*ell) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (a*Anew)*((γ*k)*k*ell) := by
        gcongr
        have hh : (1:ℝ)≤γ*k := by linarith
        nlinarith
      _ = γ*a*(Anew*(k:ℝ)^2*ell) := by ring
      _ ≤ γ*a*N := mul_le_mul_of_nonneg_left horder (by positivity)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left ht' hγ.le
        nlinarith only [hh]
    exact (le_div_iff₀ (by positivity : (0:ℝ)<4*(10:ℝ)^35)).mpr
      (le_of_mul_le_mul_left hp (by positivity : (0:ℝ)<32*k))
  have hbig : 200*(D:ℝ) ≤ γ*t/(4*(10:ℝ)^35) := by
    have hp : (32*(k:ℝ))*((3200*Λ*N)*(4*(10:ℝ)^35)) ≤ (32*k)*((γ*t)*d^2) := calc
      _ = (409600*(10:ℝ)^35)*((Λ*k)*N) := by ring
      _ ≤ (a*Anew)*((Λ*k)*N) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (a*(Anew*Λ*k))*N := by ring
      _ ≤ (a*(d^2*γ))*N := by gcongr
      _ = (a*N)*(d^2*γ) := by ring
      _ ≤ ((t:ℝ)*(32*k))*(d^2*γ) := mul_le_mul_of_nonneg_right ht' (by positivity)
      _ = _ := by ring
    have hh := le_of_mul_le_mul_left hp (by positivity : (0:ℝ)<32*k)
    have hdense : 3200*Λ*N/d^2 ≤ γ*t/(4*(10:ℝ)^35) :=
      (div_le_div_iff₀ (sq_pos_of_pos hd) (by positivity)).mpr hh
    calc
      _ ≤ 200*(16*Λ*N/d^2) := mul_le_mul_of_nonneg_left hrank (by norm_num)
      _ = 3200*Λ*N/d^2 := by ring
      _ ≤ _ := hdense
  linarith

theorem slow_raw_absorbed (N k t D : ℕ) (d γ Λ : ℝ)
    (hN : 3≤N) (hk : Real.log (N:ℝ)≤k) (hd : 0<d) (hγ : 0<γ) (hΛ : 0≤Λ)
    (horder : Anew*(k:ℝ)^2*Real.log (N:ℝ) ≤ N) (hgap : Real.log (N:ℝ)≤γ*k)
    (hmoment : Anew*Λ*k ≤ d^2*γ) (ht : a*N/(32*k) ≤ (t:ℝ))
    (hrank : (D:ℝ)≤16*Λ*N/d^2) :
    (50*(N:ℝ)*Real.exp (200*D))*Real.exp (-γ*t/(10:ℝ)^35) ≤
      Real.exp (-γ*t/(2*(10:ℝ)^35)) := by
  have hell := Erdos642.CampaignFe72210b.IntegrationParameters.log_order_gt_one N hN
  have hb := slow_budget N k t D (Real.log N) d γ Λ hell hk hd hγ hΛ
    horder hgap hmoment ht hrank
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlog50 : Real.log (50:ℝ)≤49 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<50)
    norm_num at hh ⊢; exact hh
  have hlog : Real.log (50*(N:ℝ)*Real.exp (200*D)) ≤ γ*t/(2*(10:ℝ)^35) := by
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_mul (by norm_num) hNp.ne',Real.log_exp]
    linarith
  have hh := coefficient_exp_le (50*(N:ℝ)*Real.exp (200*D))
    (γ*t/(10:ℝ)^35) (γ*t/(2*(10:ℝ)^35)) (by positivity) (by linarith)
  simpa only [neg_div,neg_mul] using hh

end Erdos642.Joint20261019.Absorption
