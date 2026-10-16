import R866.Carrier
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
namespace Erdos585.R866

lemma numeric {h q : ℕ} (hh : 6 ≤ h) (hq : 2^24*(h+1)^4 ≤ q) :
    4096*(h+1)^2 ≤ q ∧ 16*h^2 ≤ q := by
  have hs : 1 ≤ (h+1)^2 := by nlinarith
  have hc : h^2 ≤ (h+1)^2 := by nlinarith
  norm_num at hq
  constructor <;> nlinarith [sq_nonneg ((h+1)^2)]

lemma budget_cast {h : ℕ} (hh : 6 ≤ h) :
    ((4*h^2-10*h+4:ℕ):ℤ)=4*(h:ℤ)^2-10*h+4 := by
  have hs : 10*h ≤ 4*h^2 := by nlinarith
  rw [Nat.cast_add,Nat.cast_sub hs]
  push_cast
  ring

lemma selector_numeric {h q e : ℕ} (hh : 6 ≤ h)
    (hq : 2^24*(h+1)^4 ≤ q) (he : e ≤ 4*h^2-10*h+4) :
    2^20*(h+e+1)^2 ≤ q := by
  have hb : h+e+1 ≤ 4*(h+1)^2 := by
    have hs : 10*h ≤ 4*h^2 := by nlinarith
    have he2 : e ≤ 4*h^2+4 := by omega
    nlinarith
  have hp := Nat.pow_le_pow_left hb 2
  norm_num at hq ⊢
  nlinarith

lemma deficit_range {h q : ℕ} {e : ℤ} (hh : 6 ≤ h)
    (hq : 2^24*(h+1)^4 ≤ q) (he0 : 0 ≤ e)
    (he : e ≤ 4*(h:ℤ)^2-10*h+4) :
    2*(q:ℤ) ≤ (h:ℤ)*q-16*h^2+e ∧
    (h:ℤ)*q-16*h^2+e ≤ (h:ℤ)*q-12*h^2 := by
  have hq16 := (numeric hh hq).2
  have hh' : (6:ℤ) ≤ h := by exact_mod_cast hh
  have hq' : 16*(h:ℤ)^2 ≤ q := by exact_mod_cast hq16
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ (h:ℤ)-6 by omega) (show 0 ≤ (q:ℤ) by positivity)]
  · nlinarith
end Erdos585.R866
