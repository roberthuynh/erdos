import R866.Numeric
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
namespace Erdos585.R898

lemma numeric {h q : ℕ} (_hh : 6 ≤ h) (hq : 4096*(h+1)^2 ≤ q) :
    4096*(h+1)^2 ≤ q ∧ 16*h^2 ≤ q := by
  constructor
  · exact hq
  · nlinarith [sq_nonneg (h+1)]

lemma deficit_range {h q : ℕ} {e : ℤ} (hh : 6 ≤ h)
    (hq : 4096*(h+1)^2 ≤ q) (he0 : 0 ≤ e)
    (he : e ≤ 4*(h:ℤ)^2-10*h+4) :
    2*(q:ℤ) ≤ (h:ℤ)*q-16*h^2+e ∧
    (h:ℤ)*q-16*h^2+e ≤ (h:ℤ)*q-12*h^2 := by
  have hq16 := (numeric hh hq).2
  have hh' : (6:ℤ) ≤ h := by exact_mod_cast hh
  have hq' : 16*(h:ℤ)^2 ≤ q := by exact_mod_cast hq16
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ (h:ℤ)-6 by omega) (show 0 ≤ (q:ℤ) by positivity)]
  · nlinarith
end Erdos585.R898
