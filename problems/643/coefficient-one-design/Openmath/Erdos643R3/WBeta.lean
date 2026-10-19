import Openmath.Erdos643R3.WUnbounded
import Openmath.Erdos643R3.G3hpArith

set_option autoImplicit false
namespace Erdos643R3.WBox

def gW (a c : ℕ) : ℚ :=
  1 / (2 * (2 + (a : ℚ))) + ((c : ℚ) - 1) / (2 * (1 + (a : ℚ))) +
    (a : ℚ) / (2 * (1 + (c : ℚ)))

def lossW (c m : ℕ) : ℚ :=
  if m = 0 then 0 else 1 / (2 * (1 + (c : ℚ))) - 1 / (2 * (1 + (c : ℚ) + m))

theorem inv_shift_mono (x y N : ℚ) (hy : 0 < y) (hxy : y ≤ x) (hN : 0 ≤ N) :
    1 / (y + N) - 1 / y ≤ 1 / (x + N) - 1 / x := by
  have hx : 0 < x := lt_of_lt_of_le hy hxy
  have heq (z : ℚ) (hz : 0 < z) : 1 / (z + N) - 1 / z = -N / (z * (z + N)) := by
    field_simp
    ring
  rw [heq x hx, heq y hy]
  have hh : N / (x * (x + N)) ≤ N / (y * (y + N)) := by
    apply div_le_div_of_nonneg_left hN (by positivity)
    nlinarith
  simpa only [neg_div] using neg_le_neg hh

theorem inv_step_bound (z : ℚ) (hz : 2 ≤ z) : 1 / z - 1 / (z + 1) ≤ 1 / 6 := by
  have hz0 : 0 < z := by linarith
  field_simp
  nlinarith [mul_nonneg (show 0 ≤ z - 2 by linarith) (show 0 ≤ z + 3 by linarith)]

theorem inv_step_bound_three (z : ℚ) (hz : 3 ≤ z) : 1 / z - 1 / (z + 1) ≤ 1 / 12 := by
  have hz0 : 0 < z := by linarith
  field_simp
  nlinarith [mul_nonneg (show 0 ≤ z - 3 by linarith) (show 0 ≤ z + 4 by linarith)]

theorem gW_one (a : ℕ) : (1 : ℚ) / 4 ≤ gW a 1 := by
  have ha : (0 : ℚ) ≤ a := Nat.cast_nonneg a
  unfold gW
  norm_num
  field_simp
  nlinarith [sq_nonneg (a : ℚ)]

theorem gW_one_pos (a : ℕ) (ha : 1 ≤ a) : (5 : ℚ) / 12 ≤ gW a 1 := by
  have ha' : (1 : ℚ) ≤ a := by exact_mod_cast ha
  unfold gW
  norm_num
  field_simp
  nlinarith [mul_nonneg (show 0 ≤ (a : ℚ) - 1 by linarith) (show 0 ≤ (a : ℚ) + 1 by linarith)]

/-- Lemma W Step 1, the numerical beta estimate after the host degree caps. -/
theorem betaW_le_cost (a c N m : ℕ) (hc : 1 ≤ c) (ha : 1 ≤ m → 1 ≤ a) :
    betaW N m ≤ 1 / (1 + (c : ℚ) + N) + gW a c - lossW c m := by
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  by_cases hc1 : c = 1
  · subst c
    by_cases hm0 : m = 0
    · have hh := gW_one a
      simp only [betaW, lossW, hm0, ↓reduceIte]
      norm_num
      linarith
    · have hh := gW_one_pos a (ha (by omega))
      simp only [betaW, lossW, hm0, ↓reduceIte]
      norm_num
      linarith
  · have hc2 : 2 ≤ c := by omega
    have hc' : (3 : ℚ) ≤ 1 + c := by exact_mod_cast (by omega : 3 ≤ 1 + c)
    have hf := G3hpArith.lemma6 (a := a) hc2
    have hfg : G3hpArith.f6 a c = 1 / (1 + (c : ℚ)) + gW a c := by
      unfold G3hpArith.f6 gW
      ring
    rw [hfg] at hf
    have hshift := inv_shift_mono (1 + (c : ℚ)) 3 N (by norm_num) hc' hN
    have hstep : 1 / (2 + (N : ℚ)) - 1 / (3 + (N : ℚ)) ≤ 1 / 6 := by
      convert inv_step_bound (2 + (N : ℚ)) (by linarith) using 1
      ring
    by_cases hm0 : m = 0
    · simp only [betaW, lossW, hm0, ↓reduceIte]
      norm_num at hshift
      simp only [one_div] at hf hstep ⊢
      linarith
    · have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      have hshiftm := inv_shift_mono (1 + (c : ℚ)) 3 m (by norm_num) hc' hm
      have hstepm : 1 / (2 + (m : ℚ)) - 1 / (3 + (m : ℚ)) ≤ 1 / 12 := by
        convert inv_step_bound_three (2 + (m : ℚ)) (by linarith) using 1
        ring
      simp only [betaW, lossW, hm0, ↓reduceIte]
      have heq (x : ℚ) : 1 / (2 * x) = (1 / x) / 2 := by ring
      simp only [heq]
      norm_num at hshift hshiftm
      simp only [one_div] at hf hstep hstepm ⊢
      linarith

end Erdos643R3.WBox
