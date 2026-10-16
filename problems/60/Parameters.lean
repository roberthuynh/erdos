import Mathlib.Tactic
namespace Erdos60.Parameters

noncomputable def degreeF (q T k : ℝ) : ℝ :=
  (k-T-2)*q^2+(T+3-k)*q+3*k/2-k^2/2-2

theorem basic {q T : ℝ} (hq : 10^16 ≤ q) (hT : 1 ≤ T)
    (hr : T ≤ q / 10^8) : 0 < q ∧ 0 < T ∧ T ≤ q/1000 := by
  constructor
  · linarith
  constructor
  · linarith
  · linarith

theorem degree_left {q T : ℝ} (hq : 10^16 ≤ q) (hT : 1 ≤ T)
    (hr : T ≤ q/10^8) : 2*T*q < degreeF q T (T+3) := by
  have hq0 : 0 ≤ q := by linarith
  have ht0 : 0 ≤ T := by linarith
  have htq : T*q ≤ q^2/10^8 := by nlinarith [mul_nonneg (show 0 ≤ q by linarith) (sub_nonneg.mpr hr)]
  have htt : T^2 ≤ T*q/10^8 := by nlinarith [mul_nonneg (show 0 ≤ T by linarith) (sub_nonneg.mpr hr)]
  have hqq : 100*q ≤ q^2 := by nlinarith [mul_nonneg (show 0 ≤ q by linarith) (show 0 ≤ q-100 by linarith)]
  unfold degreeF
  nlinarith

theorem degree_right {q T : ℝ} (hq : 10^16 ≤ q) (hT : 1 ≤ T)
    (hr : T ≤ q/10^8) : 2*T*q < degreeF q T (q^2) := by
  have hq0 : 0 ≤ q := by linarith
  have ht0 : 0 ≤ T := by linarith
  have htq : T*q ≤ q^2/10^8 := by nlinarith [mul_nonneg (show 0 ≤ q by linarith) (sub_nonneg.mpr hr)]
  have htt : T*q^2 ≤ q^3/10^8 := by nlinarith [mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hr)]
  have hqq : 100*q ≤ q^2 := by nlinarith [mul_nonneg (show 0 ≤ q by linarith) (show 0 ≤ q-100 by linarith)]
  have hqqq : 100*q^2 ≤ q^3 := by nlinarith [mul_nonneg (sq_nonneg q) (show 0 ≤ q-100 by linarith)]
  have hqqqq : 100*q^3 ≤ q^4 := by nlinarith [mul_nonneg (show 0 ≤ q^3 by positivity) (show 0 ≤ q-100 by linarith)]
  have htq0 : 0 ≤ T*q := mul_nonneg ht0 hq0
  unfold degreeF
  nlinarith

theorem degree_interval {q T k : ℝ} (hq : 10^16 ≤ q) (hT : 1 ≤ T)
    (hr : T ≤ q/10^8) (hk : T+3 ≤ k) (hk' : k ≤ q^2) :
    2*T*q < degreeF q T k := by
  have hl := degree_left hq hT hr
  have hh := degree_right hq hT hr
  have hd : 0 < q^2-(T+3) := by
    have : q^2 ≥ 100*q := by nlinarith [mul_nonneg (show 0 ≤ q by linarith) (show 0 ≤ q-100 by linarith)]
    linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hk')
  by_contra hn
  have hn' : degreeF q T k ≤ 2*T*q := le_of_not_gt hn
  have hstrict : 0 < (q^2-k)*(degreeF q T (T+3)-2*T*q) +
      (k-(T+3))*(degreeF q T (q^2)-2*T*q) := by
    rcases lt_or_eq_of_le hk with h | h
    · have := mul_pos (sub_pos.mpr h) (sub_pos.mpr hh)
      nlinarith [mul_nonneg (sub_nonneg.mpr hk') (le_of_lt (sub_pos.mpr hl))]
    · subst k
      nlinarith [mul_pos hd (sub_pos.mpr hl)]
  have hmul := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd) (sub_nonpos.mpr hn')
  unfold degreeF at *
  nlinarith

theorem high_pair {q T : ℝ} (hq : 10^16 ≤ q) (hT : 1 ≤ T)
    (hr : T ≤ q/10^8) :
    2*T*q < q^2/10-21*q/10-1 ∧ 2*T*q < 3*q^2/5-3*q/5-6 := by
  have htq : T*q ≤ q^2/10^8 := by nlinarith [mul_nonneg (show 0 ≤ q by linarith) (sub_nonneg.mpr hr)]
  have hqq : 100*q ≤ q^2 := by nlinarith [mul_nonneg (show 0 ≤ q by linarith) (show 0 ≤ q-100 by linarith)]
  constructor <;> nlinarith

noncomputable def unionLower (q D : ℝ) : ℝ :=
  (q^2+q-2)*(q-1)*(q-2)/2 - (q-1)*(D+2+2*q/5) -
    (q^2-q-D)*(q^2-q-D-1)/2

noncomputable def disjointLower (q D : ℝ) : ℝ :=
  (q^2+q-1)*(q-1)*(q-2)/2 + (q-1)*(-q+1-D-2*q/5) -
    (q^2-q-1-D)*(q^2-q-2-D)/2

theorem high_pair_interval {q T D : ℝ} (hq : 10^16 ≤ q) (hT : 1 ≤ T)
    (hr : T ≤ q/10^8) (hd : 2 ≤ D) (hd' : D ≤ 2*T+4) :
    2*T*q < unionLower q D ∧ 2*T*q < disjointLower q D := by
  have he := high_pair hq hT hr
  have hq2 : 100*q ≤ q^2 := by
    nlinarith [mul_nonneg (show 0 ≤ q by linarith) (show 0 ≤ q-100 by linarith)]
  have hf : 0 ≤ q^2-2*q-D-2 := by linarith
  have hp := mul_nonneg (sub_nonneg.mpr hd) hf
  have hu : q^2/10-21*q/10-1 ≤ unionLower q D := by
    unfold unionLower
    nlinarith [sq_nonneg (D-2)]
  have hh : 3*q^2/5-3*q/5-6 ≤ disjointLower q D := by
    unfold disjointLower
    nlinarith [sq_nonneg (D-2)]
  exact ⟨lt_of_lt_of_le he.1 hu, lt_of_lt_of_le he.2 hh⟩

theorem simultaneous_core {q T m : ℝ} (hq : 10^16 ≤ q) (hT : 1 ≤ T)
    (hr : T ≤ q/10^8) (hm : m ≤ 292*T) :
    999*q/1000 ≤ q-318*T ∧ q-1+312*T ≤ 1001*q/1000 ∧
    292*T ≤ q/1000 ∧ q/2 < q-1-3*m-20*T := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem sqrt_parameter {q T : ℝ} (hq : 10^16 ≤ q) (hT : 1 ≤ T)
    (hr : T ≤ q/10^8) :
    10^8 ≤ Real.sqrt (T*q) ∧ Real.sqrt (T*q) ≤ q/10000 ∧
    1+2*Real.sqrt (T*q)+20*T ≤ 3*Real.sqrt (T*q) := by
  have hp : 0 ≤ T*q := mul_nonneg (by linarith) (by linarith)
  have hs := Real.sq_sqrt hp
  have hs0 := Real.sqrt_nonneg (T*q)
  have htq : T*q ≤ q^2/10^8 := by
    nlinarith [mul_nonneg (show 0 ≤ q by linarith) (sub_nonneg.mpr hr)]
  have hlow : 10^8 ≤ Real.sqrt (T*q) := by
    nlinarith [mul_nonneg (show 0 ≤ T-1 by linarith) (show 0 ≤ q by linarith)]
  have hu : Real.sqrt (T*q) ≤ q/10000 := by nlinarith
  have ht : 1000*T ≤ Real.sqrt (T*q) := by
    have := mul_nonneg (show 0 ≤ T by linarith) (sub_nonneg.mpr hr)
    nlinarith
  exact ⟨hlow, hu, by linarith⟩

theorem high_count_parameter {q T h : ℝ} (hq : 10^16 ≤ q) (hT : 1 ≤ T)
    (hr : T ≤ q/10^8) (hh : h ≤ 3*Real.sqrt (T*q)) :
    h ≤ q/10 ∧ h/(q+1) ≤ T := by
  have hs := sqrt_parameter hq hT hr
  have hhq : h ≤ q/10 := by linarith [hs.2.1]
  constructor
  · exact hhq
  · apply (div_le_iff₀ (show 0 < q+1 by linarith)).2
    nlinarith [mul_nonneg (show 0 ≤ q+1 by linarith) (show 0 ≤ T-1 by linarith)]

theorem retained_denominator {q T : ℝ} (hq : 10^16 ≤ q)
    (hr : T ≤ q/10^8) : q/2 < q-1-896*T := by linarith

theorem high_sum_bound {q T h P : ℝ} (hq : 10^16 ≤ q) (hT : 1 ≤ T)
    (hr : T ≤ q/10^8) (hh0 : 0 ≤ h) (hh : h ≤ 3*Real.sqrt (T*q))
    (hP : (q-h-1)*P ≤ 4*T*q+q+h^2/2+Real.sqrt 2*h*Real.sqrt (T*q)+5*h*T) :
    P ≤ 20*T := by
  have hs := sqrt_parameter hq hT hr
  have hp : 0 ≤ T*q := mul_nonneg (by linarith) (by linarith)
  have hs2 := Real.sq_sqrt hp
  have hs0 := Real.sqrt_nonneg (T*q)
  have hhq : h ≤ q/10 := by linarith [hs.2.1]
  have hhs : h^2 ≤ 9*T*q := by nlinarith
  have hsqrt : Real.sqrt 2 ≤ 17/12 := by
    have := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have := Real.sqrt_nonneg (2:ℝ)
    nlinarith
  have hcross : Real.sqrt 2*h*Real.sqrt (T*q) ≤ 17/4*T*q := by
    have hmul := mul_le_mul_of_nonneg_right hh hs0
    have hmul2 := mul_le_mul_of_nonneg_right hsqrt
      (mul_nonneg hh0 hs0)
    nlinarith
  have hht : h*T ≤ T*q/10 := by
    nlinarith [mul_nonneg (show 0 ≤ T by linarith) (sub_nonneg.mpr hhq)]
  have htq : q ≤ T*q := by
    nlinarith [mul_nonneg (show 0 ≤ q by linarith) (show 0 ≤ T-1 by linarith)]
  have hcoef : 4*q/5 ≤ q-h-1 := by linarith
  by_contra hn
  have hP0 : 0 ≤ P := by linarith
  have := mul_le_mul_of_nonneg_right hcoef hP0
  nlinarith

theorem neighborhood_parameters {q T b : ℝ} (hq : 10^16 ≤ q) (hT : 1 ≤ T)
    (hr : T ≤ q/10^8) (hb : 50*T ≤ b) (hb' : b ≤ q-76*T) :
    12*T*q < (q-26*T-b)*(b-20*T) ∧
    T*q < (q-172*T)*(q-172*T-1)/2 := by
  have ht0 : 0 ≤ T := by linarith
  have htq : T*q ≤ q^2/10^8 := by
    nlinarith [mul_nonneg (show 0 ≤ q by linarith) (sub_nonneg.mpr hr)]
  have htt : T^2 ≤ T*q/10^8 := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hr)]
  have hp := mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hb')
  have hq2 : 100*q ≤ q^2 := by
    nlinarith [mul_nonneg (show 0 ≤ q by linarith) (show 0 ≤ q-100 by linarith)]
  constructor <;> nlinarith

theorem transport_parameter {q T cu cv : ℝ} (hq : 10^16 ≤ q)
    (hr : T ≤ q/10^8) (hu : cu ≤ 4*q/5)
    (hp : q-175*T ≤ cu+2*cv) : q/20 ≤ cv := by linarith

theorem aggregate_parameter {q T : ℝ} (hq : 10^16 ≤ q) (hT : 1 ≤ T)
    (hr : T ≤ q/10^8) :
    9*T*q < 10*T*q-20201*T^2-285*T*Real.sqrt (T*q) := by
  have hs := sqrt_parameter hq hT hr
  have htt : T^2 ≤ T*q/10^8 := by
    nlinarith [mul_nonneg (show 0 ≤ T by linarith) (sub_nonneg.mpr hr)]
  have hts : T*Real.sqrt (T*q) ≤ T*q/10000 := by
    nlinarith [mul_nonneg (show 0 ≤ T by linarith) (sub_nonneg.mpr hs.2.1)]
  have hp : 0 < T*q := mul_pos (by linarith) (by linarith)
  nlinarith

#print axioms degree_interval
#print axioms high_pair_interval
#print axioms sqrt_parameter
#print axioms high_count_parameter
#print axioms retained_denominator
#print axioms high_sum_bound
#print axioms neighborhood_parameters
#print axioms transport_parameter
#print axioms aggregate_parameter
#print axioms simultaneous_core
end Erdos60.Parameters
