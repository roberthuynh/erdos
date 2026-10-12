import GeneralStar.UniformSeed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.GeneralStar

theorem ceilDiv_le (x y m : ℕ) (hy : 0 < y) (hxy : x ≤ y*m) : ceilDiv x y ≤ m := by
  unfold ceilDiv
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hy).mpr
  have hsum : x+y-1+1=x+y := by omega
  have hmul : m.succ*y=y*m+y := by simp [Nat.succ_mul,Nat.mul_comm]
  omega

theorem ceilDiv_mul (x y : ℕ) (hy : 0 < y) : x ≤ y*ceilDiv x y := by
  unfold ceilDiv
  have he := Nat.mod_add_div (x+y-1) y
  have hm := Nat.mod_lt (x+y-1) hy
  omega

theorem ceilDiv_pred_le_floor (x y : ℕ) (hy : 0 < y) : ceilDiv x y-1 ≤ x/y := by
  have he := Nat.mod_add_div x y
  have hm := Nat.mod_lt x hy
  have hceil := ceilDiv_le x y (x/y+1) hy (by nlinarith)
  exact Nat.sub_le_iff_le_add.mpr hceil

theorem closedD_bounds (q : ℕ) (hq : 9 ≤ q) :
    2 ≤ closedD q ∧ 2*(closedD q)^2 ≤ q-1 ∧ q-1 < 2*(closedD q+1)^2 := by
  have hl := Nat.sqrt_le' ((q-1)/2)
  have hu := Nat.lt_succ_sqrt' ((q-1)/2)
  have he := Nat.mod_add_div (q-1) 2
  have hm := Nat.mod_lt (q-1) (by omega : 0 < 2)
  have hd : 2 ≤ Nat.sqrt ((q-1)/2) := Nat.le_sqrt.mpr (by omega)
  change 2 ≤ Nat.sqrt ((q-1)/2) ∧ 2*(Nat.sqrt ((q-1)/2))^2 ≤ q-1 ∧
    q-1 < 2*(Nat.sqrt ((q-1)/2)+1)^2
  constructor
  · exact hd
  · constructor
    · have hmul := Nat.mul_le_mul_left 2 hl
      omega
    · simp only [Nat.succ_eq_add_one] at hu
      have hmul := Nat.mul_le_mul_left 2 (show (q-1)/2+1 ≤ (Nat.sqrt ((q-1)/2)+1)^2 by omega)
      omega

theorem default_product (r d : ℕ) (hd : 2 ≤ d) (_hl : 2*d^2 ≤ r)
    (hv : r=2*d^2 ∨ 2*d^2+d ≤ r) :
    max (d+ceilDiv r (2*d)) (ceilDiv r d-1) ≤ r/d := by
  have hdpos : 0 < d := by omega
  have h2pos : 0 < 2*d := by omega
  apply max_le
  · rcases hv with hv | hv
    · have he : r/d=2*d := by
        have ht : r=(2*d)*d := by rw [hv];ring
        rw [ht,Nat.mul_div_cancel _ hdpos]
      have hceil := ceilDiv_le r (2*d) d h2pos (by nlinarith)
      omega
    · let m := r/d
      have he := Nat.mod_add_div r d
      have hm := Nat.mod_lt r hdpos
      have hml : 2*d+1 ≤ m := (Nat.le_div_iff_mul_le hdpos).mpr (by nlinarith)
      have hguard : r ≤ (2*d)*(m-d) := by
        have hsub : m-d+d=m := by omega
        have hw : r < d*(m+1) := by dsimp [m];nlinarith
        nlinarith
      have hceil := ceilDiv_le r (2*d) (m-d) h2pos hguard
      change d+ceilDiv r (2*d) ≤ m
      omega
  · exact ceilDiv_pred_le_floor r d hdpos

theorem closed_params_ge9 (q : ℕ) (hq : 9 ≤ q) :
    UParams q (closedS q) (closedP q) (closedH q) (closedB q) := by
  have hq7 : ¬ (q=7 ∨ q=8) := by omega
  have hq7' : q ≠ 7 := by omega
  have hq8 : q ≠ 8 := by omega
  obtain ⟨hd,hl,_hu⟩ := closedD_bounds q hq
  let d := closedD q
  let r := q-1
  have hr : r+1=q := by dsimp [r];omega
  have hdr : 2*d^2 ≤ r := hl
  have hd' : 2 ≤ d := hd
  by_cases hex : exceptional q
  · simp only [closedS,closedP,closedH,closedB,if_neg hq7,if_neg hq7',if_neg hq8,if_pos hex]
    change UParams q d (2*d) (2*d) (r+2*d^2)
    have hps : d ≤ 2*d := by omega
    have hab : q+d ≤ r+2*d^2 := by nlinarith
    have hbq : r+2*d^2-q+q=r+2*d^2 := by omega
    have hbqs : r+2*d^2-q-d+q+d=r+2*d^2 := by omega
    have hdsub : 2*d-d=d := by omega
    have hbr : r ≤ r+2*d^2-2*d := by
      have hh : 2*d ≤ 2*d^2 := by nlinarith
      omega
    unfold UParams
    refine ⟨by omega,by omega,by omega,by nlinarith,hab,by nlinarith,by nlinarith,?_,?_,?_⟩
    · change r ≤ r+2*d^2-2*d
      exact hbr
    · rw [hdsub]
      nlinarith
    · rw [hdsub]
      nlinarith
  · have hv : r=2*d^2 ∨ 2*d^2+d ≤ r := by
      unfold exceptional at hex
      change ¬ (1 ≤ r-2*d^2 ∧ r-2*d^2 ≤ d-1) at hex
      omega
    have hprod := default_product r d hd' hdr hv
    let p := max (d+ceilDiv r (2*d)) (ceilDiv r d-1)
    have hdf : d*ceilDiv r (2*d) ≥ d*d := by
      have hc := ceilDiv_mul r (2*d) (by omega)
      nlinarith
    have hpl : 2*d ≤ p := by
      have hc := ceilDiv_mul r (2*d) (by omega)
      have hm := le_max_left (d+ceilDiv r (2*d)) (ceilDiv r d-1)
      change d+ceilDiv r (2*d) ≤ p at hm
      nlinarith
    have hpr : p*d ≤ r := by
      have hm := Nat.mul_le_mul_right d hprod
      have hb := Nat.div_mul_le_self r d
      dsimp [p] at hm ⊢
      omega
    have hpa : p ≤ q+d := by nlinarith
    have hab : q+d ≤ 2*r := by nlinarith
    have hph : p*(2*d) ≤ 2*r := by nlinarith
    have hbr : r ≤ 2*r-2*d := by
      have hlr : 2*d ≤ r := by nlinarith only [hdr,hd']
      omega
    have hfirst : r ≤ (p-d)*(2*d) := by
      have hc := ceilDiv_mul r (2*d) (by omega)
      have hm := le_max_left (d+ceilDiv r (2*d)) (ceilDiv r d-1)
      change d+ceilDiv r (2*d) ≤ p at hm
      have hsub : p-d+d=p := by omega
      nlinarith
    have hsecond : r-d ≤ p*d := by
      have hc := ceilDiv_mul r d (by omega)
      have hm := le_max_right (d+ceilDiv r (2*d)) (ceilDiv r d-1)
      change ceilDiv r d-1 ≤ p at hm
      have hceil : 1 ≤ ceilDiv r d := by nlinarith
      have hsub : ceilDiv r d-1+1=ceilDiv r d := by omega
      have hmprod := Nat.mul_le_mul_right d hm
      have he : (ceilDiv r d-1)*d+d=ceilDiv r d*d := by nlinarith only [hsub]
      have hc' : r ≤ ceilDiv r d*d := by simpa only [Nat.mul_comm] using hc
      omega
    simp only [closedS,closedP,closedH,closedB,if_neg hq7,if_neg hq7',if_neg hq8,if_neg hex]
    change UParams q d p (2*d) (2*r)
    have hsub : 2*d-d=d := by omega
    have hbq : 2*r-q=r-1 := by omega
    have hbqs : 2*r-q-d=r-d-1 := by omega
    have hrd : d < r := by nlinarith
    unfold UParams
    refine ⟨by omega,by omega,by omega,hpa,hab,by rfl,hph,?_,?_,?_⟩
    · change r ≤ 2*r-2*d
      exact hbr
    · rw [hbq];omega
    · rw [hsub,hbqs];omega

theorem closed_params (q : ℕ) (hq : 7 ≤ q) :
    UParams q (closedS q) (closedP q) (closedH q) (closedB q) := by
  by_cases hq7 : q=7
  · subst q
    norm_num [UParams,closedS,closedP,closedH,closedB]
  by_cases hq8 : q=8
  · subst q
    norm_num [UParams,closedS,closedP,closedH,closedB]
  exact closed_params_ge9 q (by omega)

end Erdos585.GeneralStar
