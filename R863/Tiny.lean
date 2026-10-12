import R863.Geometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section

namespace Erdos585.R863
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Data
variable {h q j e : ℕ} {A B : Finset V} (d : Data h q j e G A B)
include d

omit [DecidableEq V] in
lemma theta_small_bound {T : Finset V} (hsize : #T ≤ q - 2) :
    thetaJ q j G A B T ≤ (h : ℤ) * q - offset h e + j - q * #T := by
  classical
  have hq := d.parameters.q_ge_height
  have hphi : ∀ a ∈ A, max 0 (row q G B T a) ≤ 2 * (q : ℤ) - 2 - dg G B a := by
    classical
    intro a ha
    have hd := dg_le_card (G := G) T a
    have hc := d.capA_int ha
    unfold row
    omega
  have hsum : (∑ a ∈ A, max 0 (row q G B T a)) ≤
      (h : ℤ) * q - offset h e - ((q : ℤ) - 1) * j := by
    classical
    calc
      _ ≤ deficiency (2 * (q : ℤ) - 2) G B A := sum_le_sum hphi
      _ = _ := d.deficient
  unfold thetaJ theta
  nlinarith

omit [DecidableEq V] in
lemma theta_intermediate {T : Finset V} (hlo : h ≤ #T) (hhi : #T ≤ q - 2) :
    thetaJ q j G A B T ≤ (j : ℤ) - offset h e := by
  classical
  have hh := d.theta_small_bound hhi
  have hp : 0 ≤ (q : ℤ) * ((#T : ℤ) - h) :=
    mul_nonneg (Nat.cast_nonneg _) (by omega)
  nlinarith


omit [DecidableEq V] in
lemma theta_tiny_eq {T : Finset V} (htiny : #T < h) :
    thetaJ q j G A B T = (q : ℤ)*j-q*#T := by
  classical
  have hzero : ∀ v∈A, max 0 (row q G B T v)=0 := by
    classical
    intro v hv
    have hd := dg_le_card (G := G) T v
    have hh := d.parameters.height
    have hm := d.highA v hv
    apply max_eq_left
    unfold row
    omega
  unfold thetaJ theta
  rw [sum_eq_zero hzero]
  ring

omit [DecidableEq V] in
lemma theta_tiny_le {T : Finset V} (htiny : #T < h) :
    thetaJ q j G A B T ≤ (q : ℤ)*j := by
  classical
  rw [d.theta_tiny_eq htiny]
  have hp : 0≤(q : ℤ)*#T := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  omega

omit [DecidableEq V] in
lemma small_good {O T : Finset V} (hOj : #O=j) (hOT : O⊆T)
    (hsmall : #T≤q-2) : thetaJ q j G A B T≤0 := by
  classical
  have hjt : j≤#T := by rw [←hOj];exact card_le_card hOT
  by_cases htiny : #T<h
  · rw [d.theta_tiny_eq htiny]
    have hp : 0≤(q:ℤ)*((#T:ℤ)-j) := mul_nonneg (Nat.cast_nonneg _) (by omega)
    nlinarith
  · have ht := d.theta_intermediate (by omega) hsmall
    have hn := d.parameters.numeric
    have hj := d.parameters.j_bounds
    omega

end Data
end Erdos585.R863
