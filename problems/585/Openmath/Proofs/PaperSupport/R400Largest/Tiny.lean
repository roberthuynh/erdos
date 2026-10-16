import Openmath.Proofs.PaperSupport.R400Largest.Geometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHLargestH3R400
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Data
variable {h q a₀ j : ℕ} {A B : Finset V} (d : Data h q a₀ j G A B)
include d

omit [DecidableEq V] in
lemma theta_small_bound {T : Finset V} (hsize : #T ≤ q - 2) :
    thetaJ q j G A B T ≤ (h : ℤ) * q - a₀ + j - q * #T := by
  have hq := d.parameters.q_ge_height
  have hphi : ∀ v ∈ A, max 0 (row q G B T v) ≤ 2 * (q : ℤ) - 2 - dg G B v := by
    intro v hv
    have hd := dg_le_card (G := G) T v
    have hc := d.capA_int hv
    unfold row
    omega
  have hsum : (∑ v ∈ A, max 0 (row q G B T v)) ≤
      (h : ℤ) * q - a₀ - ((q : ℤ) - 1) * j := by
    calc
      _ ≤ deficiency (2 * (q : ℤ) - 2) G B A := sum_le_sum hphi
      _ = _ := d.deficient
  unfold thetaJ theta
  nlinarith

omit [DecidableEq V] in
lemma theta_intermediate {T : Finset V} (hlo : h ≤ #T) (hhi : #T ≤ q - 2) :
    thetaJ q j G A B T ≤ (j : ℤ) - a₀ := by
  have hh := d.theta_small_bound hhi
  have hp : 0 ≤ (q : ℤ) * ((#T : ℤ) - h) :=
    mul_nonneg (Nat.cast_nonneg _) (by omega)
  nlinarith

omit [DecidableEq V] in
/-- No tiny original test has any positive optimizer row at largest surplus. -/
lemma theta_tiny_exact {T : Finset V} (hsize : #T < h) :
    thetaJ q j G A B T = (q : ℤ) * j - q * #T := by
  have hs := d.parameters.scar_tiny_single
  have hrow : ∀ v ∈ A, max 0 (row q G B T v) = 0 := by
    intro v hv
    apply max_eq_left
    by_contra! hp
    have hd := dg_le_card (G := G) T v
    have hscar := d.row_scar_le hv
    unfold row at hp
    omega
  unfold thetaJ theta
  rw [sum_eq_zero hrow]
  ring

omit [DecidableEq V] in
lemma theta_tiny_le {T : Finset V} (hsize : #T < h) :
    thetaJ q j G A B T ≤ (q : ℤ) * j := by
  rw [d.theta_tiny_exact hsize]
  have hm : 0 ≤ (q : ℤ) * #T := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  omega

omit [DecidableEq V] in
lemma small_good {O T : Finset V} (hOj : #O = j) (hOT : O ⊆ T)
    (hsmall : #T ≤ q - 2) : thetaJ q j G A B T ≤ 0 := by
  have hjt : j ≤ #T := by rw [← hOj]; exact card_le_card hOT
  by_cases htiny : #T < h
  · rw [d.theta_tiny_exact htiny]
    have hm : 0 ≤ (q : ℤ) * ((#T : ℤ) - j) :=
      mul_nonneg (Nat.cast_nonneg _) (by omega)
    nlinarith
  · have ht := d.theta_intermediate (by omega) hsmall
    have hn := d.parameters.numeric
    have hj := d.parameters.j_bounds
    omega

end Data
end Erdos585.AllHLargestH3R400
