import Openmath.Proofs.PaperSupport.BqMain

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.L34
open QB4 B5
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def Sparse (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) : Prop :=
  ∀ X ⊆ U, ∀ Y ⊆ W, 3 ≤ #X + #Y → #X + #Y < #U + #W →
    4 * (q : ℤ) - 8 ≤ potential (2 * (q : ℤ) - 2) G X Y

lemma Sparse.swap {q : ℕ} {U W : Finset V} (h : Sparse q G U W) : Sparse q G W U := by
  intro Y hY X hX hlarge hproper
  rw [Bq.potential_comm]
  exact h X hX Y hY (by omega) (by omega)

structure Input (q j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) : Prop where
  j_le : j ≤ 1
  card : #W = #U + j
  minU : ∀ a ∈ U, q ≤ dg G W a
  capU : ∀ a ∈ U, dg G W a ≤ 2 * q - 2
  minW : ∀ w ∈ W, q ≤ dg G U w
  capW : ∀ w ∈ W, dg G U w ≤ 2 * q - 2
  deficient : deficiency (2 * (q : ℤ) - 2) G W U =
    2 * (q : ℤ) - 5 - ((q : ℤ) - 1) * j
  sparse : Sparse q G U W

def thetaJ (q j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W T : Finset V) : ℤ := theta q G U W T + (q : ℤ) * j - q

lemma thetaJ_one (q : ℕ) (U W T : Finset V) :
    thetaJ q 1 G U W T = theta q G U W T := by simp [thetaJ]

lemma thetaJ_canonical (q j : ℕ) (U W T : Finset V) :
    thetaJ q j G U W T =
      (q : ℤ) * j - q * #T + ∑ a ∈ canonical q G U W T, row q G W T a := by
  have hh := mixed_canonical (G := G) q U W T
  unfold mixedTheta at hh
  unfold thetaJ
  linarith

lemma thetaJ_potential (q j : ℕ) (U W T : Finset V) :
    2 * thetaJ q j G U W T = 2 * (q : ℤ) * j +
      2 * ((#(canonical q G U W T) : ℤ) - #T) +
      2 * deficiency (2 * (q : ℤ) - 2) G W (canonical q G U W T) -
      potential (2 * (q : ℤ) - 2) G (canonical q G U W T) T := by
  have hh := mixed_potential (G := G) q W (canonical q G U W T) T
  rw [mixed_canonical] at hh
  unfold thetaJ
  linarith

namespace Input
variable {q j : ℕ} {U W : Finset V}

lemma capU_int (hq : 6 ≤ q) (h : Input q j G U W) {a : V} (ha : a ∈ U) :
    (dg G W a : ℤ) ≤ 2 * (q : ℤ) - 2 := by have hd := h.capU a ha; omega

lemma capW_int (hq : 6 ≤ q) (h : Input q j G U W) {w : V} (hw : w ∈ W) :
    (dg G U w : ℤ) ≤ 2 * (q : ℤ) - 2 := by have hd := h.capW w hw; omega

lemma theta_full (h : Input q j G U W) : thetaJ q j G U W W = 0 := by
  simp only [thetaJ, theta, row, sub_self, zero_add,
    max_eq_right (Nat.cast_nonneg q), sum_const, nsmul_eq_mul]
  rw [h.card]
  push_cast
  ring

lemma theta_small (hq : 6 ≤ q) (h : Input q j G U W) {T : Finset V}
    (hne : T.Nonempty) (hsize : #T ≤ q - 2) : thetaJ q j G U W T ≤ 0 := by
  have hqn : 6 ≤ (q : ℤ) := by exact_mod_cast hq
  have hj : (j : ℤ) ≤ 1 := by exact_mod_cast h.j_le
  have hphi : ∀ a ∈ U, max 0 (row q G W T a) ≤ 2 * (q : ℤ) - 2 - dg G W a := by
    intro a ha
    have hd := dg_le_card (G := G) T a
    have hc := h.capU_int hq ha
    unfold row
    omega
  have hsum : (∑ a ∈ U, max 0 (row q G W T a)) ≤
      2 * (q : ℤ) - 5 - ((q : ℤ) - 1) * j := by
    calc _ ≤ deficiency (2 * (q : ℤ) - 2) G W U := sum_le_sum hphi
      _ = _ := h.deficient
  have htn : 1 ≤ #T := card_pos.mpr hne
  by_cases ht1 : #T = 1
  · have hrow : ∀ a ∈ U, ((q : ℤ) - 2) * max 0 (row q G W T a) ≤
        2 * (q : ℤ) - 2 - dg G W a := by
      intro a ha
      have hd := dg_le_card (G := G) T a
      have hm := h.minU a ha
      have hc := h.capU_int hq ha
      by_cases hz : max 0 (row q G W T a) = 0
      · rw [hz, mul_zero]; omega
      · have hp : max 0 (row q G W T a) = 1 := by unfold row at *; omega
        have he : dg G W a = q := by unfold row at *; omega
        rw [hp, he]
        push_cast
        nlinarith
    have hs : ((q : ℤ) - 2) * (∑ a ∈ U, max 0 (row q G W T a)) ≤
        2 * (q : ℤ) - 5 - ((q : ℤ) - 1) * j := by
      rw [mul_sum]
      calc _ ≤ deficiency (2 * (q : ℤ) - 2) G W U := sum_le_sum hrow
        _ = _ := h.deficient
    have hsum0 : 0 ≤ ∑ a ∈ U, max 0 (row q G W T a) :=
      sum_nonneg fun _ _ => le_max_left _ _
    have hcases : j = 0 ∨ j = 1 := by omega
    rcases hcases with hj0 | hj1
    · rw [hj0] at hs ⊢
      simp only [thetaJ, theta, ht1, Nat.cast_zero, Nat.cast_one, mul_zero, mul_one]
      have hp : 0 < (q : ℤ) - 2 := by omega
      nlinarith
    · rw [hj1] at hs ⊢
      norm_num at hs
      simp only [thetaJ, theta, ht1, Nat.cast_one, mul_one]
      have hp : 0 < (q : ℤ) - 2 := by omega
      nlinarith
  · have ht2 : 2 ≤ (#T : ℤ) := by omega
    have hp : 0 ≤ (q : ℤ) * ((#T : ℤ) - 2) :=
      mul_nonneg (Nat.cast_nonneg _) (by omega)
    unfold thetaJ theta
    nlinarith

lemma edge_cap_T (hq : 6 ≤ q) (h : Input q j G U W)
    {X T : Finset V} (hX : X ⊆ U) (hT : T ⊆ W) :
    (ec G X T : ℤ) ≤ (2 * (q : ℤ) - 2) * #T := by
  rw [ec_comm, ec, Nat.cast_sum]
  calc
    _ ≤ ∑ _w ∈ T, (2 * (q : ℤ) - 2) := by
      refine sum_le_sum fun w hw => ?_
      have hd := dg_mono (G := G) hX w
      have hc := h.capW_int hq (hT hw)
      omega
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

lemma canonical_proper (h : Input q j G U W) {T : Finset V}
    (hT : T ⊆ W) (hp : 0 < thetaJ q j G U W T) :
    canonical q G U W T ≠ U := by
  intro heq
  have hc := card_sdiff_add_card_eq_card hT
  have he := ec_sdiff_add_right (G := G) hT U
  have hm := Bq.ec_lower_of_min (G := G) (sdiff_subset : W \ T ⊆ W) h.minW
  rw [ec_comm] at hm
  have hi := thetaJ_canonical (G := G) q j U W T
  rw [heq, row_sum] at hi
  have hcard := h.card
  zify at hc he hm hcard
  nlinarith

/-- Every actual positive test has height one and captures the entire scar.
The balanced branch is eliminated as part of this classification. -/
lemma positive_shape (hq : 6 ≤ q) (h : Input q j G U W) {T : Finset V}
    (hT : T ⊆ W) (hne : T.Nonempty) (hp : 0 < thetaJ q j G U W T) :
    j = 1 ∧ q - 1 ≤ #T ∧ #T < #W ∧ thetaJ q j G U W T = 1 ∧
      #(canonical q G U W T) = #T + 1 ∧
      deficiency (2 * (q : ℤ) - 2) G W (canonical q G U W T) = (q : ℤ) - 4 ∧
      potential (2 * (q : ℤ) - 2) G (canonical q G U W T) T = 4 * (q : ℤ) - 8 := by
  have hlargeT : q - 1 ≤ #T := by
    by_contra! hsmall
    have hh := h.theta_small hq hne (by omega)
    omega
  have htw : T ≠ W := fun heq => by subst T; have hf := h.theta_full; omega
  have hlt : #T < #W := card_lt_card ⟨hT, fun hh => htw (Subset.antisymm hT hh)⟩
  let C := canonical q G U W T
  let k : ℤ := (#C : ℤ) - #T
  let a : ℤ := deficiency (2 * (q : ℤ) - 2) G W C
  have hCU : C ⊆ U := canonical_subset q U W T
  have hj : (j : ℤ) ≤ 1 := by exact_mod_cast h.j_le
  have hqZ : 6 ≤ (q : ℤ) := by exact_mod_cast hq
  have han : 0 ≤ a := deficiency_nonneg _ (fun b hb => h.capU_int hq (hCU hb))
  have hal : a ≤ 2 * (q : ℤ) - 5 - ((q : ℤ) - 1) * j := by
    have hd := deficiency_le_subset (G := G) (2 * (q : ℤ) - 2) hCU
      (fun b hb => h.capU_int hq hb)
    simpa [a, h.deficient] using hd
  have hbound : thetaJ q j G U W T ≤ (q : ℤ) * ((j : ℤ) + k) := by
    rw [thetaJ_canonical]
    have hs : (∑ b ∈ C, row q G W T b) ≤ (q : ℤ) * #C := by
      calc _ ≤ ∑ _b ∈ C, (q : ℤ) := by
            refine sum_le_sum fun b _ => ?_
            have hd := dg_mono (G := G) hT b
            unfold row
            omega
        _ = _ := by simp [mul_comm]
    dsimp [k]
    nlinarith
  have hk0 : 1 - (j : ℤ) ≤ k := by
    by_contra! hbad
    have hn : (j : ℤ) + k ≤ 0 := by omega
    have hh := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg q) hn
    linarith
  have hsp := h.sparse C hCU T hT (by dsimp [k] at hk0; omega)
    (by have hc := card_le_card hCU; omega)
  have hi := thetaJ_potential (G := G) q j U W T
  have hik : 2 * thetaJ q j G U W T = 2 * (q : ℤ) * j + 2 * k + 2 * a -
      potential (2 * (q : ℤ) - 2) G C T := hi
  have hlow : thetaJ q j G U W T ≤ (j : ℤ) + k - 1 := by nlinarith
  have he := h.edge_cap_T hq hCU hT
  have hg : (2 * (q : ℤ) - 2) * k ≤ potential (2 * (q : ℤ) - 2) G C T := by
    dsimp [k]
    unfold potential
    nlinarith
  have hk2 : k < 2 := by
    by_contra! hbad
    have hprod : 0 ≤ ((q : ℤ) - 2) * (k - 2) := mul_nonneg (by omega) (by omega)
    nlinarith
  have hj1 : j = 1 := by omega
  have hk : k = 1 := by omega
  have ht : thetaJ q j G U W T = 1 := by omega
  have hc : #C = #T + 1 := by dsimp [k] at hk; omega
  have ha : a = (q : ℤ) - 4 := by rw [hj1] at hal hik; norm_num at hal hik; nlinarith
  have hgp : potential (2 * (q : ℤ) - 2) G C T = 4 * (q : ℤ) - 8 := by
    rw [hj1] at hik
    norm_num at hik
    have ht1 : thetaJ q 1 G U W T = 1 := by simpa only [hj1] using ht
    omega
  exact ⟨hj1, hlargeT, hlt, ht, hc, ha, hgp⟩

end Input
end Erdos585.L34
