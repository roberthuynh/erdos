import Openmath.Proofs.QB4.Statement

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
namespace Erdos585.BqOrder
open QB4
universe u

open scoped Classical in
theorem feasible_order (q : ℕ) (hq : 5 ≤ q) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hbip : G.IsBipartite) (hn : 2 ≤ Fintype.card V)
    (he : (q - 1) * Fintype.card V ≤ G.edgeSet.ncard + q) :
    2 * q ≤ Fintype.card V := by
  classical
  obtain ⟨o⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨U, W, _, hUW, hcov, hbw⟩ := exists_sides hbip o
  have hcard : #U + #W = Fintype.card V := by
    rw [← card_union_of_disjoint hUW, hcov, card_univ]
  have hbound : G.edgeSet.ncard ≤ #U * #W := by
    rw [← ec_eq_ncard hbw]
    exact ec_le_card_mul U W
  by_contra horder
  have hsmallNat : Fintype.card V < 2 * q := by omega
  have hqZ : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hnZ : (2 : ℤ) ≤ Fintype.card V := by exact_mod_cast hn
  have hsmallZ : (Fintype.card V : ℤ) < 2 * (q : ℤ) := by
    exact_mod_cast hsmallNat
  have hcardZ : (#U : ℤ) + #W = Fintype.card V := by exact_mod_cast hcard
  have hboundZ : (G.edgeSet.ncard : ℤ) ≤ (#U : ℤ) * #W := by
    exact_mod_cast hbound
  have heCast : (((q - 1) * Fintype.card V : ℕ) : ℤ) ≤
      ((G.edgeSet.ncard + q : ℕ) : ℤ) := by exact_mod_cast he
  have heZ : ((q : ℤ) - 1) * Fintype.card V ≤ (G.edgeSet.ncard : ℤ) + q := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ q),
      Nat.cast_one] using heCast
  have hproduct : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) *
      (4 * (q : ℤ) - Fintype.card V - 6) :=
    mul_nonneg (by omega) (by omega)
  have hsquare : (0 : ℤ) ≤ ((#U : ℤ) - #W) ^ 2 := sq_nonneg _
  have hidentity :
      4 * (((q : ℤ) - 1) * Fintype.card V - q) - 4 * (#U : ℤ) * #W =
      4 * ((q : ℤ) - 3) + ((Fintype.card V : ℤ) - 2) *
        (4 * (q : ℤ) - Fintype.card V - 6) + ((#U : ℤ) - #W) ^ 2 := by
    rw [← hcardZ]
    ring
  nlinarith

theorem threshold_nontruncated {q n : ℕ} (hq : 5 ≤ q) (hn : 2 ≤ n) :
    q ≤ (q - 1) * n := by
  have hmul := Nat.mul_le_mul_left (q - 1) hn
  omega

theorem threshold_positive {q n : ℕ} (hq : 5 ≤ q) (hn : 2 ≤ n) :
    0 < (q - 1) * n - q := by
  have hmul := Nat.mul_le_mul_left (q - 1) hn
  omega

theorem threshold_nat_add {q n e : ℕ} (hq : 5 ≤ q) (hn : 2 ≤ n) :
    ((q - 1) * n - q ≤ e) ↔ ((q - 1) * n ≤ e + q) := by
  have hnontruncated := threshold_nontruncated hq hn
  omega

theorem threshold_cast {q n : ℕ} (hq : 5 ≤ q) (hn : 2 ≤ n) :
    (((q - 1) * n - q : ℕ) : ℤ) = ((q : ℤ) - 1) * (n : ℤ) - q := by
  rw [Nat.cast_sub (threshold_nontruncated hq hn), Nat.cast_mul]
  have hpred : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  rw [hpred]

#print feasible_order
#print axioms feasible_order
#print axioms threshold_nontruncated
#print axioms threshold_positive
#print axioms threshold_nat_add
#print axioms threshold_cast
end Erdos585.BqOrder
