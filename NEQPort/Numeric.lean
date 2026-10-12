import NEQPort.Reduction

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
namespace Erdos585.NEQ
open QB4 B5
universe u

lemma threshold_add {q n e : ℕ} (hq : 6 ≤ q) (hn : 2 ≤ n) :
    (q - 1) * n - q / 2 ≤ e ↔ (q - 1) * n ≤ e + q / 2 := by
  have hhalf : q / 2 ≤ q - 1 := by omega
  have hm : q - 1 ≤ (q - 1) * n := by
    have h := Nat.mul_le_mul_left (q - 1) (by omega : 1 ≤ n)
    simpa using h
  omega

lemma general_order_numeric {q n e : ℕ} (hq : 6 ≤ q) (heven : Even q)
    (hn : 2 ≤ n) (he : (q - 1) * n ≤ e + q / 2)
    (hsimple : 2 * e ≤ n * (n - 1)) : 2 * q - 1 ≤ n := by
  have hh := even_half q heven
  have hp : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hqZ : 6 ≤ (q : ℤ) := by exact_mod_cast hq
  have hnZ : 2 ≤ (n : ℤ) := by exact_mod_cast hn
  by_contra! hsmall
  have hsZ : (n : ℤ) ≤ 2 * (q : ℤ) - 2 := by omega
  have hprod : 0 ≤ ((n : ℤ) - 1) * (2 * (q : ℤ) - 2 - n) :=
    mul_nonneg (by omega) (by omega)
  zify at he hh hsimple
  rw [hp] at he
  rw [hn1] at hsimple
  nlinarith

open scoped Classical in
theorem general_feasible_order {V : Type u} [Fintype V]
    (q : ℕ) (hq : 6 ≤ q) (heven : Even q) (G : SimpleGraph V)
    (hn : 2 ≤ Fintype.card V)
    (he : (q - 1) * Fintype.card V ≤ G.edgeSet.ncard + q / 2) :
    2 * q - 1 ≤ Fintype.card V := by
  have hs := G.card_edgeFinset_le_card_choose_two
  have hec : #G.edgeFinset = G.edgeSet.ncard := by
    simp only [SimpleGraph.edgeFinset, Set.toFinset_card,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [hec, Nat.choose_two_right] at hs
  have hs2 : 2 * G.edgeSet.ncard ≤ Fintype.card V * (Fintype.card V - 1) := by
    omega
  exact general_order_numeric hq heven hn he hs2

lemma proper_floor_from_failure {q n e : ℕ} (hq : 6 ≤ q) (heven : Even q)
    (hfail : e + q / 2 < (q - 1) * n) :
    (q : ℤ) + 2 ≤ (2 * (q : ℤ) - 2) * n - 2 * (e : ℤ) := by
  have hh := even_half q heven
  have hp : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  zify at hfail hh
  rw [hp] at hfail
  nlinarith

lemma component_charge_nonnegative {d a b eps : ℤ}
    (hd : 0 ≤ d) (hb : 0 ≤ b) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hgEven : Even (d + a + b)) (haEven : Even (a - eps)) :
    Even (d + b - eps) ∧ 0 ≤ d + b - eps := by
  obtain ⟨x, hx⟩ := hgEven
  obtain ⟨y, hy⟩ := haEven
  have hc : d + b - eps = (x - y - eps) + (x - y - eps) := by linarith
  exact ⟨⟨x - y - eps, hc⟩, by omega⟩

lemma component_exceeds_residual {q d a b eps : ℤ}
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hfloor : q + 2 ≤ d + a + b) (hzero : d + b - eps = 0) :
    q ≤ a - eps := by omega

lemma budget_classification {q k delta dT eT charge : ℤ}
    (hq : 6 ≤ q) (hk : 1 ≤ k) (hdelta : delta ≤ -2)
    (hd : 0 ≤ dT) (he : 0 ≤ eT) (hc : 0 ≤ charge)
    (hid : q = (q - 2) * k - delta + 2 * dT + 2 * eT + charge) :
    k = 1 ∧ delta = -2 ∧ dT = 0 ∧ eT = 0 ∧ charge = 0 := by
  have hp : 0 ≤ (q - 6) * (k - 1) := mul_nonneg (by omega) (by omega)
  have hk1 : k = 1 := by nlinarith
  subst k
  simp only [mul_one] at hid
  exact ⟨rfl, by omega, by omega, by omega, by omega⟩

#print axioms threshold_add
#print axioms general_order_numeric
#print axioms general_feasible_order
#print axioms proper_floor_from_failure
#print axioms component_charge_nonnegative
#print axioms component_exceeds_residual
#print axioms budget_classification
end Erdos585.NEQ
