import NEQPort.Numeric

/-! Exact original empty-remainder intermediate, frozena487bb9b.
This conditional helper is not the bare NEQ or a full criterion-only NEQ
wrapper. Shore imbalance, zero internal T edges and every T saturation
are proved here from actual original incidences, never supplied. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
namespace Erdos585.NEQ
open QB4 B5
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
lemma ec_union_right {S T : Finset V} (hST : Disjoint S T) (X : Finset V) :
    ec G X (S ∪ T) = ec G X S + ec G X T := by
  unfold ec
  simp_rw [dg_union_of_disjoint hST]
  exact sum_add_distrib

omit [Fintype V] in
lemma deficiency_union (D : ℤ) (U : Finset V) {S T : Finset V}
    (hST : Disjoint S T) :
    deficiency D G U (S ∪ T) = deficiency D G U S + deficiency D G U T := by
  unfold deficiency
  exact sum_union hST

omit [Fintype V] [DecidableEq V] in
lemma zero_deficiency_degree (D : ℕ) {U T : Finset V}
    (hcap : ∀ t ∈ T, dg G U t ≤ D)
    (hzero : deficiency (D : ℤ) G U T = 0) {t : V} (ht : t ∈ T) :
    dg G U t = D := by
  have hall := (sum_eq_zero_iff_of_nonneg
    (fun x hx => by have hh := hcap x hx; omega)).mp hzero t ht
  have h := hcap t ht
  omega

open scoped Classical in
theorem neq_of_empty_barrier (q : ℕ) (hq : 6 ≤ q) (heven : Even q)
    (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V)
    (hcap : G.maxDegree ≤ 2 * q - 2)
    (hexact : G.edgeSet.ncard + q / 2 = (q - 1) * Fintype.card V)
    (S T : Finset V) (hST : Disjoint S T) (hcover : S ∪ T = univ)
    (hbarrier : (q : ℤ) * ((#T : ℤ) - #S) + (ec G S S : ℤ) ≤ -2) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  let D : ℤ := 2 * (q : ℤ) - 2
  let k : ℤ := (#S : ℤ) - #T
  let delta : ℤ := (q : ℤ) * ((#T : ℤ) - #S) + (ec G S S : ℤ)
  have hdelta : delta ≤ -2 := hbarrier
  have hqZ : 6 ≤ (q : ℤ) := by exact_mod_cast hq
  have hSS : 0 ≤ (ec G S S : ℤ) := by positivity
  have hTT : 0 ≤ (ec G T T : ℤ) := by positivity
  have hdeltaEq : delta = -(q : ℤ) * k + ec G S S := by dsimp [delta, k]; ring
  have hk : 1 ≤ k := by
    by_contra! hbad
    have hp : 0 ≤ -(q : ℤ) * k := mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    nlinarith
  have hcapI : ∀ v : V, (dg G univ v : ℤ) ≤ D := by
    intro v
    have h := (dg_le_maxDegree univ v).trans hcap
    dsimp [D]
    omega
  have hDT : 0 ≤ deficiency D G univ T :=
    deficiency_nonneg D (fun t _ => hcapI t)
  have htotal : deficiency D G univ univ = q :=
    exact_density_deficiency q hq heven hexact
  have hparts := deficiency_union (G := G) D univ hST
  rw [hcover] at hparts
  have hpartq : deficiency D G univ S + deficiency D G univ T = q :=
    hparts.symm.trans htotal
  have hSU : ec G S univ = ec G S S + ec G S T := by
    rw [← hcover]
    exact ec_union_right hST S
  have hTU : ec G T univ = ec G S T + ec G T T := by
    rw [← hcover, ec_union_right hST T, ec_comm (G := G) T S]
  have hSUZ : (ec G S univ : ℤ) = (ec G S S : ℤ) + ec G S T := by exact_mod_cast hSU
  have hTUZ : (ec G T univ : ℤ) = (ec G S T : ℤ) + ec G T T := by exact_mod_cast hTU
  have hdefS := deficiency_eq (G := G) D univ S
  have hdefT := deficiency_eq (G := G) D univ T
  have hid : (q : ℤ) = ((q : ℤ) - 2) * k - delta +
      2 * deficiency D G univ T + (ec G T T : ℤ) := by
    dsimp [D, k, delta] at *
    nlinarith
  have hb := budget_classification hqZ hk hdelta hDT (by norm_num : (0 : ℤ) ≤ 0) hTT
    (by simpa using hid)
  have hk1 : k = 1 := hb.1
  have hDzero : deficiency D G univ T = 0 := hb.2.2.1
  have hTTzero : ec G T T = 0 := by exact_mod_cast hb.2.2.2.2
  have hDcast : ((2 * q - 2 : ℕ) : ℤ) = D := by dsimp [D]; omega
  have hsaturatedTotal : ∀ t ∈ T, dg G univ t = 2 * q - 2 := by
    intro t ht
    apply zero_deficiency_degree (2 * q - 2)
      (fun x _ => (dg_le_maxDegree univ x).trans hcap)
      (by rw [hDcast]; exact hDzero) ht
  have hTzero : ∀ t ∈ T, dg G T t = 0 := by
    have hsum : ∑ t ∈ T, dg G T t = 0 := hTTzero
    exact (sum_eq_zero_iff_of_nonneg (fun t _ => Nat.zero_le (dg G T t))).mp hsum
  have hsaturatedCross : ∀ t ∈ T, dg G S t = 2 * q - 2 := by
    intro t ht
    have hsplit := dg_union_of_disjoint (G := G) hST t
    rw [hcover] at hsplit
    have hd := hsaturatedTotal t ht
    have hz := hTzero t ht
    omega
  have hcard : #S = #T + 1 := by dsimp [k] at hk1; omega
  have horder : #S + #T = Fintype.card V := by
    rw [← card_union_of_disjoint hST, hcover, card_univ]
  exact critical_saturated_pair q hq S T hST hcard (by omega) hcap hsaturatedCross

set_option pp.proofs false in
#print neq_of_empty_barrier
#print axioms ec_union_right
#print axioms deficiency_union
#print axioms zero_deficiency_degree
#print axioms neq_of_empty_barrier
end Erdos585.NEQ
