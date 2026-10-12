import Openmath.Proofs.PaperSupport.B5PairTools

/- 

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.Bq
open QB4 B5
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def Sparse (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) : Prop :=
  ∀ X ⊆ U, ∀ Y ⊆ W, 3 ≤ #X + #Y → #X + #Y < #U + #W →
    2 * (q : ℤ) + 2 ≤ potential (2 * (q : ℤ) - 2) G X Y

lemma pred_cast {q : ℕ} (hq : 5 ≤ q) : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
  omega

omit [DecidableEq V] in
lemma potential_comm (D : ℤ) (X Y : Finset V) :
    potential D G X Y = potential D G Y X := by
  unfold potential
  rw [ec_comm]
  ring

omit [DecidableEq V] in
lemma Sparse.swap {q : ℕ} {U W : Finset V} (h : Sparse q G U W) : Sparse q G W U := by
  intro Y hY X hX hlarge hproper
  rw [potential_comm]
  exact h X hX Y hY (by omega) (by omega)

/-- Generic boundary-order simplicity, not a numerical B5 order bound. -/
lemma boundary_order {q : ℕ} {U W : Finset V} (hq : 5 ≤ q)
    (hn : 2 * q ≤ #U + #W)
    (he : (q - 1) * (#U + #W) ≤ ec G U W + q) :
    2 * q + 1 ≤ #U + #W := by
  by_contra! hsmall
  have hsize : #U + #W = 2 * q := by omega
  have hp := ec_le_product (G := G) U W
  have hqZ : 5 ≤ (q : ℤ) := by exact_mod_cast hq
  have hs := sq_nonneg ((#U : ℤ) - #W)
  have hprod : 0 < (q : ℤ) * ((q : ℤ) - 3) := mul_pos (by omega) (by omega)
  zify at he hp hsize
  rw [pred_cast hq] at he
  nlinarith

/-- Every tiny actual support, without an order-one/two floor premise. -/
lemma small_potential {q : ℕ} {X Y : Finset V} (hq : 5 ≤ q)
    (hn : 3 ≤ #X + #Y) (hsmall : #X + #Y ≤ 2 * q - 1) :
    2 * (q : ℤ) + 2 ≤ potential (2 * (q : ℤ) - 2) G X Y := by
  have hp := ec_le_product (G := G) X Y
  have hqZ : 5 ≤ (q : ℤ) := by exact_mod_cast hq
  zify at hn hsmall hp
  have hs := sq_nonneg ((#X : ℤ) - #Y)
  have hi : (((#X : ℤ) + #Y) - 3) *
      (((#X : ℤ) + #Y) - (2 * (q : ℤ) - 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
  have hj : 0 ≤ ((q : ℤ) - 3) * (((#X : ℤ) + #Y) - 3) :=
    mul_nonneg (by omega) (by omega)
  unfold potential
  nlinarith

omit [DecidableEq V] in
lemma ec_lower_of_min {k : ℕ} {X U W : Finset V} (hX : X ⊆ U)
    (hmin : ∀ a ∈ U, k ≤ dg G W a) : k * #X ≤ ec G X W := by
  calc k * #X = ∑ _a ∈ X, k := by simp [sum_const, mul_comm]
    _ ≤ ec G X W := sum_le_sum fun a ha => hmin a (hX ha)

/-- All original balanced cuts are derived, not supplied to this producer. -/
theorem balanced_factor {q : ℕ} {P Q : Finset V} (hq : 5 ≤ q)
    (hbal : #P = #Q)
    (hminP : ∀ p ∈ P, q ≤ dg G Q p) (hcapP : ∀ p ∈ P, dg G Q p ≤ 2 * q - 2)
    (hminQ : ∀ w ∈ Q, q ≤ dg G P w) (hcapQ : ∀ w ∈ Q, dg G P w ≤ 2 * q - 2)
    (hdefP : deficiency (2 * (q : ℤ) - 2) G Q P = q)
    (hdefQ : deficiency (2 * (q : ℤ) - 2) G P Q = q)
    (hs : Sparse q G P Q) : FactorOn q G P Q := by
  apply B5Factor.exists_target_factor (k := q) P Q hbal
  intro X hX Y hY
  by_contra! hbad
  have hbadN := hbad
  have htn : #Y + 1 ≤ #X := by
    by_contra! hn
    have hm := Nat.mul_le_mul_left q (by omega : #X ≤ #Y)
    omega
  have hcapPi : ∀ p ∈ P, (dg G Q p : ℤ) ≤ 2 * (q : ℤ) - 2 := fun p hp => by
    have hd := hcapP p hp
    omega
  have hcapQi : ∀ w ∈ Q, (dg G P w : ℤ) ≤ 2 * (q : ℤ) - 2 := fun w hw => by
    have hd := hcapQ w hw
    omega
  have ha0 := deficiency_nonneg (G := G) (2 * (q : ℤ) - 2)
    (fun p hp => hcapPi p (hX hp))
  have hb0 := deficiency_nonneg (G := G) (2 * (q : ℤ) - 2)
    (fun w hw => hcapQi w (hY hw))
  have haq := deficiency_le_subset (G := G) (2 * (q : ℤ) - 2) hX hcapPi
  rw [hdefP] at haq
  have hbq := deficiency_le_subset (G := G) (2 * (q : ℤ) - 2) hY hcapQi
  rw [hdefQ] at hbq
  have hxsplit := ec_sdiff_add_right (G := G) hY X
  have hysplit := ec_sdiff_add_left (G := G) hX Y
  have hxcount := card_sdiff_add_card_eq_card hX
  have hycount := card_sdiff_add_card_eq_card hY
  have hda := deficiency_eq (G := G) (2 * (q : ℤ) - 2) Q X
  have hdb := deficiency_eq (G := G) (2 * (q : ℤ) - 2) P Y
  have hcomm := ec_comm (G := G) P Y
  have hqZ : 5 ≤ (q : ℤ) := by exact_mod_cast hq
  zify at hbad hxsplit hysplit hxcount hycount hbal hcomm htn
  have hsur : (#X : ℤ) = #Y + 1 := by
    have ht2 : (#X : ℤ) - #Y < 2 := by
      by_contra! ht
      have hprod : 0 ≤ ((q : ℤ) - 2) * (((#X : ℤ) - #Y) - 2) :=
        mul_nonneg (by omega) (by omega)
      have hi : 0 ≤ (ec G (P \ X) Y : ℤ) := Nat.cast_nonneg _
      nlinarith
    omega
  have hqscale : (q : ℤ) * (#X : ℤ) = q * #Y + q := by rw [hsur]; ring
  have hc : ec G X (Q \ Y) ≤ q - 1 := by omega
  have hYne : Y.Nonempty := by
    by_contra hy
    have hye : Y = ∅ := not_nonempty_iff_eq_empty.mp hy
    have hm := ec_lower_of_min (G := G) hX hminP
    simp only [hye, sdiff_empty, card_empty, mul_zero, add_zero] at hbadN
    omega
  have hXcne : (P \ X).Nonempty := by
    by_contra hx
    have hxe : P \ X = ∅ := not_nonempty_iff_eq_empty.mp hx
    have hqe : #(Q \ Y) = 1 := by simp only [hxe, card_empty] at hxcount; omega
    have hm := ec_lower_of_min (G := G) (sdiff_subset : Q \ Y ⊆ Q) hminQ
    have hxc : X = P := subset_antisymm hX (sdiff_eq_empty_iff_subset.mp hxe)
    rw [ec_comm] at hm
    rw [hxc] at hc
    simp only [hqe, mul_one] at hm
    omega
  have hlarge : 3 ≤ #(P \ X) + #(Q \ Y) := by
    have hp := card_pos.mpr hXcne
    omega
  have hproper : #(P \ X) + #(Q \ Y) < #P + #Q := by
    have hy := card_pos.mpr hYne
    omega
  have hsp := hs (P \ X) sdiff_subset (Q \ Y) sdiff_subset hlarge hproper
  have hallX := ec_sdiff_add_left (G := G) hX Q
  have hallY := ec_sdiff_add_right (G := G) hY (P \ X)
  have hdP := deficiency_eq (G := G) (2 * (q : ℤ) - 2) Q P
  rw [hdefP] at hdP
  have hDscale : (2 * (q : ℤ) - 2) * (#X : ℤ) =
      (2 * (q : ℤ) - 2) * #Y + (2 * (q : ℤ) - 2) := by rw [hsur]; ring
  zify at hallX hallY hc
  unfold potential at hsp
  nlinarith

/-- The cap and exact count derive the only two critical shore signatures. -/
theorem critical_sorted {q : ℕ} {U W : Finset V} (hq : 5 ≤ q)
    (hUW : Disjoint U W) (hn : 2 * q ≤ #U + #W) (horder : #U ≤ #W)
    (hminU : ∀ a ∈ U, q ≤ dg G W a) (hcapU : ∀ a ∈ U, dg G W a ≤ 2 * q - 2)
    (hminW : ∀ w ∈ W, q ≤ dg G U w) (hcapW : ∀ w ∈ W, dg G U w ≤ 2 * q - 2)
    (he : ec G U W + q = (q - 1) * (#U + #W)) (hs : Sparse q G U W) :
    RegularPairs q G U W := by
  have hcapUi : ∀ a ∈ U, (dg G W a : ℤ) ≤ 2 * (q : ℤ) - 2 := fun a ha => by
    have hd := hcapU a ha
    omega
  have hdU := deficiency_eq (G := G) (2 * (q : ℤ) - 2) W U
  have hdW := deficiency_eq (G := G) (2 * (q : ℤ) - 2) U W
  have hd0 := deficiency_nonneg (G := G) (2 * (q : ℤ) - 2) hcapUi
  have hc := ec_comm (G := G) W U
  have hqZ : 5 ≤ (q : ℤ) := by exact_mod_cast hq
  zify at he horder hn hc
  rw [pred_cast hq] at he
  have hcases : #W = #U ∨ #W = #U + 1 := by
    have ht : (#W : ℤ) - #U < 2 := by
      by_contra! hbad
      have hp : 0 ≤ ((q : ℤ) - 1) * (((#W : ℤ) - #U) - 2) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
    omega
  have hUne : U.Nonempty := by
    by_contra! hnU
    have hu : #U = 0 := card_eq_zero.mpr hnU
    rcases hcases with hh | hh
    · omega
    · omega
  rcases hcases with hbal | hsur
  · have hbalZ : (#W : ℤ) = #U := by exact_mod_cast hbal
    have hdq : deficiency (2 * (q : ℤ) - 2) G W U = q := by
      rw [hbalZ] at he
      nlinarith
    have hdq' : deficiency (2 * (q : ℤ) - 2) G U W = q := by
      rw [hbalZ] at hdW
      nlinarith
    exact (balanced_factor hq hbal.symm hminU hcapU hminW hcapW hdq hdq' hs).regular_pairs
      (by omega) hUne
  · have hsurZ : (#W : ℤ) = #U + 1 := by exact_mod_cast hsur
    have hd1 : deficiency (2 * (q : ℤ) - 2) G W U = 1 := by
      rw [hsurZ] at he
      nlinarith
    have hr : R2Input q G U W :=
      ⟨hUW, hsur, hminU, hcapU, hminW, hcapW, hd1, hs⟩
    obtain ⟨w, hw, hf⟩ := r2_original (G := G) q hq U W hr
    exact hf.regular_pairs (by omega) hUne |>.mono_sets (Subset.refl U) (erase_subset w W)

theorem critical_pair {q : ℕ} {U W : Finset V} (hq : 5 ≤ q)
    (hUW : Disjoint U W) (hn : 2 * q ≤ #U + #W)
    (hminU : ∀ a ∈ U, q ≤ dg G W a) (hcapU : ∀ a ∈ U, dg G W a ≤ 2 * q - 2)
    (hminW : ∀ w ∈ W, q ≤ dg G U w) (hcapW : ∀ w ∈ W, dg G U w ≤ 2 * q - 2)
    (he : ec G U W + q = (q - 1) * (#U + #W)) (hs : Sparse q G U W) :
    RegularPairs q G U W := by
  by_cases horder : #U ≤ #W
  · exact critical_sorted hq hUW hn horder hminU hcapU hminW hcapW he hs
  · have hn' : 2 * q ≤ #W + #U := by omega
    have he' : ec G W U + q = (q - 1) * (#W + #U) := by
      rw [ec_comm, add_comm (#W) (#U)]
      exact he
    exact (critical_sorted hq hUW.symm hn' (by omega) hminW hcapW hminU hcapU
      he' hs.swap).swap

lemma ec_erase_add {U W : Finset V} {a : V} (ha : a ∈ U) :
    ec G (U.erase a) W + dg G W a = ec G U W := by
  exact sum_erase_add _ _ ha

/-- The induction ranges over all original graphs and actual finite shores.
Neither degree minima, sparsity, critical signatures nor factors are supplied. -/
theorem dense_pair_aux (q : ℕ) (hq : 5 ≤ q) (n : ℕ) :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V),
      #U + #W = n → Disjoint U W → 2 * q ≤ #U + #W →
      (∀ a ∈ U, dg G W a ≤ 2 * q - 2) →
      (∀ w ∈ W, dg G U w ≤ 2 * q - 2) →
      (q - 1) * (#U + #W) ≤ ec G U W + q → RegularPairs q G U W := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ U W hnum hUW hn hcapU hcapW he
    classical
    by_contra hnone
    have hlarge := boundary_order (G := G) hq hn he
    have hnontrunc : q ≤ (q - 1) * (#U + #W) := by
      have hm := Nat.mul_le_mul_right (#U + #W) (by omega : 1 ≤ q - 1)
      simp only [one_mul] at hm
      omega
    let m := (q - 1) * (#U + #W) - q
    have hm : m ≤ ec G U W := by dsimp [m]; omega
    obtain ⟨K, hKG, hmK⟩ := thin_pair (G := G) hUW m hm
    let _ : DecidableRel K.Adj := Classical.decRel _
    have heK : ec K U W + q = (q - 1) * (#U + #W) := by
      rw [hmK]
      dsimp [m]
      omega
    have hnoneK : ¬ RegularPairs q K U W := fun h => hnone (h.mono_graph hKG)
    have hcapUK : ∀ a ∈ U, dg K W a ≤ 2 * q - 2 := fun a ha =>
      (dg_mono_graph hKG W a).trans (hcapU a ha)
    have hcapWK : ∀ w ∈ W, dg K U w ≤ 2 * q - 2 := fun w hw =>
      (dg_mono_graph hKG U w).trans (hcapW w hw)
    have hsmaller : ∀ X ⊆ U, ∀ Y ⊆ W, 2 * q ≤ #X + #Y →
        #X + #Y < #U + #W → (q - 1) * (#X + #Y) ≤ ec K X Y + q → False := by
      intro X hX Y hY horder hlt hdense
      have hf := ih (#X + #Y) (by omega) K X Y rfl (hUW.mono hX hY) horder
        (fun x hx => (dg_mono (G := K) hY x).trans (hcapUK x (hX hx)))
        (fun y hy => (dg_mono (G := K) hX y).trans (hcapWK y (hY hy))) hdense
      exact hnoneK (hf.mono_sets hX hY)
    have hminU : ∀ a ∈ U, q ≤ dg K W a := by
      intro a ha
      by_contra! hlow
      have hcard := card_erase_add_one ha
      have hec := ec_erase_add (G := K) (W := W) ha
      have hprod : (q - 1) * (#(U.erase a) + #W) + (q - 1) =
          (q - 1) * (#U + #W) := by
        calc _ = (q - 1) * ((#(U.erase a) + #W) + 1) := by ring
          _ = _ := by congr 1; omega
      exact hsmaller (U.erase a) (erase_subset a U) W (Subset.refl W)
        (by omega) (by omega) (by omega)
    have hminW : ∀ w ∈ W, q ≤ dg K U w := by
      intro w hw
      by_contra! hlow
      have hcard := card_erase_add_one hw
      have hec := ec_erase_add (G := K) (W := U) hw
      rw [ec_comm (G := K) (W.erase w) U, ec_comm (G := K) W U] at hec
      have hprod : (q - 1) * (#U + #(W.erase w)) + (q - 1) =
          (q - 1) * (#U + #W) := by
        calc _ = (q - 1) * ((#U + #(W.erase w)) + 1) := by ring
          _ = _ := by congr 1; omega
      exact hsmaller U (Subset.refl U) (W.erase w) (erase_subset w W)
        (by omega) (by omega) (by omega)
    have hs : Sparse q K U W := by
      intro X hX Y hY hthree hlt
      by_cases hsmall : #X + #Y ≤ 2 * q - 1
      · exact small_potential (G := K) hq hthree hsmall
      · by_contra! hfail
        have hpot : potential (2 * (q : ℤ) - 2) K X Y =
            2 * (((q - 1) * (#X + #Y) : ℕ) : ℤ) - 2 * (ec K X Y : ℤ) := by
          unfold potential
          push_cast
          rw [pred_cast hq]
          ring
        rw [hpot] at hfail
        have heXY : (q - 1) * (#X + #Y) ≤ ec K X Y + q := by omega
        exact hsmaller X hX Y hY (by omega) hlt heXY
    exact hnoneK (critical_pair hq hUW hn hminU hcapUK hminW hcapWK heK hs)

theorem dense_pair {q : ℕ} (hq : 5 ≤ q) (U W : Finset V)
    (hUW : Disjoint U W) (hn : 2 * q ≤ #U + #W)
    (hcapU : ∀ a ∈ U, dg G W a ≤ 2 * q - 2)
    (hcapW : ∀ w ∈ W, dg G U w ≤ 2 * q - 2)
    (he : (q - 1) * (#U + #W) ≤ ec G U W + q) : RegularPairs q G U W := by
  exact dense_pair_aux q hq (#U + #W) G U W rfl hUW hn hcapU hcapW he

open scoped Classical in
/-- Every natural q>=5; the literal nontruncated edge threshold; actual
nonempty q-regular original subgraph on arbitrary support. -/
theorem bq (q : ℕ) (hq : 5 ≤ q) {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hbip : G.IsBipartite) (hdeg : G.maxDegree ≤ 2 * q - 2)
    (hn : 2 * q ≤ Fintype.card V)
    (he : (q - 1) * Fintype.card V - q ≤ G.edgeSet.ncard) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  classical
  obtain ⟨o⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨U, W, _, hUW, hcov, hbw⟩ := exists_sides hbip o
  have hcard : #U + #W = Fintype.card V := by
    rw [← card_union_of_disjoint hUW, hcov, card_univ]
  have hec := ec_eq_ncard hbw
  have hnontrunc : q ≤ (q - 1) * Fintype.card V := by
    have hm := Nat.mul_le_mul_right (Fintype.card V) (by omega : 1 ≤ q - 1)
    simp only [one_mul] at hm
    omega
  have hePair : (q - 1) * (#U + #W) ≤ ec G U W + q := by
    rw [hcard, hec]
    omega
  have hr : RegularPairs q G U W :=
    dense_pair hq U W hUW (by omega)
      (fun a _ => (dg_le_maxDegree W a).trans hdeg)
      (fun w _ => (dg_le_maxDegree U w).trans hdeg) hePair
  exact exists_subgraph_of_regularPairs hUW hr

#print bq
#print axioms pred_cast
#print axioms potential_comm
#print axioms Sparse.swap
#print axioms boundary_order
#print axioms small_potential
#print axioms ec_lower_of_min
#print axioms balanced_factor
#print axioms critical_sorted
#print axioms critical_pair
#print axioms ec_erase_add
#print axioms dense_pair_aux
#print axioms dense_pair
#print axioms bq
end Erdos585.Bq
