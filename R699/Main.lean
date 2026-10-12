import R691.Main
import H3Unequal.Main

/-! Proper-Q0 cut argument from R394, adapting original-incidence proof code from R653. -/
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.Omit1Q0CutChainR699
open QB4 B5 L34 H3Unequal AllHTopCritical
open Omit1PrefixR691
universe u
variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V} {q : ℕ} {A B X Y : Finset V}

/-- Literal Q0 hypotheses, with no supplied negative cut or chain. -/
structure Host (q : ℕ) (G : SimpleGraph V) (A B : Finset V) : Prop
    extends Omit1PrefixR691.Host q 0 G A B where
  min_degree : ∀ v : V, q ≤ G.degree v
  no_regular : ¬ ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q

namespace Host
variable (host : Host q G A B)
include host
lemma minA (v : V) (hv : v ∈ A) : q ≤ dg G B v := by
  rw [dg_eq_degree host.bipartite hv]; exact host.min_degree v
lemma minB (v : V) (hv : v ∈ B) : q ≤ dg G A v := by
  rw [dg_eq_degree host.bipartite.symm hv]; exact host.min_degree v
lemma capA (v : V) (hv : v ∈ A) : dg G B v ≤ 2*q-2 := by
  rw [dg_eq_degree host.bipartite hv]; exact host.cap v
lemma capB (v : V) (hv : v ∈ B) : dg G A v ≤ 2*q-2 := by
  rw [dg_eq_degree host.bipartite.symm hv]; exact host.cap v
lemma capA_int (v : V) (hv : v ∈ A) : (dg G B v : ℤ) ≤ 2*q-2 :=
  Omit1PrefixR691.capA host.toHost hv
lemma capB_int (v : V) (hv : v ∈ B) : (dg G A v : ℤ) ≤ 2*q-2 :=
  Omit1PrefixR691.capB host.toHost hv
lemma shore_order : #A + #B = Fintype.card V := by
  have hc := card_union_of_disjoint host.disjoint
  rw [host.cover, card_univ] at hc
  exact hc.symm
lemma deficiency_A : deficiency (2*(q : ℤ)-2) G B A = 3*(q : ℤ)-31 := by
  rw [deficiency_eq]
  have ht := host.total
  unfold coreDefect at ht
  have hb := host.balanced
  zify at hb
  nlinarith
lemma paired_floor {X Y : Finset V} (hX : X ⊆ A) (hY : Y ⊆ B)
    (hl : 3 ≤ #X+#Y) (hp : #X+#Y < Fintype.card V) :
    3*(q : ℤ)-30 ≤ coreDefect q G X Y := by
  have hd := host.disjoint.mono hX hY
  have hc := card_union_of_disjoint hd
  have hf := host.proper (X∪Y) (by omega) (by omega)
  rw [induced_edges_eq_ec host.disjoint host.bipartite hX hY, hc] at hf
  simp only [Nat.cast_add] at hf
  unfold coreDefect
  omega
end Host

/-- Actual original rectangles of the arbitrary input cut. -/
structure Conclusion (q : ℕ) (G : SimpleGraph V) (A B X Y : Finset V) : Prop where
  imbalance : (#X : ℤ) + #Y - #B = 2
  forward : (ec G X Y : ℤ) = 2 * (q : ℤ) - 1
  reverse : (ec G (A \ X) (B \ Y) : ℤ) = (q : ℤ) - 28
  scar_A : deficiency (2 * (q : ℤ) - 2) G B (A \ X) = 0
  scar_B : deficiency (2 * (q : ℤ) - 2) G A (B \ Y) = 0
  first_deficit : coreDefect q G X (B \ Y) = 3 * (q : ℤ) - 30
  second_deficit : coreDefect q G (A \ X) Y = 3 * (q : ℤ) - 30
  first_eligible : 2 * q ≤ #X + #(B \ Y)
  second_eligible : 2 * q ≤ #(A \ X) + #Y
  first_proper : #X + #(B \ Y) < Fintype.card V
  second_proper : #(A \ X) + #Y < Fintype.card V
  first_actual_support : 2 * q ≤ #(X ∪ (B \ Y)) ∧
    #(X ∪ (B \ Y)) < Fintype.card V
  second_actual_support : 2 * q ≤ #((A \ X) ∪ Y) ∧
    #((A \ X) ∪ Y) < Fintype.card V
  saturated_A : ∀ v ∈ A \ X, G.degree v = 2 * q - 2
  saturated_B : ∀ v ∈ B \ Y, G.degree v = 2 * q - 2

lemma rectangle_lower (host : Host q G A B) (hX : X ⊆ A) (hY : Y ⊆ B) :
    (q : ℤ) * #X ≤ (#X : ℤ) * #(B \ Y) + (ec G X Y : ℤ) := by
  have hm := Bq.ec_lower_of_min (G := G) hX host.minA
  have hs := ec_sdiff_add_right (G := G) hY X
  have hp := AllHTopCritical.ec_le_product (G := G) X (B \ Y)
  zify at hm hs hp
  nlinarith

/-- Every floor uses its actual original order guard. No canonical cut is supplied. -/
theorem all_violating_cuts (host : Host q G A B)
    (hX : X ⊆ A) (hY : Y ⊆ B)
    (violation : (ec G X Y : ℤ) <
      (q : ℤ) * ((#X : ℤ) + #Y - #B)) : Conclusion q G A B X Y := by
  let k : ℤ := (#X : ℤ) + #Y - #B
  let dA := deficiency (2 * (q : ℤ) - 2) G B (A \ X)
  let dB := deficiency (2 * (q : ℤ) - 2) G A (B \ Y)
  have hq : (16384 : ℤ) ≤ q := by exact_mod_cast host.large
  have ca := card_sdiff_add_card_eq_card hX
  have cb := card_sdiff_add_card_eq_card hY
  have bal := host.balanced
  have ord := host.shore_order
  zify at ca cb bal ord
  have kX : (#X : ℤ) = #(B \ Y) + k := by dsimp [k]; omega
  have kY : (#Y : ℤ) = #(A \ X) + k := by dsimp [k]; omega
  have da0 : 0 ≤ dA := deficiency_nonneg _
    (fun v hv => host.capA_int v (sdiff_subset hv))
  have db0 : 0 ≤ dB := deficiency_nonneg _
    (fun v hv => host.capB_int v (sdiff_subset hv))
  have sx := ec_sdiff_add_right (G := G) hY X
  have sv := ec_sdiff_add_right (G := G) hY (A \ X)
  have sa := ec_sdiff_add_left (G := G) hX B
  have st := ec_sdiff_add_left (G := G) hX (B \ Y)
  have da := deficiency_eq (G := G) (2 * (q : ℤ) - 2) B (A \ X)
  have db := deficiency_eq (G := G) (2 * (q : ℤ) - 2) A (B \ Y)
  rw [ec_comm (G := G) (B \ Y) A] at db
  have whole := host.deficiency_A
  rw [deficiency_eq] at whole
  zify at sx sv sa st
  change dA = _ at da
  change dB = _ at db
  have identity : 3 * (q : ℤ) - 31 =
      2 * ((q : ℤ) - 1) * k + (ec G (A \ X) (B \ Y) : ℤ) +
        dA + dB - (ec G X Y : ℤ) := by
    nlinarith
  have x0 : 0 ≤ (ec G X Y : ℤ) := Nat.cast_nonneg _
  have z0 : 0 ≤ (ec G (A \ X) (B \ Y) : ℤ) := Nat.cast_nonneg _
  change (ec G X Y : ℤ) < (q : ℤ) * k at violation
  have kp : 1 ≤ k := by
    by_contra! hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (show (0 : ℤ) ≤ q by omega)
      (show k ≤ 0 by omega)
    nlinarith only [hm, violation, x0]
  have kle : k ≤ 2 := by
    by_contra! hn
    have hm := mul_nonneg (show (0 : ℤ) ≤ (q : ℤ) - 2 by omega)
      (show 0 ≤ k - 3 by omega)
    nlinarith only [identity, violation, hm, da0, db0, z0, hq]
  have lowerX := rectangle_lower host hX hY
  have lowerY : (q : ℤ) * #Y ≤ (#Y : ℤ) * #(A \ X) + (ec G X Y : ℤ) := by
    have hm := Bq.ec_lower_of_min (G := G) hY host.minB
    have hs := ec_sdiff_add_right (G := G) hX Y
    have hp := AllHTopCritical.ec_le_product (G := G) Y (A \ X)
    rw [ec_comm (G := G) Y X] at hs
    zify at hm hs hp
    nlinarith
  have Xlarge : (q : ℤ) + 1 ≤ #X := by
    by_contra! hn
    have hm := mul_nonneg (show (0 : ℤ) ≤ (#X : ℤ) - k by omega)
      (show 0 ≤ (q : ℤ) - #X by omega)
    nlinarith only [lowerX, kX, violation, hm]
  have Ylarge : (q : ℤ) + 1 ≤ #Y := by
    by_contra! hn
    have hm := mul_nonneg (show (0 : ℤ) ≤ (#Y : ℤ) - k by omega)
      (show 0 ≤ (q : ℤ) - #Y by omega)
    nlinarith only [lowerY, kY, violation, hm]
  have eligible1 : 2 * q ≤ #X + #(B \ Y) := by omega
  have eligible2 : 2 * q ≤ #(A \ X) + #Y := by omega
  have proper1 : #X + #(B \ Y) < Fintype.card V := by omega
  have proper2 : #(A \ X) + #Y < Fintype.card V := by omega
  have floor1 := host.paired_floor hX (sdiff_subset : B \ Y ⊆ B) (by omega) proper1
  have floor2 := host.paired_floor (sdiff_subset : A \ X ⊆ A) hY (by omega) proper2
  have diagonal1 : coreDefect q G X (B \ Y) =
      ((q : ℤ) - 1) * k + (ec G (A \ X) (B \ Y) : ℤ) + dB := by
    unfold coreDefect
    nlinarith only [kX, db, st]
  have diagonal2 : coreDefect q G (A \ X) Y =
      ((q : ℤ) - 1) * k + (ec G (A \ X) (B \ Y) : ℤ) + dA := by
    unfold coreDefect
    nlinarith only [kY, da, sv]
  rw [diagonal1] at floor1
  rw [diagonal2] at floor2
  have keq : k = 2 := by
    by_contra hn
    have hk : k = 1 := by omega
    rw [hk] at identity violation floor1 floor2
    nlinarith only [identity, violation, floor1, floor2, da0, db0]
  have rigidity : (ec G X Y : ℤ) = 2 * (q : ℤ) - 1 ∧
      (ec G (A \ X) (B \ Y) : ℤ) = (q : ℤ) - 28 ∧ dA = 0 ∧ dB = 0 := by
    rw [keq] at identity violation floor1 floor2
    constructor
    · nlinarith only [identity, violation, floor1, floor2, da0, db0]
    constructor
    · nlinarith only [identity, violation, floor1, floor2, da0, db0]
    constructor <;> nlinarith only [identity, violation, floor1, floor2, da0, db0]
  refine ⟨keq, rigidity.1, rigidity.2.1, rigidity.2.2.1, rigidity.2.2.2,
    ?_, ?_, eligible1, eligible2, proper1, proper2, ?_, ?_, ?_, ?_⟩
  · rw [diagonal1, keq, rigidity.2.1, rigidity.2.2.2]
    ring
  · rw [diagonal2, keq, rigidity.2.1, rigidity.2.2.1]
    ring
  · rw [card_union_of_disjoint (host.disjoint.mono hX sdiff_subset)]
    exact ⟨eligible1, proper1⟩
  · rw [card_union_of_disjoint (host.disjoint.mono sdiff_subset hY)]
    exact ⟨eligible2, proper2⟩
  · intro v hv
    have hz : deficiency ((2 * q - 2 : ℕ) : ℤ) G B (A \ X) = 0 := by
      have cast : ((2 * q - 2 : ℕ) : ℤ) = 2 * (q : ℤ) - 2 := by omega
      rw [cast]
      exact rigidity.2.2.1
    have hd := saturated_of_zero (fun w hw => host.capA w (sdiff_subset hw)) hz hv
    rw [dg_eq_degree host.bipartite (sdiff_subset hv)] at hd
    exact hd
  · intro v hv
    have hz : deficiency ((2 * q - 2 : ℕ) : ℤ) G A (B \ Y) = 0 := by
      have cast : ((2 * q - 2 : ℕ) : ℤ) = 2 * (q : ℤ) - 2 := by omega
      rw [cast]
      exact rigidity.2.2.2
    have hd := saturated_of_zero (fun w hw => host.capB w (sdiff_subset hw)) hz hv
    rw [dg_eq_degree host.bipartite.symm (sdiff_subset hv)] at hd
    exact hd



/-- All geometry refers to this literal original vertex set. -/
structure CutData (q : ℕ) (G : SimpleGraph V) (A B S : Finset V) : Prop where
  value : g q G A B S = -1
  imbalance : k A B S = 2
  forward : (ec G (A ∩ S) (B \ S) : ℤ) = 2*(q : ℤ)-1
  reverse : (ec G (A \ S) (B ∩ S) : ℤ) = (q : ℤ)-28
  captured : sA q G A B S = 3*(q : ℤ)-31
  scar_B : sB q G A B S = 0
  tight : f q G A B S = 3*(q : ℤ)-30
  tight_complement : f q G A B (univ \ S) = 3*(q : ℤ)-30
  order : 2*q ≤ #S
  complement_order : 2*q ≤ #(univ \ S)
  proper : #S < Fintype.card V
  complement_proper : #(univ \ S) < Fintype.card V
  saturated_A : ∀ v ∈ A \ S, G.degree v = 2*q-2
  saturated_B : ∀ v ∈ B ∩ S, G.degree v = 2*q-2

variable (host : Host q G A B)
include host

lemma all_negative (S : Finset V) (hn : g q G A B S < 0) :
    CutData q G A B S := by
  have bs : B \ (B \ S) = B ∩ S := by ext x; simp
  have ax : A \ (A ∩ S) = A \ S := by ext x; simp
  have cb := card_sdiff_add_card_eq_card (inter_subset_left : B ∩ S ⊆ B)
  have bs' : B \ (B ∩ S) = B \ S := by ext x; simp
  rw [bs'] at cb
  have vi : (ec G (A ∩ S) (B \ S) : ℤ) <
      (q : ℤ)*((#(A ∩ S) : ℤ)+#(B \ S)-#B) := by
    unfold g k at hn
    zify at cb
    nlinarith
  have r := all_violating_cuts host inter_subset_left sdiff_subset vi
  rcases r with ⟨ri,rf,rr,ra,rb,rt,rc,re1,re2,rp1,rp2,ro1,ro2,rs1,rs2⟩
  simp only [bs, ax] at rr ra rb rt rc re1 re2 rp1 rp2 ro1 ro2 rs1 rs2
  have partition := support_partition host.toHost S
  have cp : (A \ S) ∪ (B \ S) = univ \ S := by
    rw [← union_sdiff_distrib, host.cover]
  have ki : k A B S = 2 := by
    have hi := ri
    unfold k
    zify at cb
    omega
  have va : g q G A B S = -1 := by rw [g, ki, rf]; ring
  have ti : f q G A B S = 3*(q : ℤ)-30 := rt
  have tc : f q G A B (univ \ S) = 3*(q : ℤ)-30 := by
    have ac : A ∩ (univ \ S) = A \ S := by ext x; simp
    have bc : B ∩ (univ \ S) = B \ S := by ext x; simp
    simpa only [f, ac, bc] using rc
  have cap : sA q G A B S = 3*(q : ℤ)-31 := by
    have ident := cut_identity (q := q) (G := G) (A := A) (B := B) S
    omega
  have o := ro1
  rw [partition] at o
  have co := ro2
  rw [cp] at co
  exact ⟨va, ki, rf, rr, cap, rb, ti, tc,
    o.1, co.1, o.2, co.2, rs1, rs2⟩

/-- Deficiency one is proved for every original cut, not supplied. -/
theorem all_cut_lower (S : Finset V) : -1 ≤ g q G A B S := by
  by_cases hn : g q G A B S < 0
  · exact le_of_eq (all_negative host S hn).value.symm
  · omega

/-- Literal Noq and the original unit-edge factor criterion manufacture a cut. -/
theorem exists_negative : ∃ S : Finset V, g q G A B S < 0 := by
  by_contra! hn
  have hcut : ∀ X ⊆ A, ∀ C ⊆ B,
      q * #X ≤ ec G X (B \ C) + q * #C := by
    intro X hX C hC
    have ha : A ∩ (X ∪ C) = X := by
      ext x
      have hd := Finset.disjoint_left.mp host.disjoint
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hx, hxX | hxC⟩
        · exact hxX
        · exact False.elim (hd hx (hC hxC))
      · intro hx; exact ⟨hX hx, Or.inl hx⟩
    have hb : B ∩ (X ∪ C) = C := by
      ext x
      have hd := Finset.disjoint_left.mp host.disjoint
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hx, hxX | hxC⟩
        · exact False.elim (hd (hX hxX) hx)
        · exact hxC
      · intro hx; exact ⟨hC hx, Or.inr hx⟩
    have hbc : B \ (X ∪ C) = B \ C := by
      ext x
      have hd := Finset.disjoint_left.mp host.disjoint
      simp only [mem_sdiff, mem_union]
      constructor
      · tauto
      · rintro ⟨hx, hc⟩; exact ⟨hx, fun hh => hh.elim (fun hxX => hd (hX hxX) hx) hc⟩
    have hs := hn (X ∪ C)
    rw [g, k, ha, hb, hbc] at hs
    zify
    nlinarith
  have fac : FactorOn q G A B := B5Factor.exists_target_factor A B host.balanced hcut
  have hq : 0 < q := by have h := host.large; omega
  have hA : A.Nonempty := by
    by_contra he
    have ae : A = ∅ := not_nonempty_iff_eq_empty.mp he
    have ht := host.total
    simp [ae, coreDefect, ec] at ht
    have hb := host.balanced
    rw [ae, card_empty] at hb
    rw [← hb] at ht
    have hlarge := host.large
    norm_num at ht
    omega
  obtain ⟨H, _, hne, hreg⟩ := factor_exact_subgraph hq hA host.disjoint fac
  exact host.no_regular ⟨H, hne, hreg⟩

lemma internal_min_left {X Y : Finset V} (hX : X ⊆ A) (hY : Y ⊆ B)
    (hl : 2*q ≤ #X+#Y) (hp : #X+#Y < Fintype.card V)
    (hf : coreDefect q G X Y = 3*(q : ℤ)-30) {v : V} (hv : v ∈ X) :
    q-1 ≤ dg G Y v := by
  have hq := host.large
  have hs := host.paired_floor ((erase_subset v X).trans hX) hY
    (by have hc := card_erase_add_one hv; omega)
    (by have hc := card_erase_le (a := v) (s := X); omega)
  have he := potential_erase_left (G := G) (2*(q : ℤ)-2) hv Y
  have ht := twice_coreDefect (G := G) q X Y
  have hu := twice_coreDefect (G := G) q (X.erase v) Y
  have hz : (q : ℤ)-1 ≤ dg G Y v := by nlinarith
  omega

lemma internal_min_right {X Y : Finset V} (hX : X ⊆ A) (hY : Y ⊆ B)
    (hl : 2*q ≤ #X+#Y) (hp : #X+#Y < Fintype.card V)
    (hf : coreDefect q G X Y = 3*(q : ℤ)-30) {v : V} (hv : v ∈ Y) :
    q-1 ≤ dg G X v := by
  have hq := host.large
  have hs := host.paired_floor hX ((erase_subset v Y).trans hY)
    (by have hc := card_erase_add_one hv; omega)
    (by have hc := card_erase_le (a := v) (s := Y); omega)
  have he := potential_erase_left (G := G) (2*(q : ℤ)-2) hv X
  rw [coreDefect_symm (G := G) X Y] at hf
  rw [coreDefect_symm (G := G) X (Y.erase v)] at hs
  have ht := twice_coreDefect (G := G) q Y X
  have hu := twice_coreDefect (G := G) q (Y.erase v) X
  have hz : (q : ℤ)-1 ≤ dg G X v := by nlinarith
  omega


lemma diagonal_degree_A (S : Finset V) (hn : g q G A B S < 0)
    {v : V} (hv : v ∈ A ∩ S) : q-1 ≤ dg G (B ∩ S) v := by
  have r := all_negative host S hn
  have hc := support_card host.toHost S
  have hl := r.order
  have hp := r.proper
  exact internal_min_left host inter_subset_left inter_subset_left
    (by omega) (by omega) r.tight hv

lemma diagonal_degree_B_complement (S : Finset V) (hn : g q G A B S < 0)
    {v : V} (hv : v ∈ B \ S) : q-1 ≤ dg G (A \ S) v := by
  have r := all_negative host S hn
  have hc := support_card host.toHost (univ \ S)
  have hf := r.tight_complement
  have ac : A ∩ (univ \ S) = A \ S := by ext x; simp
  have bc : B ∩ (univ \ S) = B \ S := by ext x; simp
  simp only [f, ac, bc] at hc hf
  have hl := r.complement_order
  have hp := r.complement_proper
  exact internal_min_right host sdiff_subset sdiff_subset
    (by omega) (by omega) hf hv

omit host [Fintype V] in
lemma dg_le_ec {X Y : Finset V} {v : V} (hv : v ∈ X) : dg G Y v ≤ ec G X Y :=
  single_le_sum (fun _ _ => Nat.zero_le _) hv

omit host [Fintype V] in
lemma dg_difference_bound (X Y : Finset V) (v : V) :
    dg G X v ≤ dg G Y v + #(X \ Y) := by
  have hd := dg_sdiff_add (G := G) (inter_subset_left : X ∩ Y ⊆ X) v
  have he : X \ (X ∩ Y) = X \ Y := by ext x; simp
  rw [he] at hd
  have hm := dg_mono (G := G) (inter_subset_right : X ∩ Y ⊆ Y) v
  have hc := dg_le_card (G := G) (X \ Y) v
  omega

/-- Every nonempty actual difference is large enough before any floor is used. -/
lemma difference_order (S T : Finset V) (hs : g q G A B S < 0)
    (ht : g q G A B T < 0) (hne : (S \ T).Nonempty) : 3 ≤ #(S \ T) := by
  by_contra! hn
  obtain ⟨v, hv⟩ := hne
  have hvS := (mem_sdiff.mp hv).1
  have hvT := (mem_sdiff.mp hv).2
  have hq := host.large
  have rs := all_negative host S hs
  have rt := all_negative host T ht
  have hab : v ∈ A ∨ v ∈ B := by
    have hu : v ∈ A ∪ B := by rw [host.cover]; exact mem_univ v
    exact mem_union.mp hu
  rcases hab with ha | hb
  · have lower := diagonal_degree_A host S hs (mem_inter.mpr ⟨ha,hvS⟩)
    have upper := dg_difference_bound (G := G) (B ∩ S) (B ∩ T) v
    have hm := dg_le_ec (G := G) (Y := B ∩ T) (mem_sdiff.mpr ⟨ha,hvT⟩)
    have hc : #((B ∩ S) \ (B ∩ T)) ≤ #(S \ T) := by
      apply card_le_card
      intro x hx
      simp only [mem_sdiff, mem_inter] at hx ⊢
      tauto
    have hr := rt.reverse
    zify at lower upper hm hc hn
    have hqm : ((q-1 : ℕ) : ℤ) = (q : ℤ)-1 := by omega
    rw [hqm] at lower
    omega
  · have lower := diagonal_degree_B_complement host T ht (mem_sdiff.mpr ⟨hb,hvT⟩)
    have upper := dg_difference_bound (G := G) (A \ T) (A \ S) v
    have hm := dg_le_ec (G := G) (Y := A \ S) (mem_inter.mpr ⟨hb,hvS⟩)
    rw [ec_comm (G := G) (B ∩ S) (A \ S)] at hm
    have hc : #((A \ T) \ (A \ S)) ≤ #(S \ T) := by
      apply card_le_card
      intro x hx
      simp only [mem_sdiff] at hx ⊢
      tauto
    have hr := rs.reverse
    zify at lower upper hm hc hn
    have hqm : ((q-1 : ℕ) : ℤ) = (q : ℤ)-1 := by omega
    rw [hqm] at lower
    omega

lemma scar_card_bound_A {Z : Finset V} (hZ : Z ⊆ A) :
    deficiency (2*(q : ℤ)-2) G B Z ≤ ((q : ℤ)-2)*#Z := by
  have hh : ∀ v ∈ Z, 2*(q : ℤ)-2-(dg G B v : ℤ) ≤ (q : ℤ)-2 := by
    intro v hv
    have hm := host.minA v (hZ hv)
    omega
  calc
    _ ≤ ∑ _v ∈ Z, ((q : ℤ)-2) := sum_le_sum hh
    _ = ((q : ℤ)-2)*#Z := by rw [sum_const, nsmul_eq_mul]; ring

lemma scar_card_bound_B {Z : Finset V} (hZ : Z ⊆ B) :
    deficiency (2*(q : ℤ)-2) G A Z ≤ ((q : ℤ)-2)*#Z := by
  have hh : ∀ v ∈ Z, 2*(q : ℤ)-2-(dg G A v : ℤ) ≤ (q : ℤ)-2 := by
    intro v hv
    have hm := host.minB v (hZ hv)
    omega
  calc
    _ ≤ ∑ _v ∈ Z, ((q : ℤ)-2) := sum_le_sum hh
    _ = ((q : ℤ)-2)*#Z := by rw [sum_const, nsmul_eq_mul]; ring

/-- All original A scar lies in the actual intersection of any negative cuts. -/
lemma intersection_order (S T : Finset V) (hs : g q G A B S < 0)
    (ht : g q G A B T < 0) : 3 ≤ #(S ∩ T) := by
  have rs := all_negative host S hs
  have rt := all_negative host T ht
  have hz : deficiency (2*(q : ℤ)-2) G B (A ∩ (S ∩ T)) =
      deficiency (2*(q : ℤ)-2) G B A := by
    apply sum_subset inter_subset_left
    intro v hv hn
    have hnot : v ∉ S ∨ v ∉ T := by
      simp only [mem_inter] at hn
      tauto
    have hd : G.degree v = 2*q-2 := by
      rcases hnot with hS | hT
      · exact rs.saturated_A v (mem_sdiff.mpr ⟨hv,hS⟩)
      · exact rt.saturated_A v (mem_sdiff.mpr ⟨hv,hT⟩)
    rw [dg_eq_degree host.bipartite hv, hd]
    have hq := host.large
    omega
  rw [host.deficiency_A] at hz
  have hb := scar_card_bound_A host (inter_subset_left : A ∩ (S ∩ T) ⊆ A)
  have hc := card_le_card (inter_subset_right : A ∩ (S ∩ T) ⊆ S ∩ T)
  have hq : (16384 : ℤ) ≤ q := by exact_mod_cast host.large
  by_contra! hn
  zify at hc hn
  have hm := mul_nonneg (show (0 : ℤ) ≤ (q : ℤ)-2 by omega)
    (show 0 ≤ 2-(#(A ∩ (S ∩ T)) : ℤ) by omega)
  nlinarith

lemma outer_order (S T : Finset V) (hs : g q G A B S < 0)
    (ht : g q G A B T < 0) : 3 ≤ #((univ \ S) ∩ (univ \ T)) := by
  have rs := all_negative host S hs
  have rt := all_negative host T ht
  let O : Finset V := (univ \ S) ∩ (univ \ T)
  have hz : deficiency (2*(q : ℤ)-2) G A (B ∩ O) =
      deficiency (2*(q : ℤ)-2) G A B := by
    apply sum_subset inter_subset_left
    intro v hv hn
    have hin : v ∈ S ∨ v ∈ T := by
      simp only [O, mem_inter, mem_sdiff, mem_univ] at hn
      tauto
    have hd : G.degree v = 2*q-2 := by
      rcases hin with hS | hT
      · exact rs.saturated_B v (mem_inter.mpr ⟨hv,hS⟩)
      · exact rt.saturated_B v (mem_inter.mpr ⟨hv,hT⟩)
    rw [dg_eq_degree host.bipartite.symm hv, hd]
    have hq := host.large
    omega
  have db : deficiency (2*(q : ℤ)-2) G A B = 3*(q : ℤ)-31 := by
    rw [deficiency_eq, ec_comm (G := G) B A, ← host.balanced]
    have da := host.deficiency_A
    rwa [deficiency_eq] at da
  rw [db] at hz
  have hb := scar_card_bound_B host (inter_subset_left : B ∩ O ⊆ B)
  have hc := card_le_card (inter_subset_right : B ∩ O ⊆ O)
  have hq : (16384 : ℤ) ≤ q := by exact_mod_cast host.large
  change 3 ≤ #O
  by_contra! hn
  zify at hc hn
  have hm := mul_nonneg (show (0 : ℤ) ≤ (q : ℤ)-2 by omega)
    (show 0 ≤ 2-(#(B ∩ O) : ℤ) by omega)
  nlinarith

/-- Every pair of actual negative vertex sets is comparable by inclusion. -/
theorem negative_chain (S T : Finset V) (hs : g q G A B S < 0)
    (ht : g q G A B T < 0) : S ⊆ T ∨ T ⊆ S := by
  by_contra! hn
  have hst : (S \ T).Nonempty := sdiff_nonempty.mpr hn.1
  have hts : (T \ S).Nonempty := sdiff_nonempty.mpr hn.2
  have h1 := intersection_order host S T hs ht
  have h2 := difference_order host S T hs ht hst
  have h3 := difference_order host T S ht hs hts
  have h4 := outer_order host S T hs ht
  have rs := all_negative host S hs
  have hq := host.large
  have band : g q G A B T ≤ (q : ℤ)-1 := by omega
  have fc := four_cell host.toHost T S band (by have h := rs.tight; omega)
    (by have h := rs.tight_complement; omega)
  have e1 : T ∩ S = S ∩ T := inter_comm _ _
  have e2 : T ∩ (univ \ S) = T \ S := by ext x; simp
  have e3 : (univ \ T) ∩ S = S \ T := by ext x; simp [and_comm]
  have e4 : (univ \ T) ∩ (univ \ S) = (univ \ S) ∩ (univ \ T) := inter_comm _ _
  rw [e1,e2,e3,e4] at fc
  omega


omit host in
/-- Exactly all actual original negative source sets, not a selected subfamily. -/
def negativeFamily (q : ℕ) (G : SimpleGraph V) (A B : Finset V) : Finset (Finset V) :=
  univ.filter (fun S => g q G A B S < 0)

omit host in
lemma mem_negativeFamily (S : Finset V) : S ∈ negativeFamily q G A B ↔
    g q G A B S < 0 := by simp [negativeFamily]

/-- Finite extrema belong to the literal family and are themselves nonempty. -/
theorem negative_extrema : ∃ Smin Smax : Finset V,
    g q G A B Smin < 0 ∧ g q G A B Smax < 0 ∧ Smin.Nonempty ∧ Smax.Nonempty ∧
    (∀ S : Finset V, g q G A B S < 0 → Smin ⊆ S ∧ S ⊆ Smax) := by
  have hne : (negativeFamily q G A B).Nonempty := by
    obtain ⟨S,hs⟩ := exists_negative host
    exact ⟨S,(mem_negativeFamily S).mpr hs⟩
  obtain ⟨Smin,hmin,cmin⟩ := (negativeFamily q G A B).exists_min_image
    (fun S : Finset V => #S) hne
  obtain ⟨Smax,hmax,cmax⟩ := (negativeFamily q G A B).exists_max_image
    (fun S : Finset V => #S) hne
  have hsmin := (mem_negativeFamily Smin).mp hmin
  have hsmax := (mem_negativeFamily Smax).mp hmax
  have rmin := all_negative host Smin hsmin
  have rmax := all_negative host Smax hsmax
  have hq := host.large
  have hminord := rmin.order
  have hmaxord := rmax.order
  refine ⟨Smin,Smax,hsmin,hsmax,card_pos.mp (by omega),card_pos.mp (by omega),?_⟩
  intro S hs
  have hS := (mem_negativeFamily S).mpr hs
  constructor
  · rcases negative_chain host Smin S hsmin hs with hrel | hrel
    · exact hrel
    · exact (eq_of_subset_of_card_le hrel (cmin S hS)).symm.subset
  · rcases negative_chain host S Smax hs hsmax with hrel | hrel
    · exact hrel
    · exact (eq_of_subset_of_card_le hrel (cmax S hS)).symm.subset

/-- Original Q0 all-cut rigidity and the nonempty literal negative-set chain. -/
theorem q0_negative_cut_chain :
    (∀ S : Finset V, -1 ≤ g q G A B S) ∧
    (∀ S : Finset V, g q G A B S < 0 → CutData q G A B S) ∧
    (negativeFamily q G A B).Nonempty ∧
    (∀ S T : Finset V, g q G A B S < 0 → g q G A B T < 0 → S ⊆ T ∨ T ⊆ S) ∧
    (∃ Smin Smax : Finset V,
      g q G A B Smin < 0 ∧ g q G A B Smax < 0 ∧ Smin.Nonempty ∧ Smax.Nonempty ∧
      (∀ S : Finset V, g q G A B S < 0 → Smin ⊆ S ∧ S ⊆ Smax)) := by
  refine ⟨all_cut_lower host, all_negative host, ?_, negative_chain host,
    negative_extrema host⟩
  obtain ⟨S,hs⟩ := exists_negative host
  exact ⟨S,(mem_negativeFamily S).mpr hs⟩

#check @all_negative
#print axioms all_negative
#check @all_cut_lower
#print axioms all_cut_lower
#check @exists_negative
#print axioms exists_negative
#check @negative_chain
#print axioms negative_chain
#check @negative_extrema
#print axioms negative_extrema
#check @q0_negative_cut_chain
#print axioms q0_negative_cut_chain
end Erdos585.Omit1Q0CutChainR699
