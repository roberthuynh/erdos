import Openmath.Proofs.PaperSupport.QB6Assembly
import Openmath.Proofs.PaperSupport.QB7TwoReverseV2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Conditional QB7 assembly. The propositions C4Repair, U2Repair and E73Repair
remain explicit assumptions. The closed reverse-two branch uses only the strict V2 producer.
The exact conditional statement and its hypotheses are given below.
-/

open Finset

namespace Erdos585.QB7Conditional

open QB4 QB5 QB7Reduction

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def IndependentOn (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ¬ G.Adj x y

abbrev Sparse7 (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) : Prop :=
  SparseBound G U W 7

structure C4Input (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V) : Prop where
  disjoint : Disjoint U W
  independentU : IndependentOn G U
  independentW : IndependentOn G W
  card : #W = #U + 1
  minU : ∀ x ∈ U, 4 ≤ dg G W x
  capU : ∀ x ∈ U, dg G W x ≤ 6
  minW : ∀ y ∈ W, 4 ≤ dg G U y
  capW : ∀ y ∈ W, dg G U y ≤ 6
  defU : df G W U = 4
  sparse : Sparse7 G U W

structure U2Input (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V) : Prop where
  disjoint : Disjoint U W
  independentU : IndependentOn G U
  independentW : IndependentOn G W
  card : #W = #U + 2
  minU : ∀ x ∈ U, 4 ≤ dg G W x
  capU : ∀ x ∈ U, dg G W x ≤ 6
  minW : ∀ y ∈ W, 4 ≤ dg G U y
  capW : ∀ y ∈ W, dg G U y ≤ 6
  defU : df G W U = 1
  sparse : Sparse7 G U W

structure E73Input (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q A C : Finset V) : Prop where
  disjoint : Disjoint P Q
  independentP : IndependentOn G P
  independentQ : IndependentOn G Q
  balanced : #P = #Q
  defP : df G Q P = 7
  defQ : df G P Q = 7
  minP : ∀ p ∈ P, 4 ≤ dg G Q p
  capP : ∀ p ∈ P, dg G Q p ≤ 6
  minQ : ∀ q ∈ Q, 4 ≤ dg G P q
  capQ : ∀ q ∈ Q, dg G P q ≤ 6
  sparse : Sparse7 G P Q
  subsetA : A ⊆ P
  subsetC : C ⊆ Q
  cardLeft : #A = #C + 3
  cardRight : #(Q \ C) = #(P \ A) + 3
  satC : ∀ c ∈ C, dg G P c = 6
  satB : ∀ b ∈ P \ A, dg G Q b = 6
  forward : ec G A (Q \ C) = 11
  reverse : ec G (P \ A) C = 0
  potentialLeft : gv G A C = 18
  potentialRight : gv G (Q \ C) (P \ A) = 18
  internalMinA : ∀ a ∈ A, 2 ≤ dg G C a
  internalMinD : ∀ d ∈ Q \ C, 2 ≤ dg G (P \ A) d

def C4Repair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V), C4Input G U W → Quartic G U W

def U2Repair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V), U2Input G U W → Quartic G U W

def E73Repair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q A C : Finset V), E73Input G P Q A C → Quartic G P Q

omit [DecidableEq V] in
theorem Sparse7.swap {U W : Finset V} (h : Sparse7 G U W) : Sparse7 G W U := by
  intro Y hY X hX hn hlt
  rw [gv_comm]
  exact h X hX Y hY (by omega) (by omega)

omit [DecidableEq V] in
private theorem four_mul_card_le_ec {A C : Finset V}
    (h : ∀ a ∈ A, 4 ≤ dg G C a) : 4 * #A ≤ ec G A C := by
  unfold ec
  calc 4 * #A = ∑ _a ∈ A, 4 := by simp [mul_comm]
       _ ≤ ∑ a ∈ A, dg G C a := sum_le_sum h

/- A literal violated full-host cut pays order >= 4 on both proper domains.
   The order-three floor14 must not be promoted to16. -/
theorem hall_cut_large_domains {P Q A C : Finset V} (hcard : #P = #Q)
    (hminP : ∀ p ∈ P, 4 ≤ dg G Q p) (hminQ : ∀ q ∈ Q, 4 ≤ dg G P q)
    (hA : A ⊆ P) (hC : C ⊆ Q)
    (hv : ec G A (Q \ C) + 4 * #C < 4 * #A) :
    (6 ≤ #A + #C ∧ #A + #C < #P + #Q) ∧
      (6 ≤ #(P \ A) + #(Q \ C) ∧ #(P \ A) + #(Q \ C) < #P + #Q) := by
  obtain ⟨hCne, hBne, hdomX, hdomY⟩ :=
    QB6Assembly.hall_cut_domains hcard hminP hminQ hA hC hv
  have hA5 : 5 ≤ #A := by
    by_contra! hsmall
    have he := four_mul_card_le_ec (G := G) (A := A)
      (fun a ha => hminP a (hA ha))
    have hs := ec_sdiff_add_right (G := G) hC A
    have hb := (ec_le_card_mul (G := G) A C).trans
      (Nat.mul_le_mul_right #C (show #A ≤ 4 by omega))
    omega
  have hD5 : 5 ≤ #(Q \ C) := by
    by_contra! hsmall
    have he := four_mul_card_le_ec (G := G) (A := Q \ C)
      (fun d hd => hminQ d (sdiff_subset hd))
    have hs := ec_sdiff_add_right (G := G) hA (Q \ C)
    have hb := (ec_le_card_mul (G := G) (Q \ C) (P \ A)).trans
      (Nat.mul_le_mul_right #(P \ A) (show #(Q \ C) ≤ 4 by omega))
    have hcA := card_sdiff_add_card_eq_card hA
    have hcC := card_sdiff_add_card_eq_card hC
    have hf := ec_comm (G := G) (Q \ C) A
    omega
  have hcpos := card_pos.mpr hCne
  have hbpos := card_pos.mpr hBne
  exact ⟨⟨by omega, hdomX.2⟩, ⟨by omega, hdomY.2⟩⟩

/- Exact adapter of a genuine balanced minimal pair. No Hall success is supplied. -/
theorem balanced_repair (repairE : E73Repair.{u})
    {P Q : Finset V} (hd : Disjoint P Q)
    (hiP : IndependentOn G P) (hiQ : IndependentOn G Q) (hcard : #P = #Q)
    (hminP : ∀ p ∈ P, 4 ≤ dg G Q p) (hcapP : ∀ p ∈ P, dg G Q p ≤ 6)
    (hminQ : ∀ q ∈ Q, 4 ≤ dg G P q) (hcapQ : ∀ q ∈ Q, dg G P q ≤ 6)
    (hsp : Sparse7 G P Q) (hn : 4 ≤ #P + #Q) (hg : gv G P Q = 14) :
    Quartic G P Q := by
  by_contra hq
  have hQ : Q.Nonempty := card_pos.mp (by omega)
  obtain ⟨A, hA, C, hC, hv⟩ := exists_violation_of_not_quartic hcard hQ hq
  obtain ⟨hdomX, hdomY⟩ := hall_cut_large_domains hcard hminP hminQ hA hC hv
  have hdefP : df G Q P = 7 := by
    have := gv_eq_right (G := G) P Q
    omega
  have hdefQ : df G P Q = 7 := by
    have := gv_eq_left (G := G) P Q
    omega
  have hx := hsp A hA C hC (by omega) hdomX.2
  have hy := hsp (P \ A) sdiff_subset (Q \ C) sdiff_subset (by omega) hdomY.2
  have hh := balanced_hall_patterns (b := 7) (Or.inr rfl)
    hcard hcapP hcapQ hdefP hdefQ hA hC hx hy hv
  have hPA : A ∪ (P \ A) = P := union_sdiff_of_subset hA
  have hQC : C ∪ (Q \ C) = Q := union_sdiff_of_subset hC
  have hca := card_sdiff_add_card_eq_card hA
  have hcc := card_sdiff_add_card_eq_card hC
  rcases hh with h | h | h
  · omega
  · obtain ⟨_, hcardX, _, hdfB, hdfC, hrev, hfwd, hgX, hgY⟩ := h
    have hcardY : #(Q \ C) = #(P \ A) + 2 := by omega
    have hgY' : gv G (Q \ C) (P \ A) = 16 := by rwa [gv_comm]
    have hinA : ∀ a ∈ A, 3 ≤ dg G C a := by
      intro a ha
      have he := card_erase_add_one ha
      have hp := gv_erase_left (G := G) ha C
      have hs := hsp (A.erase a) ((erase_subset a A).trans hA) C hC
        (by omega) (by omega)
      omega
    have hinD : ∀ d ∈ Q \ C, 3 ≤ dg G (P \ A) d := by
      intro d hd'
      have he := card_erase_add_one hd'
      have hp := gv_erase_left (G := G) hd' (P \ A)
      have hs := hsp.swap ((Q \ C).erase d)
        ((erase_subset d (Q \ C)).trans sdiff_subset) (P \ A) sdiff_subset
        (by omega) (by omega)
      omega
    have hcrit : QB7TwoReverse.CriticalClass G A (P \ A) C (Q \ C) := by
      refine {
        disjAB := disjoint_sdiff_self_right
        disjCD := disjoint_sdiff_self_right
        disjPQ := by simpa only [hPA, hQC] using hd
        independentP := by simpa only [hPA, IndependentOn] using hiP
        independentQ := by simpa only [hQC, IndependentOn] using hiQ
        balanced := by simpa only [hPA, hQC] using hcard
        minP := by simpa only [hPA, hQC] using hminP
        capP := by simpa only [hPA, hQC] using hcapP
        minQ := by simpa only [hPA, hQC] using hminQ
        capQ := by simpa only [hPA, hQC] using hcapQ
        sparse4 := by simpa [hPA, hQC, Sparse7, SparseBound] using hsp
        sparse3 := fun X _ Y _ h3 => QB6Assembly.size_three_bound (G := G) X Y h3
        imbalanceAC := hcardX
        imbalanceDB := hcardY
        saturatedB := by
          rw [hQC]
          exact fun b hb => dg_eq_six_of_df_eq_zero
            (fun z hz => hcapP z (sdiff_subset hz)) hdfB hb
        saturatedC := by
          rw [hPA]
          exact fun c hc => dg_eq_six_of_df_eq_zero
            (fun z hz => hcapQ z (hC hz)) hdfC hc
        forward7 := hfwd
        reverse2 := hrev
        potentialAC := hgX
        potentialDB := hgY'
        minA := hinA
        minD := hinD }
    have hout := QB7TwoReverse.physical_repair G A (P \ A) C (Q \ C) hcrit
    exact hq (by simpa only [hPA, hQC] using hout)
  · obtain ⟨_, hcardX, _, hdfB, hdfC, hrev, hfwd, hgX, hgY⟩ := h
    have hcardY : #(Q \ C) = #(P \ A) + 3 := by omega
    have hgY' : gv G (Q \ C) (P \ A) = 18 := by rwa [gv_comm]
    have hinA : ∀ a ∈ A, 2 ≤ dg G C a := by
      intro a ha
      have he := card_erase_add_one ha
      have hp := gv_erase_left (G := G) ha C
      have hs := hsp (A.erase a) ((erase_subset a A).trans hA) C hC
        (by omega) (by omega)
      omega
    have hinD : ∀ d ∈ Q \ C, 2 ≤ dg G (P \ A) d := by
      intro d hd'
      have he := card_erase_add_one hd'
      have hp := gv_erase_left (G := G) hd' (P \ A)
      have hs := hsp.swap ((Q \ C).erase d)
        ((erase_subset d (Q \ C)).trans sdiff_subset) (P \ A) sdiff_subset
        (by omega) (by omega)
      omega
    exact hq (repairE G P Q A C ⟨hd, hiP, hiQ, hcard, hdefP, hdefQ,
      hminP, hcapP, hminQ, hcapQ, hsp, hA, hC, hcardX, hcardY,
      (fun c hc => dg_eq_six_of_df_eq_zero (fun z hz => hcapQ z (hC hz)) hdfC hc),
      (fun b hb => dg_eq_six_of_df_eq_zero (fun z hz => hcapP z (sdiff_subset hz)) hdfB hb),
      hfwd, hrev, hgX, hgY', hinA, hinD⟩)

theorem quartic_of_minimal_fourteen
    (repair4 : C4Repair.{u}) (repair2 : U2Repair.{u}) (repairE : E73Repair.{u})
    {U W : Finset V} (hd : Disjoint U W)
    (hiU : IndependentOn G U) (hiW : IndependentOn G W)
    (hcapU : ∀ x ∈ U, dg G W x ≤ 6) (hcapW : ∀ y ∈ W, dg G U y ≤ 6)
    (hminU : ∀ x ∈ U, 4 ≤ dg G W x) (hminW : ∀ y ∈ W, 4 ≤ dg G U y)
    (hsp : Sparse7 G U W) (hn : 4 ≤ #U + #W) (hg : gv G U W = 14) :
    Quartic G U W := by
  have ordered : ∀ {X Y : Finset V}, #X ≤ #Y → Disjoint X Y →
      IndependentOn G X → IndependentOn G Y →
      (∀ x ∈ X, dg G Y x ≤ 6) → (∀ y ∈ Y, dg G X y ≤ 6) →
      (∀ x ∈ X, 4 ≤ dg G Y x) → (∀ y ∈ Y, 4 ≤ dg G X y) →
      Sparse7 G X Y → 4 ≤ #X + #Y → gv G X Y = 14 → Quartic G X Y := by
    intro X Y horder hdisj hiX hiY hcapX hcapY hminX hminY hsparse hn' hg'
    let j := #Y - #X
    have hcard : #Y = #X + j := by omega
    obtain ⟨hj, hdef⟩ := shore_signature (b := 7) (Or.inr rfl)
      hcard hcapX (by simpa using hg')
    interval_cases j
    · exact balanced_repair repairE hdisj hiX hiY (by omega)
        hminX hcapX hminY hcapY hsparse hn' hg'
    · exact repair4 G X Y ⟨hdisj, hiX, hiY, by omega, hminX, hcapX,
        hminY, hcapY, by norm_num at hdef; exact hdef, hsparse⟩
    · exact repair2 G X Y ⟨hdisj, hiX, hiY, by omega, hminX, hcapX,
        hminY, hcapY, by norm_num at hdef; exact hdef, hsparse⟩
  by_cases horder : #U ≤ #W
  · exact ordered horder hd hiU hiW hcapU hcapW hminU hminW hsp hn hg
  · exact (ordered (by omega) hd.symm hiW hiU hcapW hcapU hminW hminU hsp.swap
      (by omega) (by rwa [gv_comm])).swap

open scoped Classical in
omit [DecidableEq V] in
/-- Select a prescribed number of actual cross edges. Ambient edges are discarded,
    so both shores are independent without requiring that of the caller's graph. -/
theorem exists_cross_thinning {U W : Finset V} (hd : Disjoint U W)
    (k : ℕ) (hk : k ≤ ec G U W) :
    ∃ H : SimpleGraph V, H ≤ G ∧ ec H U W = k ∧
      IndependentOn H U ∧ IndependentOn H W := by
  obtain ⟨F, hF, hFk⟩ := exists_subset_card_eq (s := adjPairs G U W) (n := k)
    (by simpa only [card_adjPairs] using hk)
  have hmem : ∀ {x y : V}, (x, y) ∈ F → x ∈ U ∧ y ∈ W ∧ G.Adj x y := by
    intro x y hxy
    have := hF hxy
    simpa only [adjPairs, mem_filter, mem_product, and_assoc] using this
  let H : SimpleGraph V := {
    Adj := fun x y => G.Adj x y ∧ ((x, y) ∈ F ∨ (y, x) ∈ F)
    symm := ⟨fun x y h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩ }
  let : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  have hle : H ≤ G := fun _ _ h => h.1
  have hpairs : adjPairs H U W = F := by
    ext e
    rcases e with ⟨x, y⟩
    simp only [adjPairs, mem_filter, mem_product]
    constructor
    · rintro ⟨⟨hx, hy⟩, hxy⟩
      rcases hxy.2 with h | h
      · exact h
      · exact False.elim (disjoint_left.mp hd (hmem h).1 hy)
    · intro h
      obtain ⟨hx, hy, hadj⟩ := hmem h
      exact ⟨⟨hx, hy⟩, hadj, Or.inl h⟩
  refine ⟨H, hle, ?_, ?_, ?_⟩
  · rw [← card_adjPairs, hpairs, hFk]
  · intro x hx y hy hxy
    rcases hxy.2 with h | h
    · exact disjoint_left.mp hd hy (hmem h).2.1
    · exact disjoint_left.mp hd hx (hmem h).2.1
  · intro x hx y hy hxy
    rcases hxy.2 with h | h
    · exact disjoint_left.mp hd (hmem h).1 hx
    · exact disjoint_left.mp hd (hmem h).1 hy

omit [DecidableEq V] in
theorem ec_mono_graph {H : SimpleGraph V} [DecidableRel H.Adj]
    (hle : H ≤ G) (U W : Finset V) : ec H U W ≤ ec G U W := by
  unfold ec
  exact sum_le_sum fun x _ => QB6Assembly.dg_mono_graph hle W x

omit [DecidableEq V] in
theorem Sparse7.mono_graph {H : SimpleGraph V} [DecidableRel H.Adj]
    {U W : Finset V} (h : Sparse7 G U W) (hle : H ≤ G) : Sparse7 H U W := by
  intro X hX Y hY hn hlt
  have hs := h X hX Y hY hn hlt
  have he := ec_mono_graph hle X Y
  unfold gv at *
  omega

private theorem product_le_four {a b : ℕ} (h : a + b = 4) : a * b ≤ 4 := by
  have ha : a ≤ 4 := by omega
  interval_cases a <;> omega

omit [DecidableEq V] in
theorem five_le_of_dense14 {U W : Finset V} (hn : 4 ≤ #U + #W)
    (hg : gv G U W ≤ 14) : 5 ≤ #U + #W := by
  by_contra! h
  have hsum : #U + #W = 4 := by omega
  have he := (ec_le_card_mul (G := G) U W).trans (product_le_four hsum)
  unfold gv at hg
  omega

/-- All-order subset induction. The three open physical cases remain premises;
    actual thinning pays exact whole deficiency and independence. -/
theorem quartic_of_gv_le_fourteen
    (repair4 : C4Repair.{u}) (repair2 : U2Repair.{u}) (repairE : E73Repair.{u})
    {X Y : Finset V} (hd : Disjoint X Y)
    (hcapX : ∀ x ∈ X, dg G Y x ≤ 6) (hcapY : ∀ y ∈ Y, dg G X y ≤ 6)
    (hn4 : 4 ≤ #X + #Y) (hg : gv G X Y ≤ 14) : Quartic G X Y := by
  classical
  generalize hn : #X + #Y = n
  induction n using Nat.strong_induction_on generalizing X Y with
  | _ n ih =>
    by_contra hq
    have hsparse : Sparse7 G X Y := minimal_sparsity
      (fun X' hX' Y' hY' hn' hlt hg' => ih (#X' + #Y') (hn ▸ hlt)
        (disjoint_of_subset_left hX' (disjoint_of_subset_right hY' hd))
        (fun x hx => (dg_mono hY' x).trans (hcapX x (hX' hx)))
        (fun y hy => (dg_mono hX' y).trans (hcapY y (hY' hy))) hn' hg' rfl) hq
    let k := 3 * (#X + #Y) - 7
    have hk7 : k + 7 = 3 * (#X + #Y) := by dsimp [k]; omega
    have hk : k ≤ ec G X Y := by unfold gv at hg; omega
    obtain ⟨H, hHG, hHe, hiX, hiY⟩ := exists_cross_thinning hd k hk
    have hHsp : Sparse7 H X Y := hsparse.mono_graph hHG
    have hHgv : gv H X Y = 14 := by unfold gv; omega
    have h5 : 5 ≤ #X + #Y := five_le_of_dense14 hn4 hg
    have hminX : ∀ x ∈ X, 4 ≤ dg H Y x := fun x hx =>
      minimum_four_left hHsp (by omega) h5 hx
    have hminY : ∀ y ∈ Y, 4 ≤ dg H X y := fun y hy =>
      minimum_four_left hHsp.swap (by rw [gv_comm]; omega) (by omega) hy
    have hquarticH : Quartic H X Y := quartic_of_minimal_fourteen
      repair4 repair2 repairE hd hiX hiY
      (fun x hx => (QB6Assembly.dg_mono_graph hHG Y x).trans (hcapX x hx))
      (fun y hy => (QB6Assembly.dg_mono_graph hHG X y).trans (hcapY y hy))
      hminX hminY hHsp hn4 hHgv
    exact hq (QB6Assembly.quartic_mono_graph hHG hquarticH)

open scoped Classical in
/-- Conditional QB7 endpoint on the original graph. The assumptions C4Repair, U2Repair
    and E73Repair are explicit; the reverse-two case is already produced. -/
theorem qb7_conditional
    (repair4 : C4Repair.{u}) (repair2 : U2Repair.{u}) (repairE : E73Repair.{u})
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hbip : G.IsBipartite)
    (hdeg : G.maxDegree ≤ 6) (hn : 4 ≤ Fintype.card V)
    (he : 3 * Fintype.card V ≤ G.edgeSet.ncard + 7) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 4 := by
  obtain ⟨o⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨U, W, _, hUW, hcover, hbw⟩ := exists_sides hbip o
  have hc : #U + #W = Fintype.card V := by
    rw [← card_union_of_disjoint hUW, hcover, card_univ]
  have hec := ec_eq_ncard hbw
  have hq : Quartic G U W := quartic_of_gv_le_fourteen repair4 repair2 repairE hUW
    (fun x _ => (dg_le_maxDegree W x).trans hdeg)
    (fun y _ => (dg_le_maxDegree U y).trans hdeg) (by omega) (by unfold gv; omega)
  obtain ⟨H, hne, _, h4⟩ := exists_subgraph_of_quartic hUW hq
  refine ⟨H, hne, fun v => ?_⟩
  rw [SimpleGraph.Subgraph.coe_degree]
  exact h4 v v.property

#check quartic_of_minimal_fourteen
#check quartic_of_gv_le_fourteen
#check qb7_conditional
#check QB7TwoReverse.physical_repair
#print IndependentOn
#print Sparse7
#print C4Input
#print U2Input
#print E73Input
#print C4Repair
#print U2Repair
#print E73Repair
#print QB4.Quartic
#print axioms QB7TwoReverse.physical_repair
#print axioms exists_cross_thinning
#print axioms balanced_repair
#print axioms quartic_of_minimal_fourteen
#print axioms quartic_of_gv_le_fourteen
#print axioms qb7_conditional

end Erdos585.QB7Conditional
