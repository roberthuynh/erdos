import Openmath.Proofs.QB5.Main
import Openmath.Proofs.PaperSupport.QB7Reduction

/- -/
open Finset

namespace Erdos585.QB6Assembly

open QB4 QB5 QB7Reduction

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Proper physical subpairs, including size three. -/
def Sparse6 (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) : Prop :=
  ∀ X ⊆ U, ∀ Y ⊆ W, 3 ≤ #X + #Y → #X + #Y < #U + #W → 14 ≤ gv G X Y

structure C02Input (G : SimpleGraph V) [DecidableRel G.Adj] (A C : Finset V) : Prop where
  disjoint : Disjoint A C
  card : #A = #C + 2
  minA : ∀ a ∈ A, 4 ≤ dg G C a
  capA : ∀ a ∈ A, dg G C a ≤ 6
  satC : ∀ c ∈ C, dg G A c = 6
  sparse : Sparse6 G A C

structure C3SInput (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) : Prop where
  disjoint : Disjoint U W
  card : #W = #U + 1
  minU : ∀ u ∈ U, 4 ≤ dg G W u
  capU : ∀ u ∈ U, dg G W u ≤ 6
  minW : ∀ w ∈ W, 4 ≤ dg G U w
  capW : ∀ w ∈ W, dg G U w ≤ 6
  deficiency : df G W U = 3
  sparse : Sparse6 G U W

/-- The actual seven-forward/one-reverse balanced cut class. No support is supplied. -/
structure E6Input (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q A C : Finset V) : Prop where
  disjoint : Disjoint P Q
  balanced : #P = #Q
  defP : df G Q P = 6
  defQ : df G P Q = 6
  minP : ∀ p ∈ P, 4 ≤ dg G Q p
  capP : ∀ p ∈ P, dg G Q p ≤ 6
  minQ : ∀ q ∈ Q, 4 ≤ dg G P q
  capQ : ∀ q ∈ Q, dg G P q ≤ 6
  sparse : Sparse6 G P Q
  subsetA : A ⊆ P
  subsetC : C ⊆ Q
  cardLeft : #A = #C + 2
  cardRight : #(Q \ C) = #(P \ A) + 2
  satC : ∀ c ∈ C, dg G P c = 6
  satB : ∀ b ∈ P \ A, dg G Q b = 6
  forward : ec G A (Q \ C) = 7
  reverse : ec G (P \ A) C = 1
  potentialLeft : gv G A C = 14
  potentialRight : gv G (Q \ C) (P \ A) = 14
  internalMinA : ∀ a ∈ A, 3 ≤ dg G C a
  internalMinD : ∀ d ∈ Q \ C, 3 ≤ dg G (P \ A) d

/- -/
def C02Repair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V), C02Input G A C → Quartic G A C

/- -/
def C3SRepair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V), C3SInput G U W → Quartic G U W

/- -/
def E6Repair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q A C : Finset V), E6Input G P Q A C → Quartic G P Q

omit [DecidableEq V] in
lemma Sparse6.swap {U W : Finset V} (h : Sparse6 G U W) : Sparse6 G W U := by
  intro Y hY X hX hn hlt
  rw [gv_comm]
  exact h X hX Y hY (by omega) (by omega)

omit [DecidableEq V] in
lemma Sparse6.toSparseBound {U W : Finset V} (h : Sparse6 G U W) :
    SparseBound G U W 6 := fun X hX Y hY hn hlt => h X hX Y hY (by omega) hlt

private lemma product_le_two {a b : ℕ} (h : a + b = 3) : a * b ≤ 2 := by
  have ha : a ≤ 3 := by omega
  interval_cases a <;> omega

private lemma product_le_four {a b : ℕ} (h : a + b = 4) : a * b ≤ 4 := by
  have ha : a ≤ 4 := by omega
  interval_cases a <;> omega

omit [DecidableEq V] in
/-- The literal size-three domain is paid by the simple bipartite edge bound. -/
theorem size_three_bound (X Y : Finset V) (hn : #X + #Y = 3) : 14 ≤ gv G X Y := by
  have he : ec G X Y ≤ 2 := (ec_le_card_mul (G := G) X Y).trans (product_le_two hn)
  unfold gv
  omega

theorem minimal_sparsity_three {U W : Finset V}
    (ih : ∀ X ⊆ U, ∀ Y ⊆ W, 4 ≤ #X + #Y → #X + #Y < #U + #W →
      gv G X Y ≤ 12 → Quartic G X Y)
    (hq : ¬ Quartic G U W) : Sparse6 G U W := by
  have h4 : SparseBound G U W 6 := minimal_sparsity ih hq
  intro X hX Y hY hn hlt
  by_cases hn4 : 4 ≤ #X + #Y
  · exact h4 X hX Y hY hn4 hlt
  · exact size_three_bound X Y (by omega)

omit [DecidableEq V] in
theorem five_le_of_dense {U W : Finset V} (hn : 4 ≤ #U + #W)
    (hg : gv G U W ≤ 12) : 5 ≤ #U + #W := by
  by_contra! h
  have hsum : #U + #W = 4 := by omega
  have he : ec G U W ≤ 4 := (ec_le_card_mul (G := G) U W).trans (product_le_four hsum)
  unfold gv at hg
  omega

theorem minimum_four {U W : Finset V} (hsp : Sparse6 G U W)
    (hn : 4 ≤ #U + #W) (hg : gv G U W ≤ 12) :
    (∀ u ∈ U, 4 ≤ dg G W u) ∧ (∀ w ∈ W, 4 ≤ dg G U w) := by
  have h5 := five_le_of_dense hn hg
  refine ⟨fun u hu => minimum_four_left hsp.toSparseBound hg h5 hu, ?_⟩
  intro w hw
  exact minimum_four_left hsp.swap.toSparseBound (by rwa [gv_comm]) (by omega) hw

omit [DecidableEq V] in
private lemma four_mul_card_le_ec {A C : Finset V}
    (h : ∀ a ∈ A, 4 ≤ dg G C a) : 4 * #A ≤ ec G A C := by
  unfold ec
  calc 4 * #A = ∑ _a ∈ A, 4 := by simp [mul_comm]
       _ ≤ ∑ a ∈ A, dg G C a := sum_le_sum h

/-- A violated Hall cut has two actual nonempty proper domains of size at least three. -/
theorem hall_cut_domains {P Q A C : Finset V} (hcard : #P = #Q)
    (hminP : ∀ p ∈ P, 4 ≤ dg G Q p) (hminQ : ∀ q ∈ Q, 4 ≤ dg G P q)
    (hA : A ⊆ P) (hC : C ⊆ Q)
    (hv : ec G A (Q \ C) + 4 * #C < 4 * #A) :
    C.Nonempty ∧ (P \ A).Nonempty ∧
      (3 ≤ #A + #C ∧ #A + #C < #P + #Q) ∧
      (3 ≤ #(P \ A) + #(Q \ C) ∧ #(P \ A) + #(Q \ C) < #P + #Q) := by
  have hCne : C.Nonempty := by
    by_contra h
    have hz : C = ∅ := not_nonempty_iff_eq_empty.mp h
    have he := four_mul_card_le_ec (G := G) (A := A) fun a ha => hminP a (hA ha)
    simp only [hz, sdiff_empty, card_empty, mul_zero, add_zero] at hv
    omega
  have hBne : (P \ A).Nonempty := by
    by_contra h
    have hz : P \ A = ∅ := not_nonempty_iff_eq_empty.mp h
    have hAP : A = P := Subset.antisymm hA (sdiff_eq_empty_iff_subset.mp hz)
    have he := four_mul_card_le_ec (G := G) (A := Q \ C) fun q hq => hminQ q (sdiff_subset hq)
    rw [ec_comm] at he
    have hc := card_sdiff_add_card_eq_card hC
    rw [hAP] at hv
    omega
  have hCc : 1 ≤ #C := card_pos.mpr hCne
  have hBc : 1 ≤ #(P \ A) := card_pos.mpr hBne
  have ha := card_le_card hA
  have hc := card_le_card hC
  have hca := card_sdiff_add_card_eq_card hA
  have hcc := card_sdiff_add_card_eq_card hC
  refine ⟨hCne, hBne, ?_, ?_⟩ <;> omega

/-- Every literal E6 cut input is supplied by the actual minimal pair. -/
theorem balanced_input {P Q : Finset V} (hd : Disjoint P Q) (hcard : #P = #Q)
    (hminP : ∀ p ∈ P, 4 ≤ dg G Q p) (hcapP : ∀ p ∈ P, dg G Q p ≤ 6)
    (hminQ : ∀ q ∈ Q, 4 ≤ dg G P q) (hcapQ : ∀ q ∈ Q, dg G P q ≤ 6)
    (hsp : Sparse6 G P Q) (hn : 4 ≤ #P + #Q) (hg : gv G P Q = 12)
    (hq : ¬ Quartic G P Q) : ∃ A C, E6Input G P Q A C := by
  have hQ : Q.Nonempty := card_pos.mp (by omega)
  obtain ⟨A, hA, C, hC, hv⟩ := exists_violation_of_not_quartic hcard hQ hq
  obtain ⟨hCne, hBne, hdomX, hdomY⟩ := hall_cut_domains hcard hminP hminQ hA hC hv
  have hdefP : df G Q P = 6 := by
    have h := gv_eq_right (G := G) P Q
    omega
  have hdefQ : df G P Q = 6 := by
    have h := gv_eq_left (G := G) P Q
    omega
  have hx := hsp A hA C hC hdomX.1 hdomX.2
  have hy := hsp (P \ A) sdiff_subset (Q \ C) sdiff_subset hdomY.1 hdomY.2
  have hh := balanced_hall_patterns (b := 6) (Or.inl rfl)
    hcard hcapP hcapQ hdefP hdefQ hA hC hx hy hv
  rcases hh with h | h | h
  · obtain ⟨_, hcardX, _, hdfB, hdfC, hrev, hfwd, hgX, hgY⟩ := h
    have hca := card_sdiff_add_card_eq_card hA
    have hcc := card_sdiff_add_card_eq_card hC
    have hcardY : #(Q \ C) = #(P \ A) + 2 := by omega
    have hgY' : gv G (Q \ C) (P \ A) = 14 := by rwa [gv_comm]
    have hinA : ∀ a ∈ A, 3 ≤ dg G C a := by
      intro a ha
      have he := card_erase_add_one ha
      have hp := gv_erase_left (G := G) ha C
      have hcpos : 0 < #C := card_pos.mpr hCne
      have hs := hsp (A.erase a) ((erase_subset a A).trans hA) C hC (by omega) (by omega)
      omega
    have hinD : ∀ d ∈ Q \ C, 3 ≤ dg G (P \ A) d := by
      intro d hd'
      have he := card_erase_add_one hd'
      have hp := gv_erase_left (G := G) hd' (P \ A)
      have hbpos : 0 < #(P \ A) := card_pos.mpr hBne
      have hs := hsp.swap ((Q \ C).erase d)
        ((erase_subset d (Q \ C)).trans sdiff_subset) (P \ A) sdiff_subset
        (by omega) (by omega)
      omega
    refine ⟨A, C, ⟨hd, hcard, hdefP, hdefQ, hminP, hcapP, hminQ, hcapQ, hsp,
      hA, hC, hcardX, hcardY, ?_, ?_, hfwd, hrev, hgX, hgY', hinA, hinD⟩⟩
    · exact fun c hc' => dg_eq_six_of_df_eq_zero (fun c hc' => hcapQ c (hC hc')) hdfC hc'
    · exact fun b hb' => dg_eq_six_of_df_eq_zero (fun b hb' => hcapP b (sdiff_subset hb')) hdfB hb'
  · omega
  · omega

namespace E6Input

variable {P Q A C : Finset V}

private lemma block_six_le {a c e : ℕ} (hac : a = c + 2)
    (hg : 6 * ((a : ℤ) + c) - 2 * (e : ℤ) = 14) (he : e ≤ a * c) : 6 ≤ a := by
  have hc : 4 ≤ c := by
    by_contra! hc
    interval_cases c <;> simp_all <;> omega
  omega

theorem six_le_A (h : E6Input G P Q A C) : 6 ≤ #A :=
  block_six_le h.cardLeft (by simpa [gv] using h.potentialLeft)
    (ec_le_card_mul (G := G) A C)

theorem six_le_D (h : E6Input G P Q A C) : 6 ≤ #(Q \ C) :=
  block_six_le h.cardRight (by simpa [gv] using h.potentialRight)
    (ec_le_card_mul (G := G) (Q \ C) (P \ A))

theorem sparseLeft (h : E6Input G P Q A C) :
    ∀ X ⊆ A, ∀ Y ⊆ C, 3 ≤ #X + #Y → 14 ≤ gv G X Y := by
  intro X hX Y hY hn
  have hx := card_le_card hX
  have hy := card_le_card hY
  have ha := card_le_card h.subsetA
  have hc := card_sdiff_add_card_eq_card h.subsetC
  have hD : 2 ≤ #(Q \ C) := by rw [h.cardRight]; omega
  exact h.sparse X (hX.trans h.subsetA) Y (hY.trans h.subsetC) hn (by omega)

theorem sparseRight (h : E6Input G P Q A C) :
    ∀ X ⊆ Q \ C, ∀ Y ⊆ P \ A, 3 ≤ #X + #Y → 14 ≤ gv G X Y := by
  intro X hX Y hY hn
  have hx := card_le_card hX
  have hy := card_le_card hY
  have hd := card_le_card (sdiff_subset : Q \ C ⊆ Q)
  have ha := card_sdiff_add_card_eq_card h.subsetA
  have hA : 2 ≤ #A := by rw [h.cardLeft]; omega
  exact h.sparse.swap X (hX.trans sdiff_subset) Y (hY.trans sdiff_subset) hn (by omega)

theorem capInternalA (h : E6Input G P Q A C) : ∀ a ∈ A, dg G C a ≤ 6 :=
  fun a ha => (dg_mono h.subsetC a).trans (h.capP a (h.subsetA ha))

theorem capInternalD (h : E6Input G P Q A C) : ∀ d ∈ Q \ C, dg G (P \ A) d ≤ 6 :=
  fun d hd => (dg_mono sdiff_subset d).trans (h.capQ d (sdiff_subset hd))

theorem smallDefLeft (h : E6Input G P Q A C) : df G A C = 1 := by
  have hz : df G P C = 0 := by
    unfold df
    apply sum_eq_zero
    intro c hc
    rw [h.satC c hc]
    norm_num
  have hid := df_eq_df_add_ec (G := G) h.subsetA C
  have hec := ec_comm (G := G) C (P \ A)
  have hr := h.reverse
  omega

theorem smallDefRight (h : E6Input G P Q A C) : df G (Q \ C) (P \ A) = 1 := by
  have hz : df G Q (P \ A) = 0 := by
    unfold df
    apply sum_eq_zero
    intro b hb
    rw [h.satB b hb]
    norm_num
  have hsplit := ec_sdiff_add_right (G := G) h.subsetC (P \ A)
  have hwhole := df_eq (G := G) Q (P \ A)
  have hpart := df_eq (G := G) (Q \ C) (P \ A)
  have hr := h.reverse
  omega

theorem smallDegreeLeft (h : E6Input G P Q A C) :
    ∀ c ∈ C, dg G A c = 5 ∨ dg G A c = 6 := by
  have hcap : ∀ c ∈ C, dg G A c ≤ 6 :=
    fun c hc => (dg_mono h.subsetA c).trans (h.capQ c (h.subsetC hc))
  intro c hc
  have hs := single_le_sum (f := fun c => (6 : ℤ) - dg G A c)
    (fun c hc => by have := hcap c hc; omega) hc
  change (6 : ℤ) - dg G A c ≤ df G A C at hs
  have hz := h.smallDefLeft
  have hb := hcap c hc
  omega

theorem smallDegreeRight (h : E6Input G P Q A C) :
    ∀ b ∈ P \ A, dg G (Q \ C) b = 5 ∨ dg G (Q \ C) b = 6 := by
  have hcap : ∀ b ∈ P \ A, dg G (Q \ C) b ≤ 6 :=
    fun b hb => (dg_mono sdiff_subset b).trans (h.capP b (sdiff_subset hb))
  intro b hb
  have hs := single_le_sum (f := fun b => (6 : ℤ) - dg G (Q \ C) b)
    (fun b hb => by have := hcap b hb; omega) hb
  change (6 : ℤ) - dg G (Q \ C) b ≤ df G (Q \ C) (P \ A) at hs
  have hz := h.smallDefRight
  have hc := hcap b hb
  omega

end E6Input

/-- Close the three exact shore signatures only through the three physical producers. -/
theorem quartic_of_minimal_twelve
    (repair02 : C02Repair.{u}) (repair3 : C3SRepair.{u}) (repairE6 : E6Repair.{u})
    {U W : Finset V} (hd : Disjoint U W)
    (hcapU : ∀ u ∈ U, dg G W u ≤ 6) (hcapW : ∀ w ∈ W, dg G U w ≤ 6)
    (hminU : ∀ u ∈ U, 4 ≤ dg G W u) (hminW : ∀ w ∈ W, 4 ≤ dg G U w)
    (hsp : Sparse6 G U W) (hn : 4 ≤ #U + #W) (hg : gv G U W = 12) :
    Quartic G U W := by
  have ordered : ∀ {X Y : Finset V}, #X ≤ #Y → Disjoint X Y →
      (∀ x ∈ X, dg G Y x ≤ 6) → (∀ y ∈ Y, dg G X y ≤ 6) →
      (∀ x ∈ X, 4 ≤ dg G Y x) → (∀ y ∈ Y, 4 ≤ dg G X y) →
      Sparse6 G X Y → 4 ≤ #X + #Y → gv G X Y = 12 → Quartic G X Y := by
    intro X Y horder hdisj hcapX hcapY hminX hminY hsparse hn' hg'
    let j := #Y - #X
    have hcard : #Y = #X + j := by omega
    obtain ⟨hj, hdef⟩ := shore_signature (b := 6) (Or.inl rfl)
      hcard hcapX (by simpa using hg')
    interval_cases j
    · have hbalanced : #X = #Y := by omega
      by_contra hq
      obtain ⟨A, C, hE⟩ := balanced_input hdisj hbalanced hminX hcapX hminY hcapY
        hsparse hn' hg' hq
      exact hq (repairE6 G X Y A C hE)
    · exact repair3 G X Y ⟨hdisj, by omega, hminX, hcapX, hminY, hcapY,
        by norm_num at hdef; exact hdef, hsparse⟩
    · have hzero : df G Y X = 0 := by norm_num at hdef; exact hdef
      have hsat : ∀ x ∈ X, dg G Y x = 6 :=
        fun x hx => dg_eq_six_of_df_eq_zero hcapX hzero hx
      exact (repair02 G Y X ⟨hdisj.symm, by omega, hminY, hcapY, hsat, hsparse.swap⟩).swap
  by_cases horder : #U ≤ #W
  · exact ordered horder hd hcapU hcapW hminU hminW hsp hn hg
  · exact (ordered (by omega) hd.symm hcapW hcapU hminW hminU hsp.swap
      (by omega) (by rwa [gv_comm])).swap

/-- All-order finite-subset induction. This theorem is conditional, not universal QB6. -/
theorem quartic_of_gv_le_twelve
    (repair02 : C02Repair.{u}) (repair3 : C3SRepair.{u}) (repairE6 : E6Repair.{u})
    {X Y : Finset V} (hd : Disjoint X Y)
    (hcapX : ∀ x ∈ X, dg G Y x ≤ 6) (hcapY : ∀ y ∈ Y, dg G X y ≤ 6)
    (hn4 : 4 ≤ #X + #Y) (hg : gv G X Y ≤ 12) : Quartic G X Y := by
  generalize hn : #X + #Y = n
  induction n using Nat.strong_induction_on generalizing X Y with
  | _ n ih =>
    by_contra hq
    have hsparse : Sparse6 G X Y := minimal_sparsity_three
      (fun X' hX' Y' hY' hn' hlt hg' => ih (#X' + #Y') (hn ▸ hlt)
        (disjoint_of_subset_left hX' (disjoint_of_subset_right hY' hd))
        (fun x hx => (dg_mono hY' x).trans (hcapX x (hX' hx)))
        (fun y hy => (dg_mono hX' y).trans (hcapY y (hY' hy))) hn' hg' rfl) hq
    have hgexact : gv G X Y = 12 := by
      have hnlow : ¬ gv G X Y ≤ 10 :=
        fun hlow => hq (quartic_of_gv_le_ten hcapX hcapY (by omega) hlow)
      obtain ⟨k, hk⟩ := even_gv (G := G) X Y
      omega
    obtain ⟨hminX, hminY⟩ := minimum_four hsparse hn4 hg
    exact hq (quartic_of_minimal_twelve repair02 repair3 repairE6 hd hcapX hcapY
      hminX hminY hsparse hn4 hgexact)

open scoped Classical in
/-- Actual deletion of host edges to an arbitrary prescribed feasible count. -/
theorem exists_edge_thinning {V : Type u} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (hk : k ≤ G.edgeSet.ncard) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.edgeSet.ncard = k := by
  have hcard : #G.edgeFinset = G.edgeSet.ncard := by
    rw [← SimpleGraph.coe_edgeFinset G, Set.ncard_coe_finset]
  obtain ⟨F, hFG, hFk⟩ := exists_subset_card_eq (s := G.edgeFinset) (n := k) (by omega)
  let H : SimpleGraph V := SimpleGraph.fromEdgeSet (F : Set (Sym2 V))
  have he : H.edgeSet = (F : Set (Sym2 V)) := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    constructor
    · exact fun h => h.1
    · intro hf
      refine ⟨hf, ?_⟩
      exact G.not_isDiag_of_mem_edgeFinset (hFG hf)
  refine ⟨H, ?_, ?_⟩
  · apply SimpleGraph.edgeSet_subset_edgeSet.mp
    rw [he]
    exact fun e hf => SimpleGraph.mem_edgeFinset.mp (hFG hf)
  · rw [he, Set.ncard_coe_finset]
    exact hFk

omit [DecidableRel G.Adj] in
/-- A quartic uses actual host edges and therefore lifts through a graph inclusion. -/
theorem quartic_mono_graph {H : SimpleGraph V}
    {U W : Finset V} (hle : H ≤ G) (hq : Quartic H U W) : Quartic G U W := by
  obtain ⟨F, hne, hsub, hadj, h1, h2⟩ := hq
  exact ⟨F, hne, hsub, fun e he => hle (hadj e he), h1, h2⟩

omit [DecidableEq V] in
theorem dg_mono_graph {H : SimpleGraph V} [DecidableRel H.Adj]
    (hle : H ≤ G) (S : Finset V) (v : V) : dg H S v ≤ dg G S v := by
  apply card_le_card
  intro w hw
  exact mem_filter.mpr ⟨(mem_filter.mp hw).1, hle (mem_filter.mp hw).2⟩

open scoped Classical in
/-- Conditional endpoint using QB5 normalization directly, without edge deletion. -/
theorem qb6_conditional_direct
    (repair02 : C02Repair.{u}) (repair3 : C3SRepair.{u}) (repairE6 : E6Repair.{u})
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hbip : G.IsBipartite)
    (hdeg : G.maxDegree ≤ 6) (hn : 4 ≤ Fintype.card V)
    (he : 3 * Fintype.card V ≤ G.edgeSet.ncard + 6) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 4 := by
  obtain ⟨o⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨U, W, _, hUW, hcover, hbw⟩ := exists_sides hbip o
  have hc : #U + #W = Fintype.card V := by
    rw [← card_union_of_disjoint hUW, hcover, card_univ]
  have hec := ec_eq_ncard hbw
  have hq : Quartic G U W := quartic_of_gv_le_twelve repair02 repair3 repairE6 hUW
    (fun u _ => (dg_le_maxDegree W u).trans hdeg)
    (fun w _ => (dg_le_maxDegree U w).trans hdeg) (by omega) (by unfold gv; omega)
  obtain ⟨H, hne, _, h4⟩ := exists_subgraph_of_quartic hUW hq
  refine ⟨H, hne, fun v => ?_⟩
  rw [SimpleGraph.Subgraph.coe_degree]
  exact h4 v v.property

open scoped Classical in
/-- Conditional actual endpoint through literal thinning to e=3n-6. -/
theorem qb6_conditional
    (repair02 : C02Repair.{u}) (repair3 : C3SRepair.{u}) (repairE6 : E6Repair.{u})
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hbip : G.IsBipartite)
    (hdeg : G.maxDegree ≤ 6) (hn : 4 ≤ Fintype.card V)
    (he : 3 * Fintype.card V ≤ G.edgeSet.ncard + 6) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 4 := by
  let k := 3 * Fintype.card V - 6
  have hk : k ≤ G.edgeSet.ncard := by omega
  have hk6 : k + 6 = 3 * Fintype.card V := by omega
  obtain ⟨F, hFG, hFe⟩ := exists_edge_thinning G k hk
  obtain ⟨o⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨U, W, _, hUW, hcover, hbw⟩ := exists_sides hbip o
  have hc : #U + #W = Fintype.card V := by
    rw [← card_union_of_disjoint hUW, hcover, card_univ]
  have hFbw : F.IsBipartiteWith ↑U ↑W :=
    ⟨hbw.disjoint, fun _ _ hadj => hbw.mem_of_adj (hFG hadj)⟩
  have hec := ec_eq_ncard hFbw
  have hqF : Quartic F U W := quartic_of_gv_le_twelve repair02 repair3 repairE6 hUW
    (fun u _ => (dg_mono_graph hFG W u).trans ((dg_le_maxDegree W u).trans hdeg))
    (fun w _ => (dg_mono_graph hFG U w).trans ((dg_le_maxDegree U w).trans hdeg))
    (by omega) (by unfold gv; omega)
  have hq : Quartic G U W := quartic_mono_graph hFG hqF
  obtain ⟨H, hne, _, h4⟩ := exists_subgraph_of_quartic hUW hq
  refine ⟨H, hne, fun v => ?_⟩
  rw [SimpleGraph.Subgraph.coe_degree]
  exact h4 v v.property

#print axioms exists_edge_thinning
#print axioms balanced_input
#print axioms quartic_of_gv_le_twelve
#print axioms qb6_conditional
#check qb6_conditional

/- Definition audit: every producer has physical graph fields and an actual-edge conclusion. -/
#print C02Repair
#print C3SRepair
#print E6Repair
#print C02Input
#print C3SInput
#print E6Input
#print Sparse6
#print Erdos585.QB4.Quartic
#print Erdos585.QB4.dg
#print Erdos585.QB4.ec
#print Erdos585.QB4.gv
#print Erdos585.QB4.df

end Erdos585.QB6Assembly
