import Openmath.Proofs.PaperSupport.UnitBMatchingR352Modules
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.QB7SmallLobeR643
open QB4
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def IndependentOn (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ¬ G.Adj x y

def Sparse7 (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) : Prop :=
  ∀ X ⊆ U, ∀ Y ⊆ W, 4 ≤ #X + #Y → #X + #Y < #U + #W → 16 ≤ gv G X Y

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

/-- Exact two-lobe finite decomposition after deletion of S.
Nontrivial lobes have a nonempty interior right shore. The edge separation
is original anticompleteness; no local balance or cut certificate is assumed. -/
structure Split (G : SimpleGraph V) (U W S U₁ U₂ W₁ W₂ : Finset V) : Prop where
  separator : S ⊆ W
  cardS : #S = 4
  leftCover : U₁ ∪ U₂ = U
  leftDisjoint : Disjoint U₁ U₂
  rightCover : W₁ ∪ W₂ ∪ S = W
  rightDisjoint : Disjoint W₁ W₂
  rightSep₁ : Disjoint W₁ S
  rightSep₂ : Disjoint W₂ S
  nonempty₁ : W₁.Nonempty
  nonempty₂ : W₂.Nonempty
  cross₁ : ∀ x ∈ U₁, ∀ y ∈ W₂, ¬ G.Adj x y
  cross₂ : ∀ x ∈ U₂, ∀ y ∈ W₁, ¬ G.Adj x y

/-- An actual original unit edge set; it retains exactly all left vertices
and all right vertices except the two fixed original omissions. -/
def FixedOmissionFactor (G : SimpleGraph V) (U W : Finset V) (z₁ z₂ : V) : Prop :=
  ∃ F : Finset (V × V), F ⊆ U ×ˢ (W.erase z₁ |>.erase z₂) ∧
    (∀ e ∈ F, G.Adj e.1 e.2) ∧
    (∀ x ∈ U, #{e ∈ F | e.1 = x} = 4) ∧
    (∀ y ∈ (W.erase z₁ |>.erase z₂), #{e ∈ F | e.2 = y} = 4)

/-- endpoint proposition. This declaration alone proves nothing. -/
def SmallLobeClaim : Prop :=
  ∀ (U W S U₁ U₂ W₁ W₂ : Finset V), U2Input G U W →
    Split G U W S U₁ U₂ W₁ W₂ → #U₁ = 4 →
    ∀ z₁ ∈ W₁, ∀ z₂ ∈ W₂,
      dg G U z₁ < 6 → dg G U z₂ < 6 →
      FixedOmissionFactor G U W z₁ z₂

lemma ec_union_right {A B : Finset V} (h : Disjoint A B) (X : Finset V) :
    ec G X (A ∪ B) = ec G X A + ec G X B := by
  unfold ec
  simp_rw [dg_union_of_disjoint h]
  exact sum_add_distrib

lemma ec_union_left {A B : Finset V} (h : Disjoint A B) (X : Finset V) :
    ec G (A ∪ B) X = ec G A X + ec G B X := by
  unfold ec
  exact sum_union h

omit [DecidableEq V] in
lemma dg_zero {A : Finset V} {v : V} (h : ∀ a ∈ A, ¬ G.Adj v a) :
    dg G A v = 0 := by
  unfold dg
  apply card_eq_zero.mpr
  exact filter_eq_empty_iff.mpr h

omit [DecidableEq V] in
lemma ec_zero {A B : Finset V} (h : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    ec G A B = 0 := by
  unfold ec
  exact sum_eq_zero fun a ha => dg_zero (h a ha)

lemma U2Input.minU_five {U W : Finset V} (h : U2Input G U W) :
    ∀ x ∈ U, 5 ≤ dg G W x := by
  intro x hx
  have he := df_le_of_subset (G := G) (S := W)
    (singleton_subset_iff.mpr hx) h.capU
  rw [h.defU] at he
  simp only [df, sum_singleton] at he
  omega

omit [DecidableEq V] in
lemma U2Input.defW {U W : Finset V} (h : U2Input G U W) : df G U W = 13 := by
  have hu := h.defU
  rw [df_eq] at hu ⊢
  have he := ec_comm (G := G) U W
  have hc := h.card
  omega

omit [DecidableRel G.Adj] in
lemma Split.subsets {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) :
    U₁ ⊆ U ∧ U₂ ⊆ U ∧ W₁ ⊆ W ∧ W₂ ⊆ W := by
  constructor
  · intro x hx
    rw [← h.leftCover]
    exact mem_union_left _ hx
  constructor
  · intro x hx
    rw [← h.leftCover]
    exact mem_union_right _ hx
  constructor
  · intro x hx
    rw [← h.rightCover]
    exact mem_union_left _ (mem_union_left _ hx)
  · intro x hx
    rw [← h.rightCover]
    exact mem_union_left _ (mem_union_right _ hx)

omit [DecidableRel G.Adj] in
lemma Split.swap {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) : Split G U W S U₂ U₁ W₂ W₁ := by
  refine ⟨h.separator, h.cardS, ?_, h.leftDisjoint.symm, ?_, h.rightDisjoint.symm,
    h.rightSep₂, h.rightSep₁, h.nonempty₂, h.nonempty₁, h.cross₂, h.cross₁⟩
  · simpa only [union_comm] using h.leftCover
  · simpa only [union_comm W₁ W₂] using h.rightCover

lemma Split.degree_left {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) {x : V} (hx : x ∈ U₁) :
    dg G (W₁ ∪ S) x = dg G W x := by
  have hd : Disjoint (W₁ ∪ S) W₂ :=
    disjoint_union_left.mpr ⟨h.rightDisjoint, h.rightSep₂.symm⟩
  have hc : (W₁ ∪ S) ∪ W₂ = W := by
    rw [union_assoc, union_comm S W₂, ← union_assoc, h.rightCover]
  have hz := dg_zero (h.cross₁ x hx)
  have he := dg_union_of_disjoint (G := G) hd x
  rw [hc, hz] at he
  omega

lemma Split.degree_right {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) {y : V} (hy : y ∈ W₁) :
    dg G U₁ y = dg G U y := by
  have hz : dg G U₂ y = 0 := dg_zero fun x hx => by
    simpa only [G.adj_comm] using h.cross₂ x hx y hy
  have he := dg_union_of_disjoint (G := G) h.leftDisjoint y
  rw [h.leftCover, hz] at he
  omega

lemma Split.left_large {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) : 4 ≤ #U₁ := by
  obtain ⟨y, hy⟩ := h.nonempty₁
  have hmin := hi.minW y (h.subsets.2.2.1 hy)
  rw [← h.degree_right hy] at hmin
  exact hmin.trans (dg_le_card U₁ y)

lemma Split.local_floor {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    {A T : Finset V} (hA : A ⊆ U₁) (hT : T ⊆ W₁ ∪ S)
    (hn : 4 ≤ #A + #T) : 16 ≤ gv G A T := by
  have hU : #U₁ < #U := by
    have he := card_union_of_disjoint h.leftDisjoint
    have hp := h.swap.left_large hi
    rw [h.leftCover] at he
    omega
  have hTW : W₁ ∪ S ⊆ W := union_subset h.subsets.2.2.1 h.separator
  exact hi.sparse A (hA.trans h.subsets.1) T (hT.trans hTW) hn
    (by have := card_le_card hA; have := card_le_card (hT.trans hTW); omega)

lemma Split.local_scar {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) :
    0 ≤ df G (W₁ ∪ S) U₁ ∧ df G (W₁ ∪ S) U₁ ≤ 1 := by
  have he : df G (W₁ ∪ S) U₁ = df G W U₁ := by
    unfold df
    exact sum_congr rfl fun x hx => by rw [h.degree_left hx]
  rw [he]
  constructor
  · exact df_nonneg fun x hx => hi.capU x (h.subsets.1 hx)
  · have := df_le_of_subset (G := G) (S := W) h.subsets.1 hi.capU
    rwa [hi.defU] at this

lemma Split.local_balance {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) :
    #U₁ = #W₁ + 1 := by
  have bound : ∀ (P P' Q Q' : Finset V), Split G U W S P P' Q Q' → #P ≤ #Q + 1 := by
    intro P P' Q Q' hs
    have hp := hs.left_large hi
    have hf := hs.local_floor hi (Subset.refl P) (Subset.refl (Q ∪ S)) (by omega)
    have he := gv_eq_right (G := G) P (Q ∪ S)
    have hc := hs.local_scar hi
    have hq := card_union_of_disjoint hs.rightSep₁
    rw [hs.cardS] at hq
    omega
  have h₁ := bound U₁ U₂ W₁ W₂ h
  have h₂ := bound U₂ U₁ W₂ W₁ h.swap
  have hu := card_union_of_disjoint h.leftDisjoint
  rw [h.leftCover] at hu
  have hw := card_union_of_disjoint h.rightDisjoint
  have hws := card_union_of_disjoint
    (disjoint_union_left.mpr ⟨h.rightSep₁, h.rightSep₂⟩)
  rw [h.rightCover, h.cardS] at hws
  have hc := hi.card
  omega

lemma ec_erase_right {P Q : Finset V} {z : V} (hz : z ∈ Q) :
    ec G P (Q.erase z) + dg G P z = ec G P Q := by
  rw [ec_comm P (Q.erase z), ec_comm P Q]
  exact sum_erase_add Q (dg G P) hz

lemma dg_erase_loss (Q : Finset V) (z x : V) :
    dg G Q x ≤ dg G (Q.erase z) x + 1 := by
  have hs : Q.filter (fun w => G.Adj x w) ⊆
      insert z ((Q.erase z).filter (fun w => G.Adj x w)) := by
    intro y hy
    obtain ⟨hyQ, hadj⟩ := mem_filter.mp hy
    by_cases he : y = z
    · exact mem_insert.mpr (Or.inl he)
    · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨mem_erase.mpr ⟨he,hyQ⟩,hadj⟩))
  exact (card_le_card hs).trans (card_insert_le _ _)

omit [DecidableEq V] in
lemma ec_product_bound (P Q : Finset V) : ec G P Q ≤ #P * #Q := by
  unfold ec
  calc ∑ x ∈ P, dg G Q x ≤ ∑ _x ∈ P, #Q := sum_le_sum fun x _ => dg_le_card Q x
    _ = #P * #Q := by simp

lemma single_omission_cut {P Q : Finset V} {z : V}
    (hmin : ∀ x ∈ P, 5 ≤ dg G Q x)
    (hcap : ∀ x ∈ P, dg G Q x ≤ 6)
    (hrcap : ∀ y ∈ Q, dg G P y ≤ 6)
    (hscar : df G Q P ≤ 1)
    (hfloor : ∀ A ⊆ P, ∀ T ⊆ Q, 4 ≤ #A + #T → 16 ≤ gv G A T)
    (hz : z ∈ Q) (hzd : dg G P z ≤ 5)
    {A T : Finset V} (hA : A ⊆ P) (hT : T ⊆ Q.erase z) :
    4 * #A ≤ ec G A (Q.erase z \ T) + 4 * #T := by
  have hTQ : T ⊆ Q := hT.trans (erase_subset z Q)
  have hsplit := ec_sdiff_add_right (G := G) hT A
  by_cases hnonpos : #A ≤ #T
  · omega
  have heps := (df_le_of_subset (G := G) (S := Q) hA hcap).trans hscar
  rw [df_eq] at heps
  have herase := ec_erase_right (G := G) (P := A) hz
  have hloss := (dg_mono (G := G) hA z).trans hzd
  have hsmallcut : ec G A T ≤ 6 * #T := by
    rw [ec_comm]
    exact ec_le_six_mul fun y hy => (dg_mono (G := G) hA y).trans (hrcap y (hTQ hy))
  by_cases hn : 4 ≤ #A + #T
  · have hf := hfloor A hA T hTQ hn
    unfold gv at hf
    by_cases hk : #A ≤ #T + 2 <;> omega
  · have hret : 4 * #A ≤ ec G A (Q.erase z) := by
      unfold ec
      calc 4 * #A = ∑ _x ∈ A, 4 := by simp [mul_comm]
        _ ≤ ∑ x ∈ A, dg G (Q.erase z) x := sum_le_sum fun x hx => by
          have hd := hmin x (hA hx)
          have hl := dg_erase_loss (G := G) Q z x
          omega
    have hprod := ec_product_bound (G := G) T A
    have hAt : #A ≤ 4 := by omega
    have hp : #T * #A ≤ #T * 4 := Nat.mul_le_mul_left #T hAt
    rw [ec_comm T A] at hprod
    omega

lemma original_edges_cut (P Q A T : Finset V) (hA : A ⊆ P) (_hT : T ⊆ Q) :
    #{e ∈ adjPairs G P Q | e.1 ∈ A ∧ e.2 ∉ T} = ec G A (Q \ T) := by
  rw [← card_adjPairs]
  congr 1
  ext e
  simp only [adjPairs, mem_filter, mem_product, mem_sdiff]
  constructor
  · rintro ⟨⟨⟨hp,hq⟩,hadj⟩,ha,ht⟩
    exact ⟨⟨ha,hq,ht⟩,hadj⟩
  · rintro ⟨⟨ha,hq,ht⟩,hadj⟩
    exact ⟨⟨⟨hA ha,hq⟩,hadj⟩,ha,ht⟩

/-- Uses the banked actual unit-edge Hall theorem; only local proper-support
floor and original degree assumptions are inputs, never a cut certificate. -/
theorem single_omission_left_supplier {P Q : Finset V} {z : V}
    (hmin : ∀ x ∈ P, 5 ≤ dg G Q x)
    (hcap : ∀ x ∈ P, dg G Q x ≤ 6)
    (hrcap : ∀ y ∈ Q, dg G P y ≤ 6)
    (hscar : df G Q P ≤ 1)
    (hfloor : ∀ A ⊆ P, ∀ T ⊆ Q, 4 ≤ #A + #T → 16 ≤ gv G A T)
    (hz : z ∈ Q) (hzd : dg G P z ≤ 5) :
    ∃ F : Finset (V × V), F ⊆ P ×ˢ Q.erase z ∧
      (∀ e ∈ F, G.Adj e.1 e.2) ∧
      (∀ x ∈ P, #{e ∈ F | e.1 = x} = 4) ∧
      (∀ y ∈ Q.erase z, #{e ∈ F | e.2 = y} ≤ 4) := by
  classical
  obtain ⟨F,hF,hleft,hright⟩ := UnitBMatchingR352.unitBMatchingCutCriterion
    P (Q.erase z) (adjPairs G P (Q.erase z)) (fun _ => 4) (fun _ => 4)
    (filter_subset _ _) (by
      intro A hA T hT
      have hb := single_omission_cut hmin hcap hrcap hscar hfloor hz hzd hA hT
      convert hb using 1
      · simp [mul_comm]
      · congr 1
        · have he := original_edges_cut (G := G) P (Q.erase z) A T hA hT
          convert he using 1
          congr 1
          ext e
          simp only [mem_filter]
        · simp [mul_comm])
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · exact hF.trans (filter_subset _ _)
  · intro e he
    exact (mem_filter.mp (hF he)).2
  · intro x hx
    convert hleft x hx using 1
    congr 1
    ext e
    simp only [mem_filter]
  · intro y hy
    convert hright y hy using 1
    congr 1
    ext e
    simp only [mem_filter]

/-- Original all-U supplier in either lobe, for every originally deficient
interior omission. Right vertices have capacity four, not a saturation claim. -/
theorem Split.single_omission_left_supplier {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    {z : V} (hz : z ∈ W₁) (hzd : dg G U z < 6) :
    ∃ F : Finset (V × V), F ⊆ U₁ ×ˢ (W₁ ∪ S).erase z ∧
      (∀ e ∈ F, G.Adj e.1 e.2) ∧
      (∀ x ∈ U₁, #{e ∈ F | e.1 = x} = 4) ∧
      (∀ y ∈ (W₁ ∪ S).erase z, #{e ∈ F | e.2 = y} ≤ 4) := by
  apply Erdos585.QB7SmallLobeR643.single_omission_left_supplier
  · intro x hx
    rw [h.degree_left hx]
    exact hi.minU_five x (h.subsets.1 hx)
  · intro x hx
    rw [h.degree_left hx]
    exact hi.capU x (h.subsets.1 hx)
  · intro y hy
    exact (dg_mono (G := G) h.subsets.1 y).trans
      (hi.capW y ((union_subset h.subsets.2.2.1 h.separator) hy))
  · exact (h.local_scar hi).2
  · exact fun A hA T hT hn => h.local_floor hi hA hT hn
  · exact mem_union_left _ hz
  · rw [h.degree_right hz]
    omega

lemma Split.interior_scar {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) :
    5 ≤ df G U W₁ := by
  have he : df G U₁ W₁ = df G U W₁ := by
    unfold df
    exact sum_congr rfl fun y hy => by rw [h.degree_right hy]
  have hn := h.left_large hi
  have hw := card_pos.mpr h.nonempty₁
  have hf := h.local_floor hi (Subset.refl U₁)
    (subset_union_left : W₁ ⊆ W₁ ∪ S) (by omega)
  have hc := h.local_balance hi
  rw [gv_eq_left, he] at hf
  omega

lemma Split.deficient_exists {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) :
    ∃ z ∈ W₁, dg G U z < 6 := by
  by_contra hn
  push Not at hn
  have hz : df G U W₁ = 0 := by
    unfold df
    apply sum_eq_zero
    intro y hy
    have hcap := hi.capW y (h.subsets.2.2.1 hy)
    have hmin := hn y hy
    omega
  have hd := h.interior_scar hi
  omega

lemma Split.small_interior_degree {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) (hsmall : #U₁ = 4) :
    #W₁ = 3 ∧ (∀ y ∈ W₁, dg G U y = 4) := by
  constructor
  · have := h.local_balance hi
    omega
  · intro y hy
    have hmin := hi.minW y (h.subsets.2.2.1 hy)
    have hmax := dg_le_card (G := G) U₁ y
    rw [h.degree_right hy, hsmall] at hmax
    omega

lemma Split.small_complete {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) (hsmall : #U₁ = 4) :
    ∀ x ∈ U₁, ∀ y ∈ W₁, G.Adj x y := by
  intro x hx y hy
  have hd := (h.small_interior_degree hi hsmall).2 y hy
  rw [← h.degree_right hy] at hd
  have heq : #{x ∈ U₁ | G.Adj y x} = #U₁ := by
    unfold dg at hd
    rw [hsmall]
    convert hd using 1
  have hall : ∀ x ∈ U₁, G.Adj y x := card_filter_eq_iff.mp heq
  exact G.adj_symm (hall x hx)

lemma Split.small_scar {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) (hsmall : #U₁ = 4) :
    df G U W₁ = 6 ∧ df G U W₂ + df G U S = 7 ∧
      0 ≤ df G U S ∧ df G U S ≤ 2 ∧ df G U W₂ ≤ 7 := by
  obtain ⟨hc,hd⟩ := h.small_interior_degree hi hsmall
  have hs : df G U W₁ = 6 := by
    unfold df
    have he : (∑ y ∈ W₁, (6 - (dg G U y : ℤ))) = ∑ _y ∈ W₁, (2 : ℤ) :=
      sum_congr rfl fun y hy => by rw [hd y hy]; norm_num
    rw [he]
    simp [hc]
  have htotal : df G U W₁ + df G U W₂ + df G U S = 13 := by
    have he := hi.defW
    rw [← h.rightCover] at he
    unfold df at he ⊢
    rw [sum_union (disjoint_union_left.mpr ⟨h.rightSep₁,h.rightSep₂⟩),
      sum_union h.rightDisjoint] at he
    exact he
  have hlo := h.swap.interior_scar hi
  have hnonneg : 0 ≤ df G U S := df_nonneg fun y hy => hi.capW y (h.separator hy)
  exact ⟨hs, by omega, hnonneg, by omega, by omega⟩

lemma Split.small_retained_scar {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) (hsmall : #U₁ = 4)
    {z₁ z₂ : V} (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂) (hd₂ : dg G U z₂ < 6) :
    df G U (W₁.erase z₁) = 4 ∧ df G U (W₂.erase z₂) ≤ 6 := by
  have hs := h.small_scar hi hsmall
  have he₁ : df G U (W₁.erase z₁) + (6 - (dg G U z₁ : ℤ)) = df G U W₁ := by
    exact sum_erase_add W₁ (fun y => 6 - (dg G U y : ℤ)) hz₁
  have he₂ : df G U (W₂.erase z₂) + (6 - (dg G U z₂ : ℤ)) = df G U W₂ := by
    exact sum_erase_add W₂ (fun y => 6 - (dg G U y : ℤ)) hz₂
  have hd₁ := (h.small_interior_degree hi hsmall).2 z₁ hz₁
  constructor <;> omega

#print axioms Split.single_omission_left_supplier
#print axioms Split.local_balance
#print axioms Split.small_retained_scar

/-- Exact original unit-edge capped degree sum, before minimizing Y. -/
def capped (G : SimpleGraph V) [DecidableRel G.Adj] (P T : Finset V) : ℕ :=
  ∑ x ∈ P, min 4 (dg G T x)

def rankTerm (G : SimpleGraph V) [DecidableRel G.Adj] (P Y R : Finset V) : ℤ :=
  (capped G P (Y ∪ R) : ℤ) - 4 * #Y

/-- R622 equation (8), for every actual Y and R separately.
The high-degree support is proved large before applying the local floor. -/
lemma capped_rank_lower {P Q Y R : Finset V}
    (hY : Y ⊆ Q) (hR : R ⊆ Q) (hdr : Disjoint Y R)
    (hcap : ∀ x ∈ P, dg G Q x ≤ 6)
    (hminY : ∀ y ∈ Y, 4 ≤ dg G P y)
    (hfloor : ∀ A ⊆ P, ∀ T ⊆ Q, 4 ≤ #A + #T → 16 ≤ gv G A T) :
    (ec G P R : ℤ) - max 0 (df G P Y + 2 * #R - 6) ≤ rankTerm G P Y R := by
  let A := P.filter fun x => 5 ≤ dg G (Y ∪ R) x
  have hA : A ⊆ P := filter_subset _ _
  have hlow : ∀ x ∈ P \ A, dg G (Y ∪ R) x ≤ 4 := by
    intro x hx
    have hn : ¬ 5 ≤ dg G (Y ∪ R) x := by
      intro hh
      exact (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨(mem_sdiff.mp hx).1,hh⟩)
    omega
  have hhigh : ∀ x ∈ A, 4 ≤ dg G (Y ∪ R) x := by
    intro x hx
    have := (mem_filter.mp hx).2
    omega
  have hsplitcap : capped G P (Y ∪ R) = 4 * #A + ec G (P \ A) (Y ∪ R) := by
    have he := sum_sdiff hA (f := fun x => min 4 (dg G (Y ∪ R) x))
    have ha : (∑ x ∈ A, min 4 (dg G (Y ∪ R) x)) = 4 * #A := by
      calc _ = ∑ _x ∈ A, 4 := sum_congr rfl fun x hx => min_eq_left (hhigh x hx)
        _ = _ := by simp [mul_comm]
    have hc : (∑ x ∈ P \ A, min 4 (dg G (Y ∪ R) x)) = ec G (P \ A) (Y ∪ R) := by
      exact sum_congr rfl fun x hx => min_eq_right (hlow x hx)
    unfold capped
    omega
  have hsum := ec_sdiff_add_left (G := G) hA (Y ∪ R)
  have hdegree : (ec G P (Y ∪ R) : ℤ) = 6 * #Y - df G P Y + ec G P R := by
    rw [ec_union_right hdr, Nat.cast_add, df_eq, ec_comm Y P]
    ring
  have hdY : df G P Y ≤ 2 * #Y := by
    unfold df
    calc (∑ y ∈ Y, (6 - (dg G P y : ℤ))) ≤ ∑ _y ∈ Y, (2 : ℤ) :=
        sum_le_sum fun y hy => by have := hminY y hy; omega
      _ = _ := by simp [mul_comm]
  have heps : 0 ≤ df G Q A := df_nonneg fun x hx => hcap x (hA hx)
  have hbound : (ec G P R : ℤ) + 6 - df G P Y - 2 * #R ≤ rankTerm G P Y R ∨
      (ec G P R : ℤ) ≤ rankTerm G P Y R := by
    rcases A.eq_empty_or_nonempty with hempty | ⟨x,hx⟩
    · right
      have he : capped G P (Y ∪ R) = ec G P (Y ∪ R) := by
        rw [hempty] at hsplitcap
        simpa only [card_empty, mul_zero, zero_add, sdiff_empty] using hsplitcap
      unfold rankTerm
      rw [he]
      omega
    · left
      have hsizeR : 5 ≤ #(Y ∪ R) := by
        have hh := (mem_filter.mp hx).2
        exact hh.trans (dg_le_card (Y ∪ R) x)
      have hsizeA := card_pos.mpr (show A.Nonempty from ⟨x,hx⟩)
      have hf := hfloor A hA (Y ∪ R) (union_subset hY hR) (by omega)
      have hcard := card_union_of_disjoint hdr
      have hcomplement := ec_sdiff_add_right (G := G) (union_subset hY hR) A
      have hepsEq := df_eq (G := G) Q A
      unfold gv at hf
      unfold rankTerm
      omega
  rcases hbound with hb | hb
  · have hm : df G P Y + 2 * #R - 6 ≤ max 0 (df G P Y + 2 * #R - 6) := le_max_right _ _
    omega
  · have hm : (0 : ℤ) ≤ max 0 (df G P Y + 2 * #R - 6) := le_max_left _ _
    omega

/-- Actual-original specialization, preserving Y/R incidences and original scars. -/
lemma Split.capped_rank_lower {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    {Y R : Finset V} (hY : Y ⊆ W₁) (hR : R ⊆ S) :
    (ec G U₁ R : ℤ) - max 0 (df G U Y + 2 * #R - 6) ≤ rankTerm G U₁ Y R := by
  have hdef : df G U₁ Y = df G U Y := by
    unfold df
    exact sum_congr rfl fun y hy => by rw [h.degree_right (hY hy)]
  rw [← hdef]
  apply Erdos585.QB7SmallLobeR643.capped_rank_lower
    (hY.trans subset_union_left) (hR.trans subset_union_right)
    (h.rightSep₁.mono hY hR)
  · intro x hx
    rw [h.degree_left hx]
    exact hi.capU x (h.subsets.1 hx)
  · intro y hy
    rw [h.degree_right (hY hy)]
    exact hi.minW y (h.subsets.2.2.1 (hY hy))
  · exact fun A hA T hT hn => h.local_floor hi hA hT hn

#print axioms capped_rank_lower
#print axioms Split.capped_rank_lower

lemma capped_partition (P T : Finset V) :
    ∃ A : Finset V, A ⊆ P ∧
      capped G P T = ec G A T + 4 * #(P \ A) := by
  let A := P.filter fun x => dg G T x ≤ 4
  have hA : A ⊆ P := filter_subset _ _
  refine ⟨A,hA,?_⟩
  have hs := sum_sdiff hA (f := fun x => min 4 (dg G T x))
  have hlow : (∑ x ∈ A, min 4 (dg G T x)) = ec G A T := by
    exact sum_congr rfl fun x hx => min_eq_right (mem_filter.mp hx).2
  have hhigh : (∑ x ∈ P \ A, min 4 (dg G T x)) = 4 * #(P \ A) := by
    calc _ = ∑ _x ∈ P \ A, 4 := sum_congr rfl fun x hx => by
          apply min_eq_left
          have hn : ¬ dg G T x ≤ 4 := by
            intro hh
            exact (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨(mem_sdiff.mp hx).1,hh⟩)
          omega
      _ = _ := by simp [mul_comm]
  unfold capped
  omega

lemma single_omission_capped_full {P K S Y : Finset V} {z : V}
    (hKS : Disjoint K S) (hY : Y ⊆ K.erase z) (hz : z ∈ K)
    (hbalance : #P = #K + 1)
    (hmin : ∀ x ∈ P, 5 ≤ dg G (K ∪ S) x)
    (hcap : ∀ x ∈ P, dg G (K ∪ S) x ≤ 6)
    (hrcap : ∀ y ∈ K ∪ S, dg G P y ≤ 6)
    (hscar : df G (K ∪ S) P ≤ 1)
    (hfloor : ∀ A ⊆ P, ∀ T ⊆ K ∪ S, 4 ≤ #A + #T → 16 ≤ gv G A T)
    (hzd : dg G P z ≤ 5) : 8 ≤ rankTerm G P Y S := by
  let C := K.erase z \ Y
  have hC : C ⊆ (K ∪ S).erase z := by
    intro x hx
    obtain ⟨hnez,hxK⟩ := mem_erase.mp (mem_sdiff.mp hx).1
    exact mem_erase.mpr ⟨hnez,mem_union_left _ hxK⟩
  have hdiff : (K ∪ S).erase z \ C = Y ∪ S := by
    have hzs : z ∉ S := fun hs => disjoint_left.mp hKS hz hs
    ext x
    simp only [mem_sdiff, mem_erase, mem_union, C]
    constructor
    · rintro ⟨⟨hnez,hxK|hxS⟩,hn⟩
      · exact Or.inl (by by_contra hny; exact hn ⟨⟨hnez,hxK⟩,hny⟩)
      · exact Or.inr hxS
    · rintro (hxY|hxS)
      · obtain ⟨hnez,hxK⟩ := mem_erase.mp (hY hxY)
        exact ⟨⟨hnez,Or.inl hxK⟩, fun hh => hh.2 hxY⟩
      · exact ⟨⟨fun he => hzs (he ▸ hxS),Or.inr hxS⟩,
          fun hh => disjoint_left.mp hKS hh.1.2 hxS⟩
  obtain ⟨A,hA,he⟩ := capped_partition (G := G) P (Y ∪ S)
  have hc := single_omission_cut hmin hcap hrcap hscar hfloor
    (mem_union_left S hz) hzd hA hC
  rw [hdiff] at hc
  dsimp [C] at hc
  have hPA := card_sdiff_add_card_eq_card hA
  have hKY := card_sdiff_add_card_eq_card hY
  have hKz := card_erase_add_one hz
  unfold rankTerm
  omega

lemma Split.rank_full {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    {z : V} (hz : z ∈ W₁) (hzd : dg G U z < 6)
    {Y : Finset V} (hY : Y ⊆ W₁.erase z) :
    8 ≤ rankTerm G U₁ Y S := by
  apply single_omission_capped_full h.rightSep₁ hY hz (h.local_balance hi)
  · intro x hx
    rw [h.degree_left hx]
    exact hi.minU_five x (h.subsets.1 hx)
  · intro x hx
    rw [h.degree_left hx]
    exact hi.capU x (h.subsets.1 hx)
  · intro y hy
    exact (dg_mono (G := G) h.subsets.1 y).trans
      (hi.capW y ((union_subset h.subsets.2.2.1 h.separator) hy))
  · exact (h.local_scar hi).2
  · exact fun A hA T hT hn => h.local_floor hi hA hT hn
  · rw [h.degree_right hz]
    omega

#print axioms Split.rank_full

lemma ec_insert_right {X T : Finset V} {z : V} (hz : z ∉ T) :
    ec G X (insert z T) = dg G X z + ec G X T := by
  rw [ec_comm X (insert z T), ec_comm X T]
  exact sum_insert hz

lemma Split.boundary_complement_lower {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) {s : V} (hs : s ∈ S) :
    8 - df G (W₁ ∪ S) U₁ ≤ (ec G U₁ (S.erase s) : ℤ) := by
  have hsk : s ∉ W₁ := fun hk => disjoint_left.mp h.rightSep₁ hk hs
  have hright : insert s W₁ ⊆ W₁ ∪ S := by
    intro x hx
    rcases mem_insert.mp hx with rfl|hx
    · exact mem_union_right _ hs
    · exact mem_union_left _ hx
  have hp := h.left_large hi
  have hf := h.local_floor hi (Subset.refl U₁) hright (by omega)
  have hc := h.local_balance hi
  have he := ec_union_right (G := G) h.rightSep₁ U₁
  have hz := ec_erase_right (G := G) (P := U₁) hs
  have hcs := card_insert_of_notMem hsk
  unfold gv at hf
  rw [ec_insert_right hsk] at hf
  rw [df_eq]
  omega

/-- The R637 one-port cut cap-three argument, including every tiny support.
It applies to the same fixed deficient omission throughout. -/
lemma single_port_deficit_le_three {P K S X Y : Finset V} {z s : V}
    (hKS : Disjoint K S) (hz : z ∈ K) (hs : s ∈ S)
    (hX : X ⊆ P) (hY : Y ⊆ K.erase z)
    (hbalance : #P = #K + 1)
    (hcap : ∀ x ∈ P, dg G (K ∪ S) x ≤ 6)
    (hkcap : ∀ y ∈ K, dg G P y ≤ 6)
    (hscar : df G (K ∪ S) P ≤ 1)
    (hret : df G P (K.erase z) ≤ 6)
    (hfloor : ∀ A ⊆ P, ∀ T ⊆ K ∪ S, 4 ≤ #A + #T → 16 ≤ gv G A T)
    (hboundary : 8 - df G (K ∪ S) P ≤ (ec G P (S.erase s) : ℤ)) :
    4 * ((#X : ℤ) - #Y) - ec G X (K.erase z \ Y) - ec G X (S.erase s) ≤ 3 := by
  let C := P \ X
  let Z := K.erase z \ Y
  let q : ℤ := (#X : ℤ) - #Y - 2
  have hCY := ec_sdiff_add_left (G := G) hX Y
  have hCZ := ec_sdiff_add_left (G := G) hX Z
  have hCR := ec_sdiff_add_left (G := G) hX (S.erase s)
  have hCQ := ec_union_right (G := G) hKS C
  have hXQ := ec_union_right (G := G) hKS X
  have hCXK := ec_erase_right (G := G) (P := C) hz
  have hXXK := ec_erase_right (G := G) (P := X) hz
  have hCXret := ec_sdiff_add_right (G := G) hY C
  have hXXret := ec_sdiff_add_right (G := G) hY X
  have hCXs := ec_erase_right (G := G) (P := C) hs
  have hXXs := ec_erase_right (G := G) (P := X) hs
  have hcardC := card_sdiff_add_card_eq_card hX
  have hcardZ := card_sdiff_add_card_eq_card hY
  have hcardK := card_erase_add_one hz
  have hdeltaZ : df G P Z ≤ 6 := (df_le_of_subset (G := G) (S := P)
    (sdiff_subset : Z ⊆ K.erase z) (fun y hy => hkcap y (mem_erase.mp hy).2)).trans hret
  have hepsX : df G (K ∪ S) X ≤ 1 :=
    (df_le_of_subset (G := G) (S := K ∪ S) hX hcap).trans hscar
  have hepsC : 0 ≤ df G (K ∪ S) C := df_nonneg fun x hx => hcap x (sdiff_subset hx)
  have hdZ := df_eq (G := G) P Z
  have hdX := df_eq (G := G) (K ∪ S) X
  have hdC := df_eq (G := G) (K ∪ S) C
  have hcZ := ec_comm (G := G) Z P
  have hu : 4 * ((#X : ℤ) - #Y) - ec G X Z - ec G X (S.erase s) ≤ 7 - 2 * q := by
    dsimp [C,Z] at *
    dsimp [q]
    omega
  by_cases hq : q ≤ 2
  · have hzy : z ∉ Y := fun hzY => (mem_erase.mp (hY hzY)).1 rfl
    have hsK : s ∉ K := fun hsK => disjoint_left.mp hKS hsK hs
    have hsy : s ∉ Y := fun hsY => hsK ((mem_erase.mp (hY hsY)).2)
    have hsz : s ≠ z := fun he => hsK (he ▸ hz)
    have hsmallcard : #(insert s (insert z Y)) = #Y + 2 := by
      rw [card_insert_of_notMem (by simp only [mem_insert]; exact not_or.mpr ⟨hsz,hsy⟩),
        card_insert_of_notMem hzy]
    have hsmallsubset : insert s (insert z Y) ⊆ K ∪ S := by
      intro x hx
      rcases mem_insert.mp hx with rfl|hx
      · exact mem_union_right _ hs
      rcases mem_insert.mp hx with rfl|hx
      · exact mem_union_left _ hz
      · exact mem_union_left _ ((mem_erase.mp (hY hx)).2)
    have hsmallE : ec G X (insert s (insert z Y)) =
        dg G X s + dg G X z + ec G X Y := by
      rw [ec_insert_right (by simp only [mem_insert]; exact not_or.mpr ⟨hsz,hsy⟩),
        ec_insert_right hzy]
      omega
    by_cases hn : 4 ≤ #X + #(insert s (insert z Y))
    · have hf := hfloor X hX (insert s (insert z Y)) hsmallsubset hn
      unfold gv at hf
      dsimp [q] at hq
      dsimp [Z] at *
      omega
    · have hp := ec_product_bound (G := G) X (insert s (insert z Y))
      by_cases hx0 : #X = 0
      · have hXe : X = ∅ := card_eq_zero.mp hx0
        simp [hXe,ec] at *
        omega
      · have hx1 : #X = 1 := by omega
        have hy0 : #Y = 0 := by omega
        rw [hx1,hsmallcard,hy0] at hp
        norm_num at hp
        dsimp [Z] at *
        omega
  · dsimp [Z] at hu
    omega

#print axioms single_port_deficit_le_three

lemma rank_erase_port_lower {P K S Y : Finset V} {z s : V}
    (hKS : Disjoint K S) (hz : z ∈ K) (hs : s ∈ S) (hY : Y ⊆ K.erase z)
    (hbalance : #P = #K + 1)
    (hcap : ∀ x ∈ P, dg G (K ∪ S) x ≤ 6)
    (hkcap : ∀ y ∈ K, dg G P y ≤ 6)
    (hscar : df G (K ∪ S) P ≤ 1) (hret : df G P (K.erase z) ≤ 6)
    (hfloor : ∀ A ⊆ P, ∀ T ⊆ K ∪ S, 4 ≤ #A + #T → 16 ≤ gv G A T)
    (hboundary : 8 - df G (K ∪ S) P ≤ (ec G P (S.erase s) : ℤ)) :
    5 ≤ rankTerm G P Y (S.erase s) := by
  obtain ⟨A,hA,he⟩ := capped_partition (G := G) P (Y ∪ S.erase s)
  have hc := single_port_deficit_le_three hKS hz hs hA
    (sdiff_subset : K.erase z \ Y ⊆ K.erase z)
    hbalance hcap hkcap hscar hret hfloor hboundary
  rw [Finset.sdiff_sdiff_eq_self hY] at hc
  have hYS : Disjoint Y (S.erase s) := hKS.mono (hY.trans (erase_subset z K)) (erase_subset s S)
  have hsplit := ec_union_right (G := G) hYS A
  have hPA := card_sdiff_add_card_eq_card hA
  have hKY := card_sdiff_add_card_eq_card hY
  have hKz := card_erase_add_one hz
  unfold rankTerm
  omega

lemma Split.rank_erase_port {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    {z s : V} (hz : z ∈ W₁) (hs : s ∈ S) (hret : df G U (W₁.erase z) ≤ 6)
    {Y : Finset V} (hY : Y ⊆ W₁.erase z) : 5 ≤ rankTerm G U₁ Y (S.erase s) := by
  have hdef : df G U₁ (W₁.erase z) = df G U (W₁.erase z) := by
    unfold df
    exact sum_congr rfl fun y hy => by rw [h.degree_right (mem_erase.mp hy).2]
  apply rank_erase_port_lower h.rightSep₁ hz hs hY (h.local_balance hi)
  · intro x hx
    rw [h.degree_left hx]
    exact hi.capU x (h.subsets.1 hx)
  · intro y hy
    rw [h.degree_right hy]
    exact hi.capW y (h.subsets.2.2.1 hy)
  · exact (h.local_scar hi).2
  · rwa [hdef]
  · exact fun A hA T hT hn => h.local_floor hi hA hT hn
  · exact h.boundary_complement_lower hi hs

lemma Split.small_degree_subset {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) (hsmall : #U₁ = 4)
    {Y : Finset V} (hY : Y ⊆ W₁) {x : V} (hx : x ∈ U₁) : dg G Y x = #Y := by
  unfold dg
  exact card_filter_eq_iff.mpr fun y hy => h.small_complete hi hsmall x hx y (hY hy)

lemma Split.small_rank_low {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) (hsmall : #U₁ = 4)
    {z : V} (hz : z ∈ W₁) {Y R : Finset V}
    (hY : Y ⊆ W₁.erase z) (hR : R ⊆ S) (hr : #R ≤ 2) :
    rankTerm G U₁ Y R = (ec G U₁ R : ℤ) := by
  have hY₁ := hY.trans (erase_subset z W₁)
  have hcardY : #Y ≤ 2 := by
    have hK := (h.small_interior_degree hi hsmall).1
    have hret := card_erase_add_one hz
    have := card_le_card hY
    omega
  have hYS := h.rightSep₁.mono hY₁ hR
  have hcap : capped G U₁ (Y ∪ R) = ec G U₁ (Y ∪ R) := by
    unfold capped ec
    apply sum_congr rfl
    intro x hx
    apply min_eq_right
    rw [dg_union_of_disjoint hYS, h.small_degree_subset hi hsmall hY₁ hx]
    have := dg_le_card (G := G) R x
    omega
  have hleft : ec G U₁ Y = 4 * #Y := by
    unfold ec
    calc ∑ x ∈ U₁, dg G Y x = ∑ _x ∈ U₁, #Y :=
        sum_congr rfl fun x hx => h.small_degree_subset hi hsmall hY₁ hx
      _ = _ := by simp [hsmall,mul_comm]
  unfold rankTerm
  rw [hcap,ec_union_right hYS,hleft]
  push_cast
  omega

lemma Split.small_rank_three {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) (hsmall : #U₁ = 4)
    {z s : V} (hz : z ∈ W₁) (_hs : s ∈ S)
    {Y : Finset V} (hY : Y ⊆ W₁.erase z) : 7 ≤ rankTerm G U₁ Y (S.erase s) := by
  have hY₁ := hY.trans (erase_subset z W₁)
  have hcardK := (h.small_interior_degree hi hsmall).1
  have hcardY : #Y ≤ 2 := by
    have hret := card_erase_add_one hz
    have := card_le_card hY
    omega
  have hYS := h.rightSep₁.mono hY₁ (erase_subset s S)
  have hscar := (h.local_scar hi).2
  have hrow : ∀ x ∈ U₁,
      (6 - (dg G (W₁ ∪ S) x : ℤ)) +
        (min 4 (dg G (Y ∪ S.erase s) x) : ℤ) ≥ 2 + #Y := by
    intro x hx
    have hK := h.small_degree_subset hi hsmall (Subset.refl W₁) hx
    have hYdegree := h.small_degree_subset hi hsmall hY₁ hx
    have hfull := dg_union_of_disjoint (G := G) h.rightSep₁ x
    have hretain := dg_union_of_disjoint (G := G) hYS x
    have hloss := dg_erase_loss (G := G) S s x
    have hcap := hi.capU x (h.subsets.1 hx)
    rw [← h.degree_left hx] at hcap
    omega
  have hsum : 8 + 4 * (#Y : ℤ) ≤
      df G (W₁ ∪ S) U₁ + (capped G U₁ (Y ∪ S.erase s) : ℤ) := by
    have he := sum_le_sum hrow
    simp only [sum_add_distrib, sum_const, nsmul_eq_mul, hsmall,
      df, capped, Nat.cast_sum, Nat.cast_min, Nat.cast_ofNat] at he ⊢
    omega
  unfold df at hscar hsum
  unfold rankTerm
  omega

#print axioms Split.rank_erase_port
#print axioms Split.small_rank_low
#print axioms Split.small_rank_three

/-- All sixteen outer separator cuts for the same arbitrary original omissions.
Every interior Y is quantified, so no unproved rank/profile supplier is used. -/
theorem Split.fixed_omission_rank_cuts {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) (hsmall : #U₁ = 4)
    {z₁ z₂ : V} (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6)
    {Y₁ Y₂ R : Finset V} (hY₁ : Y₁ ⊆ W₁.erase z₁)
    (hY₂ : Y₂ ⊆ W₂.erase z₂) (hR : R ⊆ S) :
    4 * (#R : ℤ) ≤ rankTerm G U₁ Y₁ R + rankTerm G U₂ Y₂ R := by
  have hscars := h.small_scar hi hsmall
  have hS := h.cardS
  have hrets := h.small_retained_scar hi hsmall hz₁ hz₂ hd₂
  have hRmax : #R ≤ 4 := by have := card_le_card hR; omega
  by_cases hrlo : #R ≤ 2
  · have hfirst := h.small_rank_low hi hsmall hz₁ hY₁ hR hrlo
    have hsecond := h.swap.capped_rank_lower hi (hY₂.trans (erase_subset z₂ W₂)) hR
    have hdefY : df G U Y₂ ≤ df G U (W₂.erase z₂) :=
      df_le_of_subset hY₂ fun y hy => hi.capW y (h.subsets.2.2.2 (mem_erase.mp hy).2)
    have hdefRet : df G U (W₂.erase z₂) + df G U S ≤ 6 := by
      have he : df G U (W₂.erase z₂) + (6 - (dg G U z₂ : ℤ)) = df G U W₂ :=
        sum_erase_add W₂ (fun y => 6 - (dg G U y : ℤ)) hz₂
      omega
    have hdefR : df G U R ≤ df G U S :=
      df_le_of_subset hR fun y hy => hi.capW y (h.separator hy)
    have hdefRcap : df G U R ≤ 2 * #R := by
      unfold df
      calc (∑ y ∈ R, (6 - (dg G U y : ℤ))) ≤ ∑ _y ∈ R, (2 : ℤ) :=
          sum_le_sum fun y hy => by have := hi.minW y (h.separator (hR hy)); omega
        _ = _ := by simp [mul_comm]
    have hloss : max 0 (df G U Y₂ + 2 * #R - 6) ≤ 2 * #R - df G U R := by
      apply max_le
      · omega
      · omega
    have he := ec_union_left (G := G) h.leftDisjoint R
    rw [h.leftCover] at he
    have hdR := df_eq (G := G) U R
    have hec := ec_comm (G := G) R U
    omega
  · by_cases hr3 : #R = 3
    · have hd := card_sdiff_add_card_eq_card hR
      have hdiffone : #(S \ R) = 1 := by omega
      obtain ⟨s,hsing⟩ := card_eq_one.mp hdiffone
      have hs : s ∈ S := (mem_sdiff.mp (show s ∈ S \ R by rw [hsing]; simp)).1
      have hReq : R = S.erase s := by
        have he := Finset.sdiff_sdiff_eq_self hR
        rw [hsing] at he
        simpa only [sdiff_singleton_eq_erase] using he.symm
      rw [hReq]
      have hfirst := h.small_rank_three hi hsmall hz₁ hs hY₁
      have hsecond := h.swap.rank_erase_port hi hz₂ hs hrets.2 hY₂
      have hc := card_erase_add_one hs
      omega
    · have hr4 : #R = 4 := by omega
      have hReq : R = S := eq_of_subset_of_card_le hR (by omega)
      rw [hReq]
      have hfirst := h.rank_full hi hz₁ hd₁ hY₁
      have hsecond := h.swap.rank_full hi hz₂ hd₂ hY₂
      have hc := h.cardS
      omega

#print axioms Split.fixed_omission_rank_cuts

lemma capped_upper_split {P A T : Finset V} (hA : A ⊆ P) :
    capped G P T ≤ ec G A T + 4 * #(P \ A) := by
  have hs := sum_sdiff hA (f := fun x => min 4 (dg G T x))
  have hl : (∑ x ∈ A, min 4 (dg G T x)) ≤ ec G A T :=
    sum_le_sum fun _x _hx => min_le_right _ _
  have hr : (∑ x ∈ P \ A, min 4 (dg G T x)) ≤ 4 * #(P \ A) := by
    calc _ ≤ ∑ _x ∈ P \ A, 4 := sum_le_sum fun _x _hx => min_le_left _ _
      _ = _ := by simp [mul_comm]
  unfold capped
  omega

/-- Standard unit-edge Hall transport for the explicitly proved capped cuts. -/
lemma factor_of_right_capped {P Q : Finset V} (hcard : #P = #Q)
    (hcut : ∀ T ⊆ Q, 4 * #T ≤ capped G P T) :
    ∃ F : Finset (V × V), F ⊆ P ×ˢ Q ∧ (∀ e ∈ F, G.Adj e.1 e.2) ∧
      (∀ x ∈ P, #{e ∈ F | e.1 = x} = 4) ∧
      (∀ y ∈ Q, #{e ∈ F | e.2 = y} = 4) := by
  apply exists_four_factor P Q hcard
  intro A hA C hC
  have hc := hcut (Q \ C) sdiff_subset
  have hu := capped_upper_split (G := G) (T := Q \ C) hA
  have hPA := card_sdiff_add_card_eq_card hA
  have hQC := card_sdiff_add_card_eq_card hC
  omega

omit [DecidableRel G.Adj] in
lemma Split.retained_cover {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) {z₁ z₂ : V} (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂) :
    (W.erase z₁).erase z₂ = (W₁.erase z₁) ∪ (W₂.erase z₂) ∪ S := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx2,hx⟩ := mem_erase.mp hx
    obtain ⟨hx1,hxW⟩ := mem_erase.mp hx
    rw [← h.rightCover] at hxW
    rcases mem_union.mp hxW with hx12|hxS
    · rcases mem_union.mp hx12 with hxK1|hxK2
      · exact mem_union_left _ (mem_union_left _ (mem_erase.mpr ⟨hx1,hxK1⟩))
      · exact mem_union_left _ (mem_union_right _ (mem_erase.mpr ⟨hx2,hxK2⟩))
    · exact mem_union_right _ hxS
  · intro hx
    rcases mem_union.mp hx with hx12|hxS
    · rcases mem_union.mp hx12 with hxK1|hxK2
      · obtain ⟨hne1,hxK1⟩ := mem_erase.mp hxK1
        have hne2 : x ≠ z₂ := fun he => disjoint_left.mp h.rightDisjoint hxK1 (he ▸ hz₂)
        exact mem_erase.mpr ⟨hne2,mem_erase.mpr ⟨hne1,h.subsets.2.2.1 hxK1⟩⟩
      · obtain ⟨hne2,hxK2⟩ := mem_erase.mp hxK2
        have hne1 : x ≠ z₁ := fun he => disjoint_left.mp h.rightDisjoint (he ▸ hz₁) hxK2
        exact mem_erase.mpr ⟨hne2,mem_erase.mpr ⟨hne1,h.subsets.2.2.2 hxK2⟩⟩
    · have hne1 : x ≠ z₁ := fun he => disjoint_left.mp h.rightSep₁ (he ▸ hz₁) hxS
      have hne2 : x ≠ z₂ := fun he => disjoint_left.mp h.rightSep₂ (he ▸ hz₂) hxS
      exact mem_erase.mpr ⟨hne2,mem_erase.mpr ⟨hne1,h.separator hxS⟩⟩

lemma Split.retained_balanced {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    {z₁ z₂ : V} (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂) :
    #U = #((W.erase z₁).erase z₂) := by
  have hne : z₂ ≠ z₁ := fun he => disjoint_left.mp h.rightDisjoint (he ▸ hz₁) hz₂
  have h1 := card_erase_add_one (h.subsets.2.2.1 hz₁)
  have h2 := card_erase_add_one (mem_erase.mpr ⟨hne,h.subsets.2.2.2 hz₂⟩)
  have hc := hi.card
  omega

lemma Split.retained_capped_cuts {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) (hsmall : #U₁ = 4)
    {z₁ z₂ : V} (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6)
    {T : Finset V} (hT : T ⊆ (W.erase z₁).erase z₂) :
    4 * #T ≤ capped G U T := by
  let Y₁ := T ∩ W₁.erase z₁
  let Y₂ := T ∩ W₂.erase z₂
  let R := T ∩ S
  have hY₁ : Y₁ ⊆ W₁.erase z₁ := inter_subset_right
  have hY₂ : Y₂ ⊆ W₂.erase z₂ := inter_subset_right
  have hR : R ⊆ S := inter_subset_right
  have hY₁K : Y₁ ⊆ W₁ := hY₁.trans (erase_subset z₁ W₁)
  have hY₂K : Y₂ ⊆ W₂ := hY₂.trans (erase_subset z₂ W₂)
  have hY₁₂ : Disjoint Y₁ Y₂ := h.rightDisjoint.mono hY₁K hY₂K
  have hY₁R : Disjoint Y₁ R := h.rightSep₁.mono hY₁K hR
  have hY₂R : Disjoint Y₂ R := h.rightSep₂.mono hY₂K hR
  have hcover : Y₁ ∪ Y₂ ∪ R = T := by
    ext x
    constructor
    · intro hx
      rcases mem_union.mp hx with hxy|hxr
      · rcases mem_union.mp hxy with hx1|hx2
        · exact (mem_inter.mp hx1).1
        · exact (mem_inter.mp hx2).1
      · exact (mem_inter.mp hxr).1
    · intro hx
      have hxQ := hT hx
      rw [h.retained_cover hz₁ hz₂] at hxQ
      rcases mem_union.mp hxQ with hx12|hxs
      · rcases mem_union.mp hx12 with hx1|hx2
        · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hx,hx1⟩))
        · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨hx,hx2⟩))
      · exact mem_union_right _ (mem_inter.mpr ⟨hx,hxs⟩)
  have hcard : #T = #Y₁ + #Y₂ + #R := by
    rw [← hcover,card_union_of_disjoint (disjoint_union_left.mpr ⟨hY₁R,hY₂R⟩),
      card_union_of_disjoint hY₁₂]
  have hleft : ∀ x ∈ U₁, dg G T x = dg G (Y₁ ∪ R) x := by
    intro x hx
    have he : (Y₁ ∪ R) ∪ Y₂ = T := by
      rw [union_assoc,union_comm R Y₂,← union_assoc,hcover]
    have hd := dg_union_of_disjoint (G := G)
      (disjoint_union_left.mpr ⟨hY₁₂,hY₂R.symm⟩) x
    have hz : dg G Y₂ x = 0 := dg_zero fun y hy => h.cross₁ x hx y (hY₂K hy)
    rw [he,hz] at hd
    omega
  have hright : ∀ x ∈ U₂, dg G T x = dg G (Y₂ ∪ R) x := by
    intro x hx
    have he : (Y₂ ∪ R) ∪ Y₁ = T := by
      rw [union_assoc,union_comm R Y₁,← union_assoc,union_comm Y₂ Y₁,hcover]
    have hd := dg_union_of_disjoint (G := G)
      (disjoint_union_left.mpr ⟨hY₁₂.symm,hY₁R.symm⟩) x
    have hz : dg G Y₁ x = 0 := dg_zero fun y hy => h.cross₂ x hx y (hY₁K hy)
    rw [he,hz] at hd
    omega
  have hcap : capped G U T = capped G U₁ (Y₁ ∪ R) + capped G U₂ (Y₂ ∪ R) := by
    unfold capped
    rw [← h.leftCover,sum_union h.leftDisjoint]
    congr 1
    · exact sum_congr rfl fun x hx => by rw [hleft x hx]
    · exact sum_congr rfl fun x hx => by rw [hright x hx]
  have hcuts := h.fixed_omission_rank_cuts hi hsmall hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR
  unfold rankTerm at hcuts
  omega

/-- all-order small-lobe endpoint. The same arbitrary original omission
pair is used in every cut and in the single constructed unit-edge witness. -/
theorem small_lobe_fixed_omissions {U W S U₁ U₂ W₁ W₂ : Finset V}
    (hi : U2Input G U W) (h : Split G U W S U₁ U₂ W₁ W₂) (hsmall : #U₁ = 4)
    {z₁ z₂ : V} (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6) :
    FixedOmissionFactor G U W z₁ z₂ := by
  exact factor_of_right_capped (h.retained_balanced hi hz₁ hz₂)
    (fun T hT => h.retained_capped_cuts hi hsmall hz₁ hz₂ hd₁ hd₂ hT)

theorem smallLobeClaim : SmallLobeClaim (G := G) := by
  intro U W S U₁ U₂ W₁ W₂ hi h hsmall z₁ hz₁ z₂ hz₂ hd₁ hd₂
  exact small_lobe_fixed_omissions hi h hsmall hz₁ hz₂ hd₁ hd₂

#print axioms small_lobe_fixed_omissions
#print axioms smallLobeClaim

end Erdos585.QB7SmallLobeR643
