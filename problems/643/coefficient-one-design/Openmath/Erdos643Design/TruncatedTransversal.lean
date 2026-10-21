import Openmath.Erdos643Design.TransversalFoundation
import Openmath.Erdos643Design.DesignTransport

/-! Truncation of one group of an actual transversal design.
The resulting pairwise-balanced design is constructed explicitly. -/
set_option autoImplicit false

namespace Erdos643Design.TruncatedTransversal
open Finset

abbrev Point (k t u : ℕ) := (Fin k × Fin t) ⊕ Fin u

variable {k t u : ℕ}

def column : Point k t u → Fin (k + 1)
  | .inl p => p.1.castSucc
  | .inr _ => Fin.last k

def symbol (hu : u ≤ t) : Point k t u → Fin t
  | .inl p => p.2
  | .inr a => a.castLE hu

theorem point_ext (hu : u ≤ t) {p q : Point k t u}
    (hc : column p = column q) (hs : symbol hu p = symbol hu q) : p = q := by
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      apply congrArg Sum.inl
      exact Prod.ext (Fin.castSucc_injective k hc) hs
    | inr q => exact False.elim (Fin.castSucc_ne_last p.1 hc)
  | inr p =>
    cases q with
    | inl q => exact False.elim (Fin.castSucc_ne_last q.1 hc.symm)
    | inr q =>
      apply congrArg Sum.inr
      apply Fin.ext
      exact congrArg (fun z : Fin t => z.val) hs

def mainRow (r : Fin (k + 1) → Fin t) : Finset (Point k t u) :=
  univ.image (fun i : Fin k => Sum.inl (i, r i.castSucc))

def rowBlock (r : Fin (k + 1) → Fin t) : Finset (Point k t u) :=
  mainRow r ∪ if h : (r (Fin.last k)).val < u then {Sum.inr ⟨_, h⟩} else ∅

theorem mainRow_card (r : Fin (k + 1) → Fin t) :
    (mainRow (u := u) r).card = k := by
  rw [mainRow, card_image_iff.mpr, card_univ, Fintype.card_fin]
  intro i _ j _ h
  exact congrArg Prod.fst (Sum.inl.inj h)

theorem mem_rowBlock (hu : u ≤ t) (r : Fin (k + 1) → Fin t) (p : Point k t u) :
    p ∈ rowBlock r ↔ r (column p) = symbol hu p := by
  cases p with
  | inl p =>
    rcases p with ⟨i,a⟩
    unfold rowBlock
    split_ifs <;> simp [mainRow, column, symbol]
  | inr a =>
    unfold rowBlock
    split_ifs with h
    · simp only [mem_union,mainRow,mem_image,mem_univ,true_and,Sum.inl_ne_inr,
        exists_false,false_or,mem_singleton,Sum.inr.injEq,column,symbol]
      constructor
      · intro he
        apply Fin.ext
        exact (congrArg (fun z : Fin u => z.val) he).symm
      · intro he
        apply Fin.ext
        exact (congrArg (fun z : Fin t => z.val) he).symm
    · simp only [mem_union,mainRow,mem_image,mem_univ,true_and,Sum.inl_ne_inr,
        exists_false,false_or,Finset.notMem_empty,false_iff,column,symbol]
      intro he
      exact h (by simpa only [he, Fin.val_castLE] using a.isLt)

theorem rowBlock_card (r : Fin (k + 1) → Fin t) :
    (rowBlock (u := u) r).card = k ∨ (rowBlock (u := u) r).card = k + 1 := by
  have hd : ∀ a : Fin u, Disjoint (mainRow r) {Sum.inr a} := by
    intro a
    apply disjoint_left.mpr
    intro p hp hp'
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    simp at hp'
  unfold rowBlock
  split_ifs with h
  · right
    rw [card_union_of_disjoint (hd _), mainRow_card, card_singleton]
  · left
    simp [mainRow_card]

def groupBlock (i : Fin (k + 1)) : Finset (Point k t u) :=
  univ.filter (fun p => column p = i)

@[simp] theorem mem_groupBlock (i : Fin (k + 1)) (p : Point k t u) :
    p ∈ groupBlock i ↔ column p = i := by simp [groupBlock]

theorem groupBlock_cast (i : Fin k) :
    groupBlock (t := t) (u := u) i.castSucc =
      univ.image (fun a : Fin t => (Sum.inl (i,a) : Point k t u)) := by
  ext p
  cases p with
  | inl p => simp [column, Fin.castSucc_inj, Prod.eq_iff_fst_eq_snd_eq,eq_comm]
  | inr a => simp [column, Ne.symm (Fin.castSucc_ne_last i)]

theorem groupBlock_last :
    groupBlock (k := k) (t := t) (u := u) (Fin.last k) =
      univ.image (fun a : Fin u => (Sum.inr a : Point k t u)) := by
  ext p
  cases p with
  | inl p => simp [column, Fin.castSucc_ne_last]
  | inr a => simp [column]

theorem groupBlock_card (i : Fin (k + 1)) :
    (groupBlock (t := t) (u := u) i).card = t ∨
      (groupBlock (t := t) (u := u) i).card = u := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · right
    rw [groupBlock_last, card_image_iff.mpr, card_univ, Fintype.card_fin]
    intro a _ b _ he
    exact Sum.inr.inj he
  · left
    rw [groupBlock_cast, card_image_iff.mpr, card_univ, Fintype.card_fin]
    intro a _ b _ he
    exact congrArg Prod.snd (Sum.inl.inj he)

def blocks (T : Foundation.TransversalRows (Fin (k + 1)) (Fin t)) :
    Finset (Finset (Point k t u)) :=
  T.rows.image rowBlock ∪
    (univ.filter (fun i : Fin (k + 1) => 2 ≤ (groupBlock (t := t) (u := u) i).card)).image
      groupBlock

theorem block_card (T : Foundation.TransversalRows (Fin (k + 1)) (Fin t))
    {b : Finset (Point k t u)} (hb : b ∈ blocks T) :
    b.card = k ∨ b.card = k + 1 ∨ b.card = t ∨ b.card = u := by
  rcases mem_union.mp hb with hr | hg
  · obtain ⟨r, _, rfl⟩ := mem_image.mp hr
    rcases rowBlock_card r with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hg
    exact Or.inr (Or.inr (groupBlock_card i))

theorem blocks_min_card (T : Foundation.TransversalRows (Fin (k + 1)) (Fin t))
    (hk : 2 ≤ k) {b : Finset (Point k t u)} (hb : b ∈ blocks T) : 2 ≤ b.card := by
  rcases mem_union.mp hb with hr | hg
  · obtain ⟨r, _, rfl⟩ := mem_image.mp hr
    rcases rowBlock_card r with h | h <;> omega
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp hg
    exact (mem_filter.mp hi).2

/-- An empty or singleton last group is omitted, including as a coincident row block. -/
theorem last_group_not_mem (T : Foundation.TransversalRows (Fin (k + 1)) (Fin t))
    (hk : 2 ≤ k) (hu : u ≤ 1) :
    groupBlock (k := k) (t := t) (u := u) (Fin.last k) ∉ blocks T := by
  intro hm
  have hcard : (groupBlock (k := k) (t := t) (u := u) (Fin.last k)).card = u := by
    rw [groupBlock_last,card_image_iff.mpr,card_univ,Fintype.card_fin]
    intro a _ b _ he
    exact Sum.inr.inj he
  have hl := blocks_min_card T hk hm
  omega

theorem unique_pair (T : Foundation.TransversalRows (Fin (k + 1)) (Fin t))
    (hu : u ≤ t) (p q : Point k t u) (hpq : p ≠ q) :
    ∃! b, b ∈ blocks T ∧ p ∈ b ∧ q ∈ b := by
  by_cases hc : column p = column q
  · have hp : p ∈ groupBlock (column p) := (mem_groupBlock _ _).mpr rfl
    have hq : q ∈ groupBlock (column p) := (mem_groupBlock _ _).mpr hc.symm
    have hgcard : 2 ≤ (groupBlock (t := t) (u := u) (column p)).card :=
      one_lt_card.mpr ⟨p,hp,q,hq,hpq⟩
    refine ⟨groupBlock (column p), ⟨mem_union_right _ (mem_image.mpr
      ⟨column p,mem_filter.mpr ⟨mem_univ _,hgcard⟩,rfl⟩),hp,hq⟩,?_⟩
    intro c hc'
    rcases mem_union.mp hc'.1 with hr | hg
    · obtain ⟨r, _, rfl⟩ := mem_image.mp hr
      have hs : symbol hu p = symbol hu q :=
        ((mem_rowBlock hu r p).mp hc'.2.1).symm.trans
          (hc ▸ (mem_rowBlock hu r q).mp hc'.2.2)
      exact False.elim (hpq (point_ext hu hc hs))
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hg
      exact congrArg groupBlock ((mem_groupBlock i p).mp hc'.2.1).symm
  · obtain ⟨r,hr,hru⟩ := T.pair_unique (column p) (column q) hc (symbol hu p) (symbol hu q)
    refine ⟨rowBlock r, ⟨mem_union_left _ (mem_image.mpr ⟨r,hr.1,rfl⟩),
      (mem_rowBlock hu r p).mpr hr.2.1,(mem_rowBlock hu r q).mpr hr.2.2⟩,?_⟩
    intro c hc'
    rcases mem_union.mp hc'.1 with hr' | hg
    · obtain ⟨s,hs,rfl⟩ := mem_image.mp hr'
      exact congrArg rowBlock (hru s ⟨hs,(mem_rowBlock hu s p).mp hc'.2.1,
        (mem_rowBlock hu s q).mp hc'.2.2⟩)
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hg
      exact False.elim (hc (((mem_groupBlock i p).mp hc'.2.1).trans
        ((mem_groupBlock i q).mp hc'.2.2).symm))

theorem isPairwiseBalancedDesign
    (T : Foundation.TransversalRows (Fin (k + 1)) (Fin t)) (hk : 2 ≤ k) (hu : u ≤ t) :
    (blocks (u := u) T).IsPairwiseBalancedDesign := by
  refine ⟨fun _ hb => blocks_min_card T hk hb,?_⟩
  intro S hS
  obtain ⟨p,q,hpq,rfl⟩ := card_eq_two.mp hS
  obtain ⟨b,hb,hbu⟩ := unique_pair T hu p q hpq
  refine ⟨b,⟨hb.1,?_⟩,?_⟩
  · simpa only [insert_subset_iff,singleton_subset_iff] using hb.2
  · intro c hc
    exact hbu c ⟨hc.1,hc.2 (by simp),hc.2 (by simp)⟩

theorem isPairwiseBalancedDesign_relabel {V W : Type*} [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (P : Finset (Finset V)) (hP : P.IsPairwiseBalancedDesign) :
    (DesignTransport.relabel e P).IsPairwiseBalancedDesign := by
  refine ⟨?_,?_⟩
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
    rw [card_map]
    exact hP.1 a ha
  · intro S hS
    have hT : (S.map e.symm.toEmbedding).card = 2 := by rw [card_map,hS]
    obtain ⟨b,hb,hbu⟩ := hP.2 (S.map e.symm.toEmbedding) hT
    refine ⟨b.map e.toEmbedding,⟨mem_image.mpr ⟨b,hb.1,rfl⟩,
      map_symm_subset.mp hb.2⟩,?_⟩
    intro c hc
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hc.1
    exact congrArg (fun a => a.map e.toEmbedding)
      (hbu d ⟨hd,map_symm_subset.mpr hc.2⟩)

/-- Truncating one TD group gives an actual PBD of the exact target order.
Empty and singleton final groups contribute no group block. -/
theorem exists_pbd_fin (T : Foundation.TransversalRows (Fin (k + 1)) (Fin t))
    (hk : 2 ≤ k) (hu : u ≤ t) :
    ∃ P : Finset (Finset (Fin (k * t + u))), P.IsPairwiseBalancedDesign ∧
      ∀ b ∈ P, b.card = k ∨ b.card = k + 1 ∨ b.card = t ∨ b.card = u := by
  have hc : Fintype.card (Point k t u) = k * t + u := by
    simp only [Point,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  let e := Fintype.equivFinOfCardEq hc
  refine ⟨DesignTransport.relabel e (blocks T),
    isPairwiseBalancedDesign_relabel e _ (isPairwiseBalancedDesign T hk hu),?_⟩
  intro b hb
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
  rw [card_map]
  exact block_card T ha

end Erdos643Design.TruncatedTransversal
