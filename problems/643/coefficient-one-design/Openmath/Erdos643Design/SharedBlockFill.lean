import Openmath.Erdos643Design.TransversalFoundation
import Openmath.Erdos643Design.DesignTransport
import Mathlib.Logic.Equiv.Set

/-! Shared-block filling from transversal rows and designs sharing a common block. -/
set_option autoImplicit false
namespace Erdos643Design.Foundation.SharedBlockFill
open Finset
variable {C I A : Type*} [Fintype C] [DecidableEq C]
  [Fintype I] [DecidableEq I] [DecidableEq A]

def shared : Finset (Sum C A) := univ.map ⟨Sum.inl, Sum.inl_injective⟩
def common : Finset (Sum C (I × A)) := shared
def fillEmbedding (i : I) : Sum C A ↪ Sum C (I × A) where
  toFun := Sum.map id (fun a => (i,a))
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all
def fillBlock (i : I) (b : Finset (Sum C A)) := b.map (fillEmbedding i)
def crossBlock (r : I → A) : Finset (Sum C (I × A)) :=
  (TransversalRows.rowBlock r).map ⟨Sum.inr, Sum.inr_injective⟩

omit [DecidableEq C] [DecidableEq A] in
@[simp] theorem mem_shared (x : Sum C A) : x ∈ shared ↔ ∃ c, x = Sum.inl c := by
  cases x <;> simp [shared]
omit [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I] [DecidableEq A] in
@[simp] theorem inl_fill (c : C) (i : I) (b : Finset (Sum C A)) :
    Sum.inl c ∈ fillBlock i b ↔ Sum.inl c ∈ b := by
  constructor
  · rintro h
    obtain ⟨x,hx,he⟩ := mem_map.mp h
    cases x with
    | inl d => exact (Sum.inl.inj he) ▸ hx
    | inr a => cases he
  · intro h
    exact mem_map.mpr ⟨Sum.inl c,h,rfl⟩
omit [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I] [DecidableEq A] in
@[simp] theorem inr_fill (i j : I) (a : A) (b : Finset (Sum C A)) :
    Sum.inr (i,a) ∈ fillBlock j b ↔ i = j ∧ Sum.inr a ∈ b := by
  constructor
  · intro h
    obtain ⟨x,hx,he⟩ := mem_map.mp h
    cases x with
    | inl c => cases he
    | inr b =>
      have hh : (j,b) = (i,a) := Sum.inr.inj he
      obtain ⟨hji,hba⟩ := Prod.mk.inj hh
      exact ⟨hji.symm,hba ▸ hx⟩
  · rintro ⟨rfl,h⟩
    exact mem_map.mpr ⟨Sum.inr a,h,rfl⟩
omit [Fintype C] [DecidableEq C] in
@[simp] theorem inl_cross (c : C) (r : I → A) : Sum.inl c ∉ crossBlock r := by
  simp [crossBlock]
omit [Fintype C] [DecidableEq C] in
@[simp] theorem inr_cross (i : I) (a : A) (r : I → A) :
    Sum.inr (i,a) ∈ crossBlock (C := C) r ↔ r i = a := by
  constructor
  · intro h
    obtain ⟨p,hp,he⟩ := mem_map.mp h
    have heq : p = (i,a) := Sum.inr.inj he
    subst p
    exact (TransversalRows.mem_rowBlock r i a).mp hp
  · intro h
    exact mem_map.mpr ⟨(i,a),(TransversalRows.mem_rowBlock r i a).mpr h,rfl⟩
omit [DecidableEq C] [Fintype I] [DecidableEq I] [DecidableEq A] in
@[simp] theorem fill_shared (i : I) : fillBlock i (shared : Finset (Sum C A)) = common := by
  ext x
  cases x with
  | inl c => simp [common]
  | inr p => rcases p with ⟨j,a⟩; simp [common]

def blocks (T : TransversalRows I A) (B : Finset (Finset (Sum C A))) :
    Finset (Finset (Sum C (I × A))) :=
  insert common (T.rows.image crossBlock ∪ univ.biUnion (fun i => B.image (fillBlock i)))
theorem mem_blocks (T : TransversalRows I A) (B : Finset (Finset (Sum C A)))
    (b : Finset (Sum C (I × A))) : b ∈ blocks T B ↔ b = common ∨
      (∃ r ∈ T.rows, crossBlock r = b) ∨ ∃ i c, c ∈ B ∧ fillBlock i c = b := by
  simp [blocks]
theorem uniform (T : TransversalRows I A) (B : Finset (Finset (Sum C A)))
    (hB : B.IsUniform (Fintype.card I)) (hcard : Fintype.card C = Fintype.card I) :
    (blocks T B).IsUniform (Fintype.card I) := by
  intro b hb
  rcases (mem_blocks T B b).mp hb with rfl | ⟨r,hr,rfl⟩ | ⟨i,c,hc,rfl⟩
  · simpa [common, shared] using hcard
  · rw [crossBlock, card_map]
    exact T.blocks_uniform _ (mem_image.mpr ⟨r,hr,rfl⟩)
  · rw [fillBlock, card_map]
    exact hB c hc

omit [DecidableEq I] in
theorem local_shared_unique (B : Finset (Finset (Sum C A)))
    (hB : B.IsBlockDesign 2 (Fintype.card I)) (hs : shared ∈ B)
    (c d : C) (hcd : c ≠ d) {b : Finset (Sum C A)}
    (hb : b ∈ B) (hc : Sum.inl c ∈ b) (hd : Sum.inl d ∈ b) : b = shared := by
  obtain ⟨e,he,hu⟩ := hB.2 {Sum.inl c,Sum.inl d} (by simp [hcd])
  exact (hu b ⟨hb,by simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hc hd⟩).trans
    (hu shared ⟨hs,by simp only [insert_subset_iff,singleton_subset_iff,mem_shared]; exact ⟨⟨c,rfl⟩,⟨d,rfl⟩⟩⟩).symm
theorem unique_shared (T : TransversalRows I A) (B : Finset (Finset (Sum C A)))
    (hB : B.IsBlockDesign 2 (Fintype.card I)) (hs : shared ∈ B)
    (c d : C) (hcd : c ≠ d) :
    ∃! b, b ∈ blocks T B ∧ Sum.inl c ∈ b ∧ Sum.inl d ∈ b := by
  refine ⟨common, ⟨(mem_blocks T B _).mpr (Or.inl rfl),by simp [common],by simp [common]⟩,?_⟩
  intro b hb
  rcases (mem_blocks T B b).mp hb.1 with he | ⟨r,hr,rfl⟩ | ⟨i,e,he,rfl⟩
  · exact he
  · exact False.elim (inl_cross c r hb.2.1)
  · have heq := local_shared_unique B hB hs c d hcd he
      ((inl_fill c i e).mp hb.2.1) ((inl_fill d i e).mp hb.2.2)
    rw [heq,fill_shared]
theorem unique_mixed (T : TransversalRows I A) (B : Finset (Finset (Sum C A)))
    (hB : B.IsBlockDesign 2 (Fintype.card I)) (c : C) (i : I) (a : A) :
    ∃! b, b ∈ blocks T B ∧ Sum.inl c ∈ b ∧ Sum.inr (i,a) ∈ b := by
  obtain ⟨e,he,hu⟩ := hB.2 {Sum.inl c,Sum.inr a} (by simp)
  have hc : Sum.inl c ∈ e := he.2 (by simp)
  have ha : Sum.inr a ∈ e := he.2 (by simp)
  refine ⟨fillBlock i e,⟨(mem_blocks T B _).mpr (Or.inr (Or.inr ⟨i,e,he.1,rfl⟩)),
    by simpa,by simp [ha]⟩,?_⟩
  intro b hb
  rcases (mem_blocks T B b).mp hb.1 with rfl | ⟨r,hr,rfl⟩ | ⟨j,f,hf,rfl⟩
  · simpa [common] using hb.2.2
  · exact False.elim (inl_cross c r hb.2.1)
  · obtain ⟨hij,ha'⟩ := (inr_fill i j a f).mp hb.2.2
    subst j
    have hfe := hu f ⟨hf,by simpa only [insert_subset_iff,singleton_subset_iff] using And.intro ((inl_fill c i f).mp hb.2.1) ha'⟩
    exact congrArg (fillBlock i) hfe
theorem unique_same (T : TransversalRows I A) (B : Finset (Finset (Sum C A)))
    (hB : B.IsBlockDesign 2 (Fintype.card I)) (i : I) (a b : A) (hab : a ≠ b) :
    ∃! e, e ∈ blocks T B ∧ Sum.inr (i,a) ∈ e ∧ Sum.inr (i,b) ∈ e := by
  obtain ⟨e,he,hu⟩ := hB.2 {Sum.inr a,Sum.inr b} (by simp [hab])
  have ha : Sum.inr a ∈ e := he.2 (by simp)
  have hb : Sum.inr b ∈ e := he.2 (by simp)
  refine ⟨fillBlock i e,⟨(mem_blocks T B _).mpr (Or.inr (Or.inr ⟨i,e,he.1,rfl⟩)),
    by simp [ha],by simp [hb]⟩,?_⟩
  intro d hd
  rcases (mem_blocks T B d).mp hd.1 with rfl | ⟨r,hr,rfl⟩ | ⟨j,f,hf,rfl⟩
  · simpa [common] using hd.2.1
  · exact False.elim (hab (((inr_cross i a r).mp hd.2.1).symm.trans ((inr_cross i b r).mp hd.2.2)))
  · obtain ⟨hij,ha'⟩ := (inr_fill i j a f).mp hd.2.1
    subst j
    have hfe := hu f ⟨hf,by simpa only [insert_subset_iff,singleton_subset_iff] using And.intro ha' ((inr_fill i i b f).mp hd.2.2).2⟩
    exact congrArg (fillBlock i) hfe
theorem unique_cross (T : TransversalRows I A) (B : Finset (Finset (Sum C A)))
    (i j : I) (hij : i ≠ j) (a b : A) :
    ∃! e, e ∈ blocks T B ∧ Sum.inr (i,a) ∈ e ∧ Sum.inr (j,b) ∈ e := by
  obtain ⟨r,hr,hu⟩ := T.pair_unique i j hij a b
  refine ⟨crossBlock r,⟨(mem_blocks T B _).mpr (Or.inr (Or.inl ⟨r,hr.1,rfl⟩)),
    by simpa using hr.2.1,by simpa using hr.2.2⟩,?_⟩
  intro e he
  rcases (mem_blocks T B e).mp he.1 with rfl | ⟨s,hs,rfl⟩ | ⟨l,f,hf,rfl⟩
  · simpa [common] using he.2.1
  · exact congrArg crossBlock (hu s ⟨hs,(inr_cross i a s).mp he.2.1,(inr_cross j b s).mp he.2.2⟩)
  · exact False.elim (hij (((inr_fill i l a f).mp he.2.1).1.trans ((inr_fill j l b f).mp he.2.2).1.symm))
theorem unique_pair (T : TransversalRows I A) (B : Finset (Finset (Sum C A)))
    (hB : B.IsBlockDesign 2 (Fintype.card I)) (hs : shared ∈ B)
    (p q : Sum C (I × A)) (hpq : p ≠ q) :
    ∃! b, b ∈ blocks T B ∧ p ∈ b ∧ q ∈ b := by
  cases p with
  | inl c =>
    cases q with
    | inl d => exact unique_shared T B hB hs c d (fun h => hpq (congrArg Sum.inl h))
    | inr q => exact unique_mixed T B hB c q.1 q.2
  | inr p =>
    cases q with
    | inl c =>
      obtain ⟨b,hb,hu⟩ := unique_mixed T B hB c p.1 p.2
      exact ⟨b,⟨hb.1,hb.2.2,hb.2.1⟩,fun d hd => hu d ⟨hd.1,hd.2.2,hd.2.1⟩⟩
    | inr q =>
      rcases p with ⟨i,a⟩
      rcases q with ⟨j,b⟩
      by_cases hij : i = j
      · subst j
        exact unique_same T B hB i a b (fun h => hpq (by subst b; rfl))
      · exact unique_cross T B i j hij a b

theorem isBlockDesign (T : TransversalRows I A) (B : Finset (Finset (Sum C A)))
    (hB : B.IsBlockDesign 2 (Fintype.card I)) (hs : shared ∈ B)
    (hcard : Fintype.card C = Fintype.card I) :
    (blocks T B).IsBlockDesign 2 (Fintype.card I) := by
  refine ⟨uniform T B hB.1 hcard,?_⟩
  intro S hS
  obtain ⟨p,q,hpq,rfl⟩ := card_eq_two.mp hS
  obtain ⟨b,hb,hu⟩ := unique_pair T B hB hs p q hpq
  refine ⟨b,⟨hb.1,?_⟩,?_⟩
  · simpa only [insert_subset_iff,singleton_subset_iff] using hb.2
  · intro d hd
    exact hu d ⟨hd.1,hd.2 (by simp),hd.2 (by simp)⟩

/-- Normalize any selected block; both block and complement coordinates are constructed. -/
theorem normalize_local {n k : ℕ} (D : Finset (Finset (Fin (n+k))))
    (hD : D.IsBlockDesign 2 k) (b : Finset (Fin (n+k))) (hb : b ∈ D) :
    ∃ B : Finset (Finset (Sum (Fin k) (Fin n))), B.IsBlockDesign 2 k ∧ shared ∈ B := by
  classical
  have hbk : b.card = k := hD.1 b hb
  have hbc : Fintype.card {v : Fin (n+k) // v ∉ b} = n := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin, Fintype.card_coe, hbk]
    omega
  let eb : ↥b ≃ Fin k := Finset.equivFinOfCardEq hbk
  let ec : {v : Fin (n+k) // v ∉ b} ≃ Fin n := Fintype.equivFinOfCardEq hbc
  let e : Fin (n+k) ≃ Sum (Fin k) (Fin n) :=
    (Equiv.sumCompl (fun v : Fin (n+k) => v ∈ b)).symm.trans (Equiv.sumCongr eb ec)
  have hmap : b.map e.toEmbedding = shared := by
    ext z
    cases z with
    | inl c =>
      have hh : e.symm (Sum.inl c) ∈ b := (eb.symm c).property
      simp only [mem_map_equiv,mem_shared,Sum.inl.injEq,exists_eq',hh]
    | inr a =>
      have hh : e.symm (Sum.inr a) ∉ b := (ec.symm a).property
      simp only [mem_map_equiv,mem_shared,Sum.inr_ne_inl,exists_false,hh]
  refine ⟨DesignTransport.relabel e D,DesignTransport.isBlockDesign_relabel e D 2 k hD,?_⟩
  exact mem_image.mpr ⟨b,hb,hmap⟩

/-- A nontrivial supplied design contains a block, so no distinguished-block oracle is needed. -/
theorem normalize_local_exists {n k : ℕ} (hk : 2 ≤ n+k)
    (D : Finset (Finset (Fin (n+k)))) (hD : D.IsBlockDesign 2 k) :
    ∃ B : Finset (Finset (Sum (Fin k) (Fin n))), B.IsBlockDesign 2 k ∧ shared ∈ B := by
  let x : Fin (n+k) := ⟨0,by omega⟩
  let y : Fin (n+k) := ⟨1,by omega⟩
  obtain ⟨b,hb,_⟩ := hD.2 {x,y} (by simp [x,y,Fin.ext_iff])
  exact normalize_local D hD b hb.1

/-- Actual finite design from rows and a design of order n+k; all inputs remain explicit. -/
theorem finite_exists {n k : ℕ} (hk : 2 ≤ n+k)
    (T : TransversalRows (Fin k) (Fin n))
    (D : Finset (Finset (Fin (n+k)))) (hD : D.IsBlockDesign 2 k) :
    ∃ H : Finset (Finset (Fin (k*n+k))), H.IsBlockDesign 2 k := by
  classical
  obtain ⟨B,hB,hs⟩ := normalize_local_exists hk D hD
  have hlocal : B.IsBlockDesign 2 (Fintype.card (Fin k)) := by simpa using hB
  have h := isBlockDesign T B hlocal hs (by simp : Fintype.card (Fin k) = Fintype.card (Fin k))
  let e : Sum (Fin k) (Fin k × Fin n) ≃ Fin (k*n+k) :=
    Fintype.equivFinOfCardEq (by simp; omega)
  exact ⟨DesignTransport.relabel e (blocks T B), DesignTransport.isBlockDesign_relabel e _ 2 k (by simpa using h)⟩

end Erdos643Design.Foundation.SharedBlockFill
