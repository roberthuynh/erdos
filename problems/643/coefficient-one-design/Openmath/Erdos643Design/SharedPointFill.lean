import Openmath.Erdos643Design.TransversalFoundation

/-! Supplied transversal rows and supplied designs with one common point. -/
set_option autoImplicit false
namespace Erdos643Design.Foundation.SharedPoint
open Finset
variable {I A : Type*} [Fintype I] [DecidableEq I] [DecidableEq A]

def someEmbedding : (I × A) ↪ Option (I × A) := ⟨some, fun _ _ h => Option.some.inj h⟩
def groupEmbedding (i : I) : Option A ↪ Option (I × A) where
  toFun := fun a => a.map (fun x => (i,x))
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all

def crossBlock (r : I → A) := (TransversalRows.rowBlock r).map someEmbedding
def fillBlock (i : I) (b : Finset (Option A)) := b.map (groupEmbedding i)

@[simp] theorem none_cross (r : I → A) : none ∉ crossBlock r := by
  simp [crossBlock, someEmbedding]
@[simp] theorem some_cross (r : I → A) (i : I) (a : A) :
    some (i,a) ∈ crossBlock r ↔ r i = a := by
  simp only [crossBlock, mem_map]
  constructor
  · rintro ⟨p,hp,he⟩
    change some p = some (i,a) at he
    have hpi : p = (i,a) := Option.some.inj he
    subst p
    exact (TransversalRows.mem_rowBlock r i a).mp hp
  · intro h
    exact ⟨(i,a),(TransversalRows.mem_rowBlock r i a).mpr h,rfl⟩
omit [Fintype I] [DecidableEq I] [DecidableEq A] in
@[simp] theorem none_fill (i : I) (b : Finset (Option A)) :
    none ∈ fillBlock i b ↔ none ∈ b := by
  simp only [fillBlock, mem_map]
  constructor
  · rintro ⟨x,hx,he⟩
    change x.map (fun a => (i,a)) = none at he
    cases x with
    | none => exact hx
    | some a => simp at he
  · intro h
    exact ⟨none,h,rfl⟩
omit [Fintype I] [DecidableEq I] [DecidableEq A] in
@[simp] theorem some_fill (i j : I) (a : A) (b : Finset (Option A)) :
    some (i,a) ∈ fillBlock j b ↔ i = j ∧ some a ∈ b := by
  simp only [fillBlock, mem_map]
  constructor
  · rintro ⟨x,hx,he⟩
    change x.map (fun a => (j,a)) = some (i,a) at he
    cases x with
    | none => simp at he
    | some x =>
      simp only [Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at he
      obtain ⟨hji,hxa⟩ := he
      subst j
      subst x
      exact ⟨rfl,hx⟩
  · rintro ⟨rfl,ha⟩
    exact ⟨some a,ha,rfl⟩

def blocks (T : TransversalRows I A) (B : Finset (Finset (Option A))) :
    Finset (Finset (Option (I × A))) :=
  T.rows.image crossBlock ∪ univ.biUnion (fun i => B.image (fillBlock i))

theorem mem_blocks (T : TransversalRows I A) (B : Finset (Finset (Option A)))
    (b : Finset (Option (I × A))) :
    b ∈ blocks T B ↔ (∃ r ∈ T.rows, crossBlock r = b) ∨
      ∃ i c, c ∈ B ∧ fillBlock i c = b := by
  simp [blocks]

theorem uniform (T : TransversalRows I A) (B : Finset (Finset (Option A)))
    (hB : B.IsUniform (Fintype.card I)) : (blocks T B).IsUniform (Fintype.card I) := by
  intro b hb
  rcases (mem_blocks T B b).mp hb with ⟨r,hr,rfl⟩ | ⟨i,c,hc,rfl⟩
  · rw [crossBlock, card_map]
    exact T.blocks_uniform _ (mem_image.mpr ⟨r,hr,rfl⟩)
  · rw [fillBlock, card_map]
    exact hB c hc

theorem unique_none (T : TransversalRows I A) (B : Finset (Finset (Option A)))
    (hB : B.IsBlockDesign 2 (Fintype.card I)) (i : I) (a : A) :
    ∃! b, b ∈ blocks T B ∧ none ∈ b ∧ some (i,a) ∈ b := by
  obtain ⟨c,hc,hu⟩ := hB.2 {none,some a} (by simp)
  have hn : none ∈ c := hc.2 (by simp)
  have ha : some a ∈ c := hc.2 (by simp)
  refine ⟨fillBlock i c, ⟨(mem_blocks T B _).mpr (Or.inr ⟨i,c,hc.1,rfl⟩),
    (none_fill i c).mpr hn, (some_fill i i a c).mpr ⟨rfl,ha⟩⟩, ?_⟩
  intro b hb
  rcases (mem_blocks T B b).mp hb.1 with ⟨r,hr,rfl⟩ | ⟨j,d,hd,rfl⟩
  · exact False.elim (none_cross r hb.2.1)
  · obtain ⟨hij,ha'⟩ := (some_fill i j a d).mp hb.2.2
    subst j
    have hd' : d = c := hu d ⟨hd, by
      simpa only [insert_subset_iff, singleton_subset_iff] using
        And.intro ((none_fill i d).mp hb.2.1) ha'⟩
    exact congrArg (fillBlock i) hd'

theorem unique_same (T : TransversalRows I A) (B : Finset (Finset (Option A)))
    (hB : B.IsBlockDesign 2 (Fintype.card I)) (i : I) (a b : A) (hab : a ≠ b) :
    ∃! c, c ∈ blocks T B ∧ some (i,a) ∈ c ∧ some (i,b) ∈ c := by
  obtain ⟨c,hc,hu⟩ := hB.2 {some a,some b} (by simp [hab])
  have ha : some a ∈ c := hc.2 (by simp)
  have hb : some b ∈ c := hc.2 (by simp)
  refine ⟨fillBlock i c, ⟨(mem_blocks T B _).mpr (Or.inr ⟨i,c,hc.1,rfl⟩),
    (some_fill i i a c).mpr ⟨rfl,ha⟩, (some_fill i i b c).mpr ⟨rfl,hb⟩⟩, ?_⟩
  intro d hd
  rcases (mem_blocks T B d).mp hd.1 with ⟨r,hr,rfl⟩ | ⟨j,e,he,rfl⟩
  · exact False.elim (hab (((some_cross r i a).mp hd.2.1).symm.trans
      ((some_cross r i b).mp hd.2.2)))
  · obtain ⟨hij,ha'⟩ := (some_fill i j a e).mp hd.2.1
    subst j
    have he' : e = c := hu e ⟨he, by
      simpa only [insert_subset_iff, singleton_subset_iff] using
        And.intro ha' ((some_fill i i b e).mp hd.2.2).2⟩
    exact congrArg (fillBlock i) he'

theorem unique_cross (T : TransversalRows I A) (B : Finset (Finset (Option A)))
    (i j : I) (hij : i ≠ j) (a b : A) :
    ∃! c, c ∈ blocks T B ∧ some (i,a) ∈ c ∧ some (j,b) ∈ c := by
  obtain ⟨r,hr,hu⟩ := T.pair_unique i j hij a b
  refine ⟨crossBlock r, ⟨(mem_blocks T B _).mpr (Or.inl ⟨r,hr.1,rfl⟩),
    (some_cross r i a).mpr hr.2.1, (some_cross r j b).mpr hr.2.2⟩, ?_⟩
  intro c hc
  rcases (mem_blocks T B c).mp hc.1 with ⟨s,hs,rfl⟩ | ⟨l,d,hd,rfl⟩
  · exact congrArg crossBlock (hu s ⟨hs,(some_cross s i a).mp hc.2.1,
      (some_cross s j b).mp hc.2.2⟩)
  · exact False.elim (hij (((some_fill i l a d).mp hc.2.1).1.trans
      ((some_fill j l b d).mp hc.2.2).1.symm))

theorem unique_pair (T : TransversalRows I A) (B : Finset (Finset (Option A)))
    (hB : B.IsBlockDesign 2 (Fintype.card I))
    (p q : Option (I × A)) (hpq : p ≠ q) :
    ∃! b, b ∈ blocks T B ∧ p ∈ b ∧ q ∈ b := by
  cases p with
  | none =>
    cases q with
    | none => exact False.elim (hpq rfl)
    | some q => exact unique_none T B hB q.1 q.2
  | some p =>
    cases q with
    | none =>
      obtain ⟨b,hb,hu⟩ := unique_none T B hB p.1 p.2
      exact ⟨b,⟨hb.1,hb.2.2,hb.2.1⟩,fun c hc => hu c ⟨hc.1,hc.2.2,hc.2.1⟩⟩
    | some q =>
      rcases p with ⟨i,a⟩
      rcases q with ⟨j,b⟩
      by_cases hij : i = j
      · subst j
        exact unique_same T B hB i a b (fun h => hpq (by subst b; rfl))
      · exact unique_cross T B i j hij a b

/-- Supplied rows and a supplied design with one extra point give an actual upstream design.
No size or existence assumptions beyond the displayed certificates are needed. -/
theorem isBlockDesign (T : TransversalRows I A) (B : Finset (Finset (Option A)))
    (hB : B.IsBlockDesign 2 (Fintype.card I)) :
    (blocks T B).IsBlockDesign 2 (Fintype.card I) := by
  refine ⟨uniform T B hB.1, ?_⟩
  intro S hS
  obtain ⟨p,q,hpq,rfl⟩ := card_eq_two.mp hS
  obtain ⟨b,hb,hu⟩ := unique_pair T B hB p q hpq
  refine ⟨b,⟨hb.1,?_⟩,?_⟩
  · simpa only [insert_subset_iff, singleton_subset_iff] using hb.2
  · intro c hc
    exact hu c ⟨hc.1,hc.2 (by simp),hc.2 (by simp)⟩

end Erdos643Design.Foundation.SharedPoint
