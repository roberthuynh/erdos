import Openmath.Erdos643Design.SharedPointFill

/-! Completion of supplied cross-group blocks by supplied designs sharing one point. -/
set_option autoImplicit false
namespace Erdos643Design.Foundation.SharedGroupCompletion
open Finset
variable {G A : Type*} [Fintype G] [DecidableEq G] [DecidableEq A] {k : ℕ}

/-- All finite cross-group input data required by the completion. -/
structure CrossDesign (G A : Type*) [DecidableEq G] [DecidableEq A] (k : ℕ) where
  cross : Finset (Finset (G × A))
  uniform : cross.IsUniform k
  transverse : ∀ b ∈ cross, ∀ p ∈ b, ∀ q ∈ b, p.1 = q.1 → p = q
  unique : ∀ p q : G × A, p.1 ≠ q.1 → ∃! b, b ∈ cross ∧ p ∈ b ∧ q ∈ b

def crossBlock (b : Finset (G × A)) : Finset (Option (G × A)) :=
  b.map SharedPoint.someEmbedding

omit [Fintype G] [DecidableEq G] [DecidableEq A] in
@[simp] theorem none_cross (b : Finset (G × A)) : none ∉ crossBlock b := by
  simp [crossBlock, SharedPoint.someEmbedding]

omit [Fintype G] [DecidableEq G] [DecidableEq A] in
@[simp] theorem some_cross (b : Finset (G × A)) (p : G × A) :
    some p ∈ crossBlock b ↔ p ∈ b := by
  simp only [crossBlock, mem_map]
  constructor
  · rintro ⟨q,hq,he⟩
    change some q = some p at he
    exact Option.some.inj he ▸ hq
  · intro hp
    exact ⟨p,hp,rfl⟩

def blocks (X : CrossDesign G A k) (B : Finset (Finset (Option A))) :
    Finset (Finset (Option (G × A))) :=
  X.cross.image crossBlock ∪ univ.biUnion (fun i => B.image (SharedPoint.fillBlock i))

theorem mem_blocks (X : CrossDesign G A k) (B : Finset (Finset (Option A)))
    (b : Finset (Option (G × A))) :
    b ∈ blocks X B ↔ (∃ c ∈ X.cross, crossBlock c = b) ∨
      ∃ i c, c ∈ B ∧ SharedPoint.fillBlock i c = b := by
  simp [blocks]

theorem uniform (X : CrossDesign G A k) (B : Finset (Finset (Option A)))
    (hB : B.IsUniform k) : (blocks X B).IsUniform k := by
  intro b hb
  rcases (mem_blocks X B b).mp hb with ⟨c,hc,rfl⟩ | ⟨i,c,hc,rfl⟩
  · rw [crossBlock, card_map]
    exact X.uniform c hc
  · rw [SharedPoint.fillBlock, card_map]
    exact hB c hc

theorem unique_none (X : CrossDesign G A k) (B : Finset (Finset (Option A)))
    (hB : B.IsBlockDesign 2 k) (i : G) (a : A) :
    ∃! b, b ∈ blocks X B ∧ none ∈ b ∧ some (i,a) ∈ b := by
  obtain ⟨c,hc,hu⟩ := hB.2 {none,some a} (by simp)
  have hn : none ∈ c := hc.2 (by simp)
  have ha : some a ∈ c := hc.2 (by simp)
  refine ⟨SharedPoint.fillBlock i c,
    ⟨(mem_blocks X B _).mpr (Or.inr ⟨i,c,hc.1,rfl⟩),
    (SharedPoint.none_fill i c).mpr hn, (SharedPoint.some_fill i i a c).mpr ⟨rfl,ha⟩⟩, ?_⟩
  intro b hb
  rcases (mem_blocks X B b).mp hb.1 with ⟨d,hd,rfl⟩ | ⟨j,d,hd,rfl⟩
  · exact False.elim (none_cross d hb.2.1)
  · obtain ⟨hij,ha'⟩ := (SharedPoint.some_fill i j a d).mp hb.2.2
    subst j
    have hd' : d = c := hu d ⟨hd, by
      simpa only [insert_subset_iff, singleton_subset_iff] using
        And.intro ((SharedPoint.none_fill i d).mp hb.2.1) ha'⟩
    exact congrArg (SharedPoint.fillBlock i) hd'

theorem unique_same (X : CrossDesign G A k) (B : Finset (Finset (Option A)))
    (hB : B.IsBlockDesign 2 k) (i : G) (a b : A) (hab : a ≠ b) :
    ∃! c, c ∈ blocks X B ∧ some (i,a) ∈ c ∧ some (i,b) ∈ c := by
  obtain ⟨c,hc,hu⟩ := hB.2 {some a,some b} (by simp [hab])
  have ha : some a ∈ c := hc.2 (by simp)
  have hb : some b ∈ c := hc.2 (by simp)
  refine ⟨SharedPoint.fillBlock i c,
    ⟨(mem_blocks X B _).mpr (Or.inr ⟨i,c,hc.1,rfl⟩),
    (SharedPoint.some_fill i i a c).mpr ⟨rfl,ha⟩,
    (SharedPoint.some_fill i i b c).mpr ⟨rfl,hb⟩⟩, ?_⟩
  intro d hd
  rcases (mem_blocks X B d).mp hd.1 with ⟨e,he,rfl⟩ | ⟨j,e,he,rfl⟩
  · exact False.elim (hab (congrArg Prod.snd
      (X.transverse e he (i,a) ((some_cross e (i,a)).mp hd.2.1)
        (i,b) ((some_cross e (i,b)).mp hd.2.2) rfl)))
  · obtain ⟨hij,ha'⟩ := (SharedPoint.some_fill i j a e).mp hd.2.1
    subst j
    have he' : e = c := hu e ⟨he, by
      simpa only [insert_subset_iff, singleton_subset_iff] using
        And.intro ha' ((SharedPoint.some_fill i i b e).mp hd.2.2).2⟩
    exact congrArg (SharedPoint.fillBlock i) he'

theorem unique_cross (X : CrossDesign G A k) (B : Finset (Finset (Option A)))
    (i j : G) (hij : i ≠ j) (a b : A) :
    ∃! c, c ∈ blocks X B ∧ some (i,a) ∈ c ∧ some (j,b) ∈ c := by
  obtain ⟨c,hc,hu⟩ := X.unique (i,a) (j,b) hij
  refine ⟨crossBlock c, ⟨(mem_blocks X B _).mpr (Or.inl ⟨c,hc.1,rfl⟩),
    (some_cross c (i,a)).mpr hc.2.1, (some_cross c (j,b)).mpr hc.2.2⟩, ?_⟩
  intro d hd
  rcases (mem_blocks X B d).mp hd.1 with ⟨e,he,rfl⟩ | ⟨l,e,he,rfl⟩
  · exact congrArg crossBlock (hu e ⟨he,(some_cross e (i,a)).mp hd.2.1,
      (some_cross e (j,b)).mp hd.2.2⟩)
  · exact False.elim (hij (((SharedPoint.some_fill i l a e).mp hd.2.1).1.trans
      ((SharedPoint.some_fill j l b e).mp hd.2.2).1.symm))

theorem unique_pair (X : CrossDesign G A k) (B : Finset (Finset (Option A)))
    (hB : B.IsBlockDesign 2 k) (p q : Option (G × A)) (hpq : p ≠ q) :
    ∃! b, b ∈ blocks X B ∧ p ∈ b ∧ q ∈ b := by
  cases p with
  | none =>
    cases q with
    | none => exact False.elim (hpq rfl)
    | some q => exact unique_none X B hB q.1 q.2
  | some p =>
    cases q with
    | none =>
      obtain ⟨b,hb,hu⟩ := unique_none X B hB p.1 p.2
      exact ⟨b,⟨hb.1,hb.2.2,hb.2.1⟩,fun c hc => hu c ⟨hc.1,hc.2.2,hc.2.1⟩⟩
    | some q =>
      rcases p with ⟨i,a⟩
      rcases q with ⟨j,b⟩
      by_cases hij : i = j
      · subst j
        exact unique_same X B hB i a b (fun h => hpq (by subst b; rfl))
      · exact unique_cross X B i j hij a b

/-- Supplied cross-group blocks and supplied shared-point fillings give an actual design. -/
theorem isBlockDesign (X : CrossDesign G A k) (B : Finset (Finset (Option A)))
    (hB : B.IsBlockDesign 2 k) : (blocks X B).IsBlockDesign 2 k := by
  refine ⟨uniform X B hB.1, ?_⟩
  intro S hS
  obtain ⟨p,q,hpq,rfl⟩ := card_eq_two.mp hS
  obtain ⟨b,hb,hu⟩ := unique_pair X B hB p q hpq
  refine ⟨b,⟨hb.1,?_⟩,?_⟩
  · simpa only [insert_subset_iff, singleton_subset_iff] using hb.2
  · intro c hc
    exact hu c ⟨hc.1,hc.2 (by simp),hc.2 (by simp)⟩

end Erdos643Design.Foundation.SharedGroupCompletion
