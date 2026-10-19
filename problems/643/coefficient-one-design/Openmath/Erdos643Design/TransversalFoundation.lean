import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
import Mathlib.Tactic

/-! Original finite interfaces for transversal rows and filling groups.
No general design existence theorem, external implementation or finite table is assumed. -/
set_option autoImplicit false

namespace Erdos643Design.Foundation
open Finset

/-- Finite rows with uniquely prescribed entries in any two different columns. -/
structure TransversalRows (I A : Type*) [Fintype I] [DecidableEq I] [DecidableEq A] where
  rows : Finset (I → A)
  pair_unique : ∀ i j : I, i ≠ j → ∀ x y : A,
    ∃! r, r ∈ rows ∧ r i = x ∧ r j = y

namespace TransversalRows
variable {I A : Type*} [Fintype I] [DecidableEq I] [DecidableEq A]

def rowBlock (r : I → A) : Finset (I × A) := univ.image (fun i => (i, r i))

def blocks (T : TransversalRows I A) : Finset (Finset (I × A)) :=
  T.rows.image rowBlock

@[simp] theorem mem_rowBlock (r : I → A) (i : I) (x : A) :
    (i, x) ∈ rowBlock r ↔ r i = x := by
  simp [rowBlock]

theorem blocks_uniform (T : TransversalRows I A) : T.blocks.IsUniform (Fintype.card I) := by
  intro b hb
  obtain ⟨r, hr, rfl⟩ := mem_image.mp hb
  unfold rowBlock
  rw [card_image_iff.mpr, card_univ]
  intro i _ j _ he
  exact congrArg Prod.fst he

theorem blocks_transverse (T : TransversalRows I A) {b : Finset (I × A)}
    (hb : b ∈ T.blocks) {p q : I × A} (hp : p ∈ b) (hq : q ∈ b)
    (hgroup : p.1 = q.1) : p = q := by
  obtain ⟨r, hr, rfl⟩ := mem_image.mp hb
  rcases p with ⟨i,x⟩
  rcases q with ⟨j,y⟩
  simp only [mem_rowBlock] at hp hq
  simp only at hgroup
  subst j
  exact Prod.ext rfl (hp.symm.trans hq)

theorem blocks_unique_crosspair (T : TransversalRows I A) (p q : I × A)
    (hgroup : p.1 ≠ q.1) :
    ∃! b, b ∈ T.blocks ∧ p ∈ b ∧ q ∈ b := by
  rcases p with ⟨i,x⟩
  rcases q with ⟨j,y⟩
  obtain ⟨r, hr, hu⟩ := T.pair_unique i j hgroup x y
  refine ⟨rowBlock r, ⟨mem_image.mpr ⟨r, hr.1, rfl⟩, ?_, ?_⟩, ?_⟩
  · exact (mem_rowBlock r i x).mpr hr.2.1
  · exact (mem_rowBlock r j y).mpr hr.2.2
  · intro b hb
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hb.1
    have heq : s = r := hu s ⟨hs, (mem_rowBlock s i x).mp hb.2.1,
      (mem_rowBlock s j y).mp hb.2.2⟩
    exact congrArg rowBlock heq

end TransversalRows

/-- All inputs required to fill transverse blocks with designs inside the groups. -/
structure GroupedDesign (V I : Type*) [DecidableEq V] [Fintype I] [DecidableEq I]
    (k : ℕ) where
  group : V → I
  cross : Finset (Finset V)
  cross_uniform : cross.IsUniform k
  cross_transverse : ∀ b ∈ cross, ∀ x ∈ b, ∀ y ∈ b, group x = group y → x = y
  cross_unique : ∀ x y, group x ≠ group y → ∃! b, b ∈ cross ∧ x ∈ b ∧ y ∈ b
  fill : I → Finset (Finset V)
  fill_uniform : ∀ i, (fill i).IsUniform k
  fill_within : ∀ i b, b ∈ fill i → ∀ x ∈ b, group x = i
  fill_unique : ∀ i x y, x ≠ y → group x = i → group y = i →
    ∃! b, b ∈ fill i ∧ x ∈ b ∧ y ∈ b

namespace GroupedDesign
variable {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I] {k : ℕ}

def completed (D : GroupedDesign V I k) : Finset (Finset V) :=
  D.cross ∪ univ.biUnion D.fill

theorem completed_uniform (D : GroupedDesign V I k) : D.completed.IsUniform k := by
  intro b hb
  rcases mem_union.mp hb with hc | hf
  · exact D.cross_uniform b hc
  · obtain ⟨i, _, hi⟩ := mem_biUnion.mp hf
    exact D.fill_uniform i b hi

theorem completed_unique_pair (D : GroupedDesign V I k) (x y : V) (hxy : x ≠ y) :
    ∃! b, b ∈ D.completed ∧ x ∈ b ∧ y ∈ b := by
  by_cases hg : D.group x = D.group y
  · obtain ⟨b, hb, hu⟩ := D.fill_unique (D.group x) x y hxy rfl hg.symm
    refine ⟨b, ⟨mem_union_right _ (mem_biUnion.mpr ⟨D.group x, mem_univ _, hb.1⟩),
      hb.2⟩, ?_⟩
    intro c hc
    rcases mem_union.mp hc.1 with hcross | hfill
    · exact False.elim (hxy (D.cross_transverse c hcross x hc.2.1 y hc.2.2 hg))
    · obtain ⟨i, _, hi⟩ := mem_biUnion.mp hfill
      have heq := D.fill_within i c hi x hc.2.1
      subst i
      exact hu c ⟨hi, hc.2⟩
  · obtain ⟨b, hb, hu⟩ := D.cross_unique x y hg
    refine ⟨b, ⟨mem_union_left _ hb.1, hb.2⟩, ?_⟩
    intro c hc
    rcases mem_union.mp hc.1 with hcross | hfill
    · exact hu c ⟨hcross, hc.2⟩
    · obtain ⟨i, _, hi⟩ := mem_biUnion.mp hfill
      exact False.elim (hg ((D.fill_within i c hi x hc.2.1).trans
        (D.fill_within i c hi y hc.2.2).symm))

/-- The filled family satisfies the actual upstream block-design definition. -/
theorem completed_isBlockDesign (D : GroupedDesign V I k) :
    D.completed.IsBlockDesign 2 k := by
  refine ⟨D.completed_uniform, ?_⟩
  intro S hS
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hS
  obtain ⟨b, hb, hu⟩ := D.completed_unique_pair x y hxy
  refine ⟨b, ⟨hb.1, ?_⟩, ?_⟩
  · simpa only [insert_subset_iff, singleton_subset_iff] using hb.2
  · intro c hc
    apply hu c
    refine ⟨hc.1, ?_, ?_⟩
    · exact hc.2 (by simp)
    · exact hc.2 (by simp)

end GroupedDesign
/-- Within-group designs to combine with a transversal row family.
The target block size is the number of columns. -/
structure TransversalFill (I A : Type*) [Fintype I] [DecidableEq I] [DecidableEq A] where
  blocks : I → Finset (Finset (I × A))
  uniform : ∀ i, (blocks i).IsUniform (Fintype.card I)
  within : ∀ i b, b ∈ blocks i → ∀ p ∈ b, p.1 = i
  unique : ∀ i x y, x ≠ y → ∃! b, b ∈ blocks i ∧ (i,x) ∈ b ∧ (i,y) ∈ b

variable {I A : Type*} [Fintype I] [DecidableEq I] [DecidableEq A]

/-- This adapter carries explicit row and filling certificates into the generic group interface. -/
def fromTransversal (T : TransversalRows I A) (F : TransversalFill I A) :
    GroupedDesign (I × A) I (Fintype.card I) where
  group := Prod.fst
  cross := T.blocks
  cross_uniform := T.blocks_uniform
  cross_transverse := by
    intro b hb p hp q hq hg
    exact T.blocks_transverse hb hp hq hg
  cross_unique := T.blocks_unique_crosspair
  fill := F.blocks
  fill_uniform := F.uniform
  fill_within := F.within
  fill_unique := by
    intro i p q hpq hp hq
    rcases p with ⟨j,x⟩
    rcases q with ⟨l,y⟩
    simp only at hp hq
    subst j
    subst l
    apply F.unique i x y
    intro heq
    exact hpq (congrArg (Prod.mk i) heq)

/-- A supplied transversal and supplied fillings give a genuine upstream design. -/
theorem transversal_filled_design (T : TransversalRows I A) (F : TransversalFill I A) :
    (fromTransversal T F).completed.IsBlockDesign 2 (Fintype.card I) :=
  GroupedDesign.completed_isBlockDesign (fromTransversal T F)

def groupEmbedding (i : I) : A ↪ I × A where
  toFun := fun x => (i,x)
  inj' := fun _ _ h => congrArg Prod.snd h

/-- Lift actual upstream designs on the symbol type into each column's group. -/
def fillFromDesigns (Q : I → Finset (Finset A))
    (hQ : ∀ i, (Q i).IsBlockDesign 2 (Fintype.card I)) : TransversalFill I A where
  blocks := fun i => (Q i).image (fun b => b.map (groupEmbedding i))
  uniform := by
    intro i b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    rw [card_map]
    exact (hQ i).1 a ha
  within := by
    intro i b hb p hp
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hp
    rfl
  unique := by
    intro i x y hxy
    obtain ⟨a, ha, hu⟩ := (hQ i).2 {x,y} (by simp [hxy])
    have hx : x ∈ a := ha.2 (by simp)
    have hy : y ∈ a := ha.2 (by simp)
    refine ⟨a.map (groupEmbedding i), ⟨mem_image.mpr ⟨a, ha.1, rfl⟩, ?_, ?_⟩, ?_⟩
    · exact mem_map.mpr ⟨x,hx,rfl⟩
    · exact mem_map.mpr ⟨y,hy,rfl⟩
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := mem_image.mp hb.1
      have hxc : x ∈ c := by
        obtain ⟨z, hz, he⟩ := mem_map.mp hb.2.1
        have heq : z = x := congrArg Prod.snd he
        exact heq ▸ hz
      have hyc : y ∈ c := by
        obtain ⟨z, hz, he⟩ := mem_map.mp hb.2.2
        have heq : z = y := congrArg Prod.snd he
        exact heq ▸ hz
      have heq : c = a := hu c ⟨hc, by
        simpa only [insert_subset_iff, singleton_subset_iff] using And.intro hxc hyc⟩
      exact congrArg (fun d => d.map (groupEmbedding i)) heq

/-- Direct bridge from a supplied transversal and actual upstream within-group designs. -/
theorem transversal_and_block_designs (T : TransversalRows I A)
    (Q : I → Finset (Finset A)) (hQ : ∀ i, (Q i).IsBlockDesign 2 (Fintype.card I)) :
    (fromTransversal T (fillFromDesigns Q hQ)).completed.IsBlockDesign 2 (Fintype.card I) :=
  transversal_filled_design T (fillFromDesigns Q hQ)

end Erdos643Design.Foundation
