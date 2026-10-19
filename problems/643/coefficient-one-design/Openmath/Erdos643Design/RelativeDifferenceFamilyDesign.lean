import Openmath.Erdos643Design.DifferenceFamilyCertificate
import Openmath.Erdos643Design.TransversalFoundation
import Openmath.Erdos643Design.DesignTransport

/-! Relative difference families with vertical groups of size five.
The supplied hypotheses count actual ordered differences of actual base-block points.
Developing by all translations and inserting each vertical group gives an actual design. -/
set_option autoImplicit false

namespace Erdos643Design.RelativeDifferenceFamily
open Finset
variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- Relative difference data with the forbidden subgroup `ZMod 5 × {0}`. -/
structure Supplied (A : Type*) [AddCommGroup A] [Fintype A] [DecidableEq A] where
  base : Finset (Finset (ZMod 5 × A))
  uniform : base.IsUniform 5
  transverse : ∀ B ∈ base, ∀ x ∈ B, ∀ y ∈ B, x.2 = y.2 → x = y
  unique_difference : ∀ d : ZMod 5 × A, d.2 ≠ 0 →
    ∃! w, w ∈ DifferenceFamily.witnesses base d

/-- Small, exact difference counts suffice; no pair-coverage property is assumed. -/
def Supplied.of_small_counts (base : Finset (Finset (ZMod 5 × A)))
    (uniform : base.IsUniform 5)
    (transverse : ∀ B ∈ base, ∀ x ∈ B, ∀ y ∈ B, x.2 = y.2 → x = y)
    (counts : ∀ d : ZMod 5 × A, d.2 ≠ 0 →
      (DifferenceFamily.smallWitnesses base d).card = 1) : Supplied A where
  base := base
  uniform := uniform
  transverse := transverse
  unique_difference := by
    intro d hd
    have hc : (DifferenceFamily.witnesses base d).card = 1 := by
      rw [← DifferenceFamily.smallWitnesses_eq]
      exact counts d hd
    obtain ⟨w,hw⟩ := card_eq_one.mp hc
    refine ⟨w, ?_, ?_⟩
    · rw [hw]
      exact mem_singleton_self w
    · intro z hz
      rw [hw] at hz
      exact mem_singleton.mp hz

/-- All actual unequal ordered-point witnesses, enumerated once before certification. -/
def properWitnesses (base : Finset (Finset (ZMod 5 × A))) :
    Finset (Finset (ZMod 5 × A) × (ZMod 5 × A) × (ZMod 5 × A)) :=
  (base.biUnion (fun B => (B ×ˢ B).image (fun xy => (B,xy)))).filter
    (fun w => w.2.1 ≠ w.2.2)

omit [AddCommGroup A] [Fintype A] in
@[simp] theorem mem_properWitnesses (base : Finset (Finset (ZMod 5 × A)))
    (B : Finset (ZMod 5 × A)) (x y : ZMod 5 × A) :
    (B,x,y) ∈ properWitnesses base ↔ B ∈ base ∧ x ∈ B ∧ y ∈ B ∧ x ≠ y := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  simp [properWitnesses, and_assoc]

/-- The ordered difference attached to a witness. -/
def difference (w : Finset (ZMod 5 × A) × (ZMod 5 × A) × (ZMod 5 × A)) :
    ZMod 5 × A := w.2.1 - w.2.2

/-- One global injectivity and image certificate can replace per-difference counts. -/
def Supplied.of_difference_image (base : Finset (Finset (ZMod 5 × A)))
    (uniform : base.IsUniform 5)
    (transverse : ∀ B ∈ base, ∀ x ∈ B, ∀ y ∈ B, x.2 = y.2 → x = y)
    (injective : Set.InjOn (difference (A := A)) (↑(properWitnesses base) : Set _))
    (image_eq : (properWitnesses base).image difference =
      univ.filter (fun d : ZMod 5 × A => d.2 ≠ 0)) : Supplied A where
  base := base
  uniform := uniform
  transverse := transverse
  unique_difference := by
    intro d hd
    have hd' : d ∈ (properWitnesses base).image difference := by
      rw [image_eq]
      exact mem_filter.mpr ⟨mem_univ _,hd⟩
    obtain ⟨⟨B,x,y⟩,hw,hwd⟩ := mem_image.mp hd'
    obtain ⟨hB,hx,hy,_⟩ := (mem_properWitnesses _ _ _ _).mp hw
    refine ⟨(B,x,y), (DifferenceFamily.mem_witnesses _ _ _ _ _).mpr
      ⟨hB,hx,hy,hwd⟩, ?_⟩
    intro w hw'
    rcases w with ⟨C,a,b⟩
    obtain ⟨hC,ha,hb,hvd⟩ := (DifferenceFamily.mem_witnesses _ _ _ _ _).mp hw'
    have hab : a ≠ b := by
      intro heq
      have hz : d = 0 := hvd.symm.trans (sub_eq_zero.mpr heq)
      exact hd (congrArg Prod.snd hz)
    exact injective ((mem_properWitnesses _ _ _ _).mpr ⟨hC,ha,hb,hab⟩) hw
      (hvd.trans hwd.symm)

/-- The number of differences outside the vertical forbidden subgroup. -/
theorem allowed_difference_card :
    (univ.filter (fun d : ZMod 5 × A => d.2 ≠ 0)).card =
      5 * (Fintype.card A - 1) := by
  have heq : univ.filter (fun d : ZMod 5 × A => d.2 ≠ 0) =
      (univ : Finset (ZMod 5)) ×ˢ ((univ : Finset A).erase 0) := by
    ext p
    simp
  rw [heq,card_product]
  simp

def Supplied.of_difference_card (base : Finset (Finset (ZMod 5 × A)))
    (uniform : base.IsUniform 5)
    (transverse : ∀ B ∈ base, ∀ x ∈ B, ∀ y ∈ B, x.2 = y.2 → x = y)
    (injective : Set.InjOn (difference (A := A)) (↑(properWitnesses base) : Set _))
    (count : (properWitnesses base).card = 5 * (Fintype.card A - 1)) : Supplied A := by
  apply Supplied.of_difference_image base uniform transverse injective
  have hsubset : (properWitnesses base).image difference ⊆
      univ.filter (fun d : ZMod 5 × A => d.2 ≠ 0) := by
    intro d hd
    obtain ⟨⟨B,x,y⟩,hw,rfl⟩ := mem_image.mp hd
    obtain ⟨hB,hx,hy,hxy⟩ := (mem_properWitnesses _ _ _ _).mp hw
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    intro hz
    exact hxy (transverse B hB x hx y hy (sub_eq_zero.mp hz))
  apply eq_of_subset_of_card_le hsubset
  have hc : ((properWitnesses base).image difference).card = (properWitnesses base).card :=
    card_image_iff.mpr injective
  rw [hc, count, allowed_difference_card]

/-- The five points having prescribed second coordinate. -/
def vertical (a : A) : Finset (ZMod 5 × A) := univ.image (fun z => (z,a))

omit [AddCommGroup A] [Fintype A] in
@[simp] theorem mem_vertical (a : A) (p : ZMod 5 × A) : p ∈ vertical a ↔ p.2 = a := by
  rcases p with ⟨z,b⟩
  simp [vertical, eq_comm]

omit [AddCommGroup A] [Fintype A] in
theorem vertical_card (a : A) : (vertical a).card = 5 := by
  calc
    (vertical a).card = (univ : Finset (ZMod 5)).card := by
      apply card_image_iff.mpr
      intro x _ y _ h
      exact congrArg Prod.fst h
    _ = 5 := by simp

namespace Supplied

/-- The cross-group blocks are all translates of all base blocks. -/
def developed (D : Supplied A) : Finset (Finset (ZMod 5 × A)) :=
  (D.base ×ˢ univ).image (fun Bg => DifferenceFamily.translate Bg.2 Bg.1)

theorem developed_uniform (D : Supplied A) : D.developed.IsUniform 5 := by
  intro B hB
  obtain ⟨⟨C,g⟩,hCg,rfl⟩ := mem_image.mp hB
  rw [DifferenceFamily.translate_card]
  exact D.uniform C (mem_product.mp hCg).1

theorem developed_transverse (D : Supplied A) (B : Finset (ZMod 5 × A))
    (hB : B ∈ D.developed) (p : ZMod 5 × A) (hp : p ∈ B)
    (q : ZMod 5 × A) (hq : q ∈ B) (hpq : p.2 = q.2) : p = q := by
  obtain ⟨⟨C,g⟩,hCg,rfl⟩ := mem_image.mp hB
  obtain ⟨x,hx,rfl⟩ := (DifferenceFamily.mem_translate _ _ _).mp hp
  obtain ⟨y,hy,rfl⟩ := (DifferenceFamily.mem_translate _ _ _).mp hq
  have hxy : x.2 = y.2 := add_left_cancel hpq
  rw [D.transverse C (mem_product.mp hCg).1 x hx y hy hxy]

/-- Each pair in distinct vertical groups has exactly one developed block. -/
theorem developed_unique_pair (D : Supplied A) (p q : ZMod 5 × A)
    (hpq : p.2 ≠ q.2) :
    ∃! B, B ∈ D.developed ∧ p ∈ B ∧ q ∈ B := by
  have hd0 : (p-q).2 ≠ 0 := sub_ne_zero.mpr hpq
  obtain ⟨⟨B,x,y⟩,hBxy,hu⟩ := D.unique_difference (p-q) hd0
  obtain ⟨hB,hx,hy,hd⟩ := (DifferenceFamily.mem_witnesses _ _ _ _ _).mp hBxy
  have hx' : (p-x)+x = p := sub_add_cancel p x
  have hy' : (p-x)+y = q := by
    calc
      (p-x)+y = p-(x-y) := by abel
      _ = q := by rw [hd]; abel
  refine ⟨DifferenceFamily.translate (p-x) B, ⟨?_,?_,?_⟩,?_⟩
  · exact mem_image.mpr ⟨(B,p-x),mem_product.mpr ⟨hB,mem_univ _⟩,rfl⟩
  · exact (DifferenceFamily.mem_translate _ _ _).mpr ⟨x,hx,hx'⟩
  · exact (DifferenceFamily.mem_translate _ _ _).mpr ⟨y,hy,hy'⟩
  · intro C hC
    obtain ⟨⟨B',g⟩,hBg,rfl⟩ := mem_image.mp hC.1
    obtain ⟨a,ha,hap⟩ := (DifferenceFamily.mem_translate _ _ _).mp hC.2.1
    obtain ⟨b,hb,hbq⟩ := (DifferenceFamily.mem_translate _ _ _).mp hC.2.2
    have hd' : a-b = p-q := by rw [← hap,← hbq]; abel
    have hw : (B',a,b) = (B,x,y) := hu _
      ((DifferenceFamily.mem_witnesses _ _ _ _ _).mpr
        ⟨(mem_product.mp hBg).1,ha,hb,hd'⟩)
    have hBB : B' = B := congrArg Prod.fst hw
    have hax : a = x := congrArg (fun w : Finset (ZMod 5 × A) ×
      (ZMod 5 × A) × (ZMod 5 × A) => w.2.1) hw
    subst B'
    subst a
    have hg : g = p-x := (eq_sub_iff_add_eq).mpr hap
    rw [hg]

/-- Cross blocks and the vertical five-point groups satisfy every completion input. -/
def grouped (D : Supplied A) : Foundation.GroupedDesign (ZMod 5 × A) A 5 where
  group := Prod.snd
  cross := D.developed
  cross_uniform := D.developed_uniform
  cross_transverse := D.developed_transverse
  cross_unique := D.developed_unique_pair
  fill := fun a => {vertical a}
  fill_uniform := by
    intro a B hB
    have h := mem_singleton.mp hB
    subst B
    exact vertical_card a
  fill_within := by
    intro a B hB p hp
    have h := mem_singleton.mp hB
    subst B
    exact (mem_vertical a p).mp hp
  fill_unique := by
    intro a p q _ hp hq
    refine ⟨vertical a, ⟨mem_singleton_self _,?_,?_⟩,?_⟩
    · exact (mem_vertical a p).mpr hp
    · exact (mem_vertical a q).mpr hq
    · intro B hB
      exact mem_singleton.mp hB.1

/-- The explicit union of developed blocks and vertical groups. -/
def completed (D : Supplied A) : Finset (Finset (ZMod 5 × A)) := D.grouped.completed

/-- The completed family satisfies the actual upstream block-design definition. -/
theorem completed_isBlockDesign (D : Supplied A) : D.completed.IsBlockDesign 2 5 :=
  Foundation.GroupedDesign.completed_isBlockDesign D.grouped

/-- Supplied relative difference data gives an actual design on the indicated finite order. -/
theorem exists_design_fin (D : Supplied A) :
    ∃ B : Finset (Finset (Fin (5 * Fintype.card A))), B.IsBlockDesign 2 5 := by
  let e : (ZMod 5 × A) ≃ Fin (5 * Fintype.card A) :=
    (Fintype.equivFin _).trans (finCongr (by simp))
  exact ⟨DesignTransport.relabel e D.completed,
    DesignTransport.isBlockDesign_relabel e D.completed 2 5 D.completed_isBlockDesign⟩

end Supplied
end Erdos643Design.RelativeDifferenceFamily
