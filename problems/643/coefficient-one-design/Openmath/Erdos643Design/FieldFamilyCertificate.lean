import Openmath.Erdos643Design.RelativeDifferenceFamilyDesign

/-! Small cardinal certificates for explicit additive-coordinate witnesses. -/
set_option autoImplicit false

namespace Erdos643Design.FieldFamilyCertificate
open Finset RelativeDifferenceFamily

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

omit [AddCommGroup A] [Fintype A] in
/-- A cardinality-preserving second projection gives block transversality. -/
theorem transverse_of_projection_card (base : Finset (Finset (ZMod 5 × A)))
    (h : ∀ B ∈ base, (B.image Prod.snd).card = B.card) :
    ∀ B ∈ base, ∀ x ∈ B, ∀ y ∈ B, x.2 = y.2 → x = y := by
  intro B hB x hx y hy hxy
  exact (card_image_iff.mp (h B hB)) hx hy hxy

/-- Form finite base blocks from explicit finite point lists. -/
def baseFromLists (blocks : List (List (ZMod 5 × A))) : Finset (Finset (ZMod 5 × A)) :=
  (blocks.map List.toFinset).toFinset

/-- Enumerate the actual unequal ordered witnesses using their supplied lists. -/
def witnessList (blocks : List (List (ZMod 5 × A))) :
    List (Finset (ZMod 5 × A) × (ZMod 5 × A) × (ZMod 5 × A)) :=
  blocks.flatMap (fun B => ((B.product B).filter (fun xy => xy.1 ≠ xy.2)).map
    (fun xy => (B.toFinset,xy)))

omit [AddCommGroup A] [Fintype A] in
@[simp] theorem mem_witnessList (blocks : List (List (ZMod 5 × A)))
    (B : Finset (ZMod 5 × A)) (x y : ZMod 5 × A) :
    (B,x,y) ∈ witnessList blocks ↔ B ∈ baseFromLists blocks ∧ x ∈ B ∧ y ∈ B ∧ x ≠ y := by
  simp only [witnessList, List.mem_flatMap, List.mem_map, List.mem_filter,
    baseFromLists, List.mem_toFinset]
  constructor
  · rintro ⟨C,hC,⟨a,b⟩,⟨hab',hab⟩,heq⟩
    obtain ⟨ha,hb⟩ := List.mem_product.mp hab'
    have hab : a ≠ b := of_decide_eq_true hab
    have hB : C.toFinset = B := congrArg Prod.fst heq
    have hax : a = x := congrArg (fun w : Finset (ZMod 5 × A) ×
      (ZMod 5 × A) × (ZMod 5 × A) => w.2.1) heq
    have hby : b = y := congrArg (fun w : Finset (ZMod 5 × A) ×
      (ZMod 5 × A) × (ZMod 5 × A) => w.2.2) heq
    subst B; subst x; subst y
    exact ⟨⟨C,hC,rfl⟩, List.mem_toFinset.mpr ha, List.mem_toFinset.mpr hb, hab⟩
  · rintro ⟨⟨C,hC,rfl⟩,hx,hy,hxy⟩
    exact ⟨C,hC,(x,y),⟨List.mem_product.mpr ⟨List.mem_toFinset.mp hx,List.mem_toFinset.mp hy⟩,
      decide_eq_true hxy⟩,rfl⟩

omit [AddCommGroup A] [Fintype A] in
theorem properWitnesses_eq_toFinset (blocks : List (List (ZMod 5 × A))) :
    properWitnesses (baseFromLists blocks) = (witnessList blocks).toFinset := by
  ext ⟨B,x,y⟩
  simp only [mem_properWitnesses, List.mem_toFinset, mem_witnessList]

/-- Kernel-checked list equality, no-repeat and length data suffice for the relative design.
The claimed differences are only a computation aid: equality to the actual ordered
differences is a separate proof input. -/
def suppliedOfLists (blocks : List (List (ZMod 5 × A)))
    (uniform : (baseFromLists blocks).IsUniform 5)
    (transverse : ∀ B ∈ baseFromLists blocks, ∀ x ∈ B, ∀ y ∈ B, x.2 = y.2 → x = y)
    (claimed : List (ZMod 5 × A))
    (difference_eq : (witnessList blocks).map difference = claimed)
    (no_repeats : claimed.Nodup)
    (count : (witnessList blocks).length = 5 * (Fintype.card A - 1)) : Supplied A := by
  have hn : ((witnessList blocks).map difference).Nodup := difference_eq.symm ▸ no_repeats
  apply Supplied.of_difference_card (baseFromLists blocks) uniform transverse
  · intro x hx y hy hxy
    change x ∈ properWitnesses (baseFromLists blocks) at hx
    change y ∈ properWitnesses (baseFromLists blocks) at hy
    rw [properWitnesses_eq_toFinset] at hx hy
    exact List.inj_on_of_nodup_map hn (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hxy
  · rw [properWitnesses_eq_toFinset, List.toFinset_card_of_nodup (hn.of_map difference)]
    exact count

end Erdos643Design.FieldFamilyCertificate
