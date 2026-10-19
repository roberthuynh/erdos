import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
import Mathlib.Tactic

/-! Development of supplied finite difference families by all group translations. -/
set_option autoImplicit false

namespace Erdos643Design.DifferenceFamily
open Finset
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Ordered difference witnesses: a base block and two ordered points in it. -/
def witnesses (base : Finset (Finset G)) (d : G) : Finset (Finset G × G × G) :=
  (base ×ˢ (univ ×ˢ univ)).filter
    (fun w => w.2.1 ∈ w.1 ∧ w.2.2 ∈ w.1 ∧ w.2.1 - w.2.2 = d)

@[simp] theorem mem_witnesses (base : Finset (Finset G)) (d : G)
    (B : Finset G) (x y : G) :
    (B,x,y) ∈ witnesses base d ↔ B ∈ base ∧ x ∈ B ∧ y ∈ B ∧ x-y = d := by
  simp [witnesses]

/-- A supplied family has exactly one ordered witness for each nonzero difference. -/
structure Supplied (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (k : ℕ) where
  base : Finset (Finset G)
  uniform : base.IsUniform k
  unique_difference : ∀ d : G, d ≠ 0 → ∃! w, w ∈ witnesses base d

/-- Translate every point in one finite block. -/
def translate (g : G) (B : Finset G) : Finset G := B.image (g + ·)

omit [Fintype G] in
@[simp] theorem mem_translate (g p : G) (B : Finset G) :
    p ∈ translate g B ↔ ∃ x ∈ B, g+x = p := by
  simp only [translate, mem_image]

omit [Fintype G] in
theorem translate_card (g : G) (B : Finset G) : (translate g B).card = B.card := by
  apply card_image_iff.mpr
  intro x _ y _ h
  exact add_left_cancel h

namespace Supplied
variable {k : ℕ}

/-- The actual finite family of all translates of all supplied base blocks. -/
def developed (D : Supplied G k) : Finset (Finset G) :=
  (D.base ×ˢ univ).image (fun Bg => translate Bg.2 Bg.1)

theorem developed_uniform (D : Supplied G k) : D.developed.IsUniform k := by
  intro B hB
  obtain ⟨⟨C,g⟩, hCg, rfl⟩ := mem_image.mp hB
  rw [translate_card]
  exact D.uniform C (mem_product.mp hCg).1

/-- A prescribed ordered point pair determines a developed block uniquely. -/
theorem developed_unique_pair (D : Supplied G k) (p q : G) (hpq : p ≠ q) :
    ∃! B, B ∈ D.developed ∧ p ∈ B ∧ q ∈ B := by
  obtain ⟨⟨B,x,y⟩, hBxy, hu⟩ := D.unique_difference (p-q) (sub_ne_zero.mpr hpq)
  obtain ⟨hB,hx,hy,hd⟩ := (mem_witnesses _ _ _ _ _).mp hBxy
  have hx' : (p-x)+x = p := sub_add_cancel p x
  have hy' : (p-x)+y = q := by
    calc
      (p-x)+y = p-(x-y) := by abel
      _ = q := by rw [hd]; abel
  refine ⟨translate (p-x) B, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact mem_image.mpr ⟨(B,p-x), mem_product.mpr ⟨hB,mem_univ _⟩, rfl⟩
  · exact (mem_translate _ _ _).mpr ⟨x,hx,hx'⟩
  · exact (mem_translate _ _ _).mpr ⟨y,hy,hy'⟩
  · intro C hC
    obtain ⟨⟨A,g⟩, hAg, rfl⟩ := mem_image.mp hC.1
    obtain ⟨a,ha,hap⟩ := (mem_translate _ _ _).mp hC.2.1
    obtain ⟨b,hb,hbq⟩ := (mem_translate _ _ _).mp hC.2.2
    have hd' : a-b = p-q := by rw [← hap, ← hbq]; abel
    have hw : (A,a,b) = (B,x,y) := hu _ ((mem_witnesses _ _ _ _ _).mpr
      ⟨(mem_product.mp hAg).1,ha,hb,hd'⟩)
    have hAB : A = B := congrArg Prod.fst hw
    have hax : a = x := congrArg (fun w : Finset G × G × G => w.2.1) hw
    subst A
    subst a
    have hg : g = p-x := (eq_sub_iff_add_eq).mpr hap
    rw [hg]

/-- Developing a supplied difference family gives the actual upstream design. -/
theorem developed_isBlockDesign (D : Supplied G k) : D.developed.IsBlockDesign 2 k := by
  refine ⟨D.developed_uniform, ?_⟩
  intro S hS
  obtain ⟨p,q,hpq,rfl⟩ := card_eq_two.mp hS
  obtain ⟨B,hB,hu⟩ := D.developed_unique_pair p q hpq
  refine ⟨B, ⟨hB.1, ?_⟩, ?_⟩
  · simpa only [insert_subset_iff, singleton_subset_iff] using hB.2
  · intro C hC
    exact hu C ⟨hC.1, hC.2 (by simp), hC.2 (by simp)⟩

end Supplied
end Erdos643Design.DifferenceFamily
