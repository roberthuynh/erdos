import Openmath.Erdos643Design.TransversalFoundation

/-! Finite-row closure under restriction of columns and products of alphabets.
These constructions require supplied transversal rows; they assert no general existence. -/
set_option autoImplicit false

namespace Erdos643Design.Foundation.TransversalRows
open Finset
variable {I J A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [DecidableEq A] [DecidableEq B]

/-- Restrict the actual finite row family along an embedding of columns. -/
def restrict (T : TransversalRows I A) (e : J ↪ I) : TransversalRows J A where
  rows := T.rows.image (fun r => r ∘ e)
  pair_unique := by
    intro i j hij x y
    obtain ⟨r, hr, hu⟩ := T.pair_unique (e i) (e j) (fun h => hij (e.injective h)) x y
    refine ⟨r ∘ e, ⟨mem_image.mpr ⟨r, hr.1, rfl⟩, hr.2⟩, ?_⟩
    intro s hs
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hs.1
    have he : t = r := hu t ⟨ht, hs.2⟩
    exact congrArg (fun u => u ∘ e) he

/-- Form the actual finite image of pairs of supplied rows, coordinate by coordinate. -/
def prod (T : TransversalRows I A) (U : TransversalRows I B) :
    TransversalRows I (A × B) where
  rows := (T.rows ×ˢ U.rows).image (fun rs i => (rs.1 i, rs.2 i))
  pair_unique := by
    intro i j hij x y
    obtain ⟨r, hr, hru⟩ := T.pair_unique i j hij x.1 y.1
    obtain ⟨s, hs, hsu⟩ := U.pair_unique i j hij x.2 y.2
    refine ⟨(fun l => (r l, s l)), ⟨?_, ?_, ?_⟩, ?_⟩
    · exact mem_image.mpr ⟨(r,s), mem_product.mpr ⟨hr.1, hs.1⟩, rfl⟩
    · exact Prod.ext hr.2.1 hs.2.1
    · exact Prod.ext hr.2.2 hs.2.2
    · intro t ht
      obtain ⟨⟨r',s'⟩, hrs, rfl⟩ := mem_image.mp ht.1
      obtain ⟨hr',hs'⟩ := mem_product.mp hrs
      have her : r' = r := hru r' ⟨hr', congrArg Prod.fst ht.2.1,
        congrArg Prod.fst ht.2.2⟩
      have hes : s' = s := hsu s' ⟨hs', congrArg Prod.snd ht.2.1,
        congrArg Prod.snd ht.2.2⟩
      subst r'
      subst s'
      rfl

end Erdos643Design.Foundation.TransversalRows
