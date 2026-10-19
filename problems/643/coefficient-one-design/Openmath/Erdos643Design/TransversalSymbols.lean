import Openmath.Erdos643Design.TransversalFoundation

/-! Relabel the symbols of actual transversal rows. -/
set_option autoImplicit false

namespace Erdos643Design.Foundation.TransversalRows
variable {I A B : Type*} [Fintype I] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]

/-- Apply a symbol equivalence to each entry of each actual row. -/
def symbolEquiv (T : TransversalRows I A) (e : A ≃ B) : TransversalRows I B where
  rows := T.rows.image (fun r => e ∘ r)
  pair_unique := by
    intro i j hij x y
    obtain ⟨r, hr, hu⟩ := T.pair_unique i j hij (e.symm x) (e.symm y)
    refine ⟨e ∘ r, ⟨Finset.mem_image.mpr ⟨r,hr.1,rfl⟩, ?_, ?_⟩, ?_⟩
    · change e (r i) = x
      rw [hr.2.1, e.apply_symm_apply]
    · change e (r j) = y
      rw [hr.2.2, e.apply_symm_apply]
    · intro s hs
      obtain ⟨u, hurows, rfl⟩ := Finset.mem_image.mp hs.1
      have hui : u i = e.symm x := by
        exact e.injective (by simpa only [Function.comp_apply, e.apply_symm_apply] using hs.2.1)
      have huj : u j = e.symm y := by
        exact e.injective (by simpa only [Function.comp_apply, e.apply_symm_apply] using hs.2.2)
      exact congrArg (fun a => e ∘ a) (hu u ⟨hurows,hui,huj⟩)

/-- The one-symbol alphabet has the singleton constant row family. -/
def one : TransversalRows I (Fin 1) where
  rows := {fun _ => 0}
  pair_unique := by
    intro i j _ x y
    refine ⟨(fun _ => 0), ⟨by simp, Subsingleton.elim _ _, Subsingleton.elim _ _⟩, ?_⟩
    intro r hr
    exact Finset.mem_singleton.mp hr.1

end Erdos643Design.Foundation.TransversalRows
