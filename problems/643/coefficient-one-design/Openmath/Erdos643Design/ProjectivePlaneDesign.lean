import Openmath.Erdos643Design.SharedPointFill
import Openmath.Erdos643Design.TransversalField

/-! A finite-field projective-plane design obtained by shared-point filling. -/
set_option autoImplicit false
namespace Erdos643Design.Foundation.ProjectivePlane
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A single complete block supplies each group together with the common point. -/
def groupDesign : Finset (Finset (Option F)) := {univ}

omit [Field F] [DecidableEq F] in
theorem groupDesign_isBlockDesign :
    (groupDesign (F := F)).IsBlockDesign 2 (Fintype.card (Option F)) := by
  constructor
  · intro b hb
    have he : b = univ := mem_singleton.mp hb
    subst b
    exact card_univ
  · intro S _
    refine ⟨univ, ⟨mem_singleton_self _, subset_univ _⟩, ?_⟩
    intro b hb
    exact mem_singleton.mp hb.1

/-- The point set has one common point and a finite point for every column-symbol pair. -/
abbrev Points (F : Type*) := Option ((Option F) × F)

/-- Actual finite blocks over the explicitly displayed point set. -/
def blocks : Finset (Finset (Points F)) :=
  SharedPoint.blocks (FiniteFieldRows.transversal (F := F)) (groupDesign (F := F))

theorem isBlockDesign :
    (blocks (F := F)).IsBlockDesign 2 (Fintype.card F + 1) := by
  have h := SharedPoint.isBlockDesign (FiniteFieldRows.transversal (F := F))
    (groupDesign (F := F)) (groupDesign_isBlockDesign (F := F))
  simpa only [blocks, Fintype.card_option] using h

omit [Field F] [DecidableEq F] in
/-- The exact point count is q² + q + 1, where q is the finite field's cardinality. -/
theorem card_points : Fintype.card (Points F) =
    Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp only [Points, Fintype.card_option, Fintype.card_prod]
  ring

end Erdos643Design.Foundation.ProjectivePlane
