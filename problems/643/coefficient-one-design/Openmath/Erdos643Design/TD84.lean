import Openmath.Erdos643Design.TD21
import Mathlib.FieldTheory.Finite.GaloisField

/-! GPLv3 derived construction using the SageMath finite table in TD21.
Original table provenance and terms are retained in TD21, NOTICE-DESIGN.md,
COPYING and licenses/Sage-COPYING.txt. -/


set_option autoImplicit false
namespace Erdos643Design.TD84
open Foundation
noncomputable section
instance : Fact (Nat.Prime 2) := ⟨by decide⟩
abbrev F := GaloisField 2 2
instance : Fintype F := Fintype.ofFinite _
instance : DecidableEq F := Classical.decEq _
theorem card_field : Fintype.card F = 4 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)]
  decide
def fieldColumns : Fin 4 ↪ F :=
  (Fintype.equivFinOfCardEq card_field).symm.toEmbedding
def supplied : DifferenceMatrix (Fin 4) (F × ZMod 21) :=
  ((DifferenceMatrix.field F).restrict fieldColumns).product TD21.supplied

def rows : TransversalRows (Fin 5) (Fin 84) :=
  let e : Fin 5 ↪ Option (Fin 4) := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simp))
  (supplied.transversal.restrict e).symbolEquiv
    (Fintype.equivFinOfCardEq (by simp [card_field]))

theorem exists_rows : Nonempty (TransversalRows (Fin 5) (Fin 84)) := ⟨rows⟩
end
end Erdos643Design.TD84
