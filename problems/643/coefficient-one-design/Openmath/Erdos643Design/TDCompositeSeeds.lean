import Openmath.Erdos643Design.TD60
import Openmath.Erdos643Design.TD84

/-! GPLv3 composite transversal constructions with Sage-derived TD21/TD60
dependencies. See their module notices and NOTICE-DESIGN.md, COPYING and
licenses/Sage-COPYING.txt for original source provenance and terms. -/


set_option autoImplicit false
namespace Erdos643Design.TDCompositeSeeds
open Foundation
noncomputable section
def rows60 : TransversalRows (Fin 5) (Fin 60) :=
  let e : Fin 5 ↪ Option (Fin 4) := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simp))
  (TD60.supplied.transversal.restrict e).symbolEquiv
    (Fintype.equivFinOfCardEq (by simp [TD60.G]))

theorem exists_rows60 : Nonempty (TransversalRows (Fin 5) (Fin 60)) := ⟨rows60⟩
theorem exists_rows84 : Nonempty (TransversalRows (Fin 5) (Fin 84)) := TD84.exists_rows
end
end Erdos643Design.TDCompositeSeeds
