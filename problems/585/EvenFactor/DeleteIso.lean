import EvenFactor.Extremal
import EvenFactor.LiftedGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset SimpleGraph
namespace Erdos585.EvenFactorCriterion
open FactorMatching
universe u v
local instance deleteIsoDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Odd components and their actual support sizes are invariant under graph isomorphism. -/
theorem iso_odd_count {A : Type u} {B : Type v} (G : SimpleGraph A)
    (H : SimpleGraph B) (e : G ≃g H) : G.oddComponents.ncard = H.oddComponents.ncard := by
  have hc (C : G.ConnectedComponent) : C.supp.ncard = (e.connectedComponentEquiv C).supp.ncard :=
    Set.ncard_congr' (C.isoEquivSupp e)
  exact Set.ncard_congr' (e.connectedComponentEquiv.subtypeEquiv (fun C => by
    change Odd C.supp.ncard ↔ Odd (e.connectedComponentEquiv C).supp.ncard
    rw [hc C]))

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The remaining original gadget and the exact vertex-deletion graph in Mathlib's Tutte
criterion have the same physical vertices and edges. -/
def deleteRemainingIso (S T : Finset V) :
    ((⊤ : (gadget q G).Subgraph).deleteVerts (canonicalDeletion q G S T : Set _)).coe ≃g
      remainingGraph q G S T where
  toFun x := ⟨x.val,x.property.2⟩
  invFun x := ⟨x.val,⟨Set.mem_univ _,x.property⟩⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_rel_iff' := by
    intro x y
    change (gadget q G).Adj x.val y.val ↔ _
    simp only [Subgraph.coe_adj, Subgraph.deleteVerts_adj, Subgraph.verts_top,
      Set.mem_univ, Subgraph.top_adj, true_and]
    simp only [x.property.2, y.property.2, not_false_eq_true, true_and]

lemma canonical_oddRemaining (S T : Finset V) :
    oddRemaining (gadget q G) (canonicalDeletion q G S T) =
      (remainingGraph q G S T).oddComponents.ncard :=
  iso_odd_count _ _ (deleteRemainingIso q G S T)

end Erdos585.EvenFactorCriterion
