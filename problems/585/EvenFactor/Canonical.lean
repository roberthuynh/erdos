import EvenFactor.TutteBridge
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset SimpleGraph Function
namespace Erdos585.EvenFactorCriterion
open QB4 FactorMatching
universe u
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]

def dartsAt (T : Finset V) : Finset G.Dart := univ.filter (fun d => d.fst ∈ T)

def canonicalDeletion (S T : Finset V) : Finset (Vertex q G) :=
  (S ×ˢ (univ : Finset (Fin q))).disjSum (dartsAt G T)

@[simp] lemma mem_dartsAt (T : Finset V) (d : G.Dart) :
    d ∈ dartsAt G T ↔ d.fst ∈ T := by simp [dartsAt]

@[simp] lemma mem_canonical_slot (S T : Finset V) (v : V) (i : Fin q) :
    Sum.inl (v,i) ∈ canonicalDeletion q G S T ↔ v ∈ S := by
  simp [canonicalDeletion]

@[simp] lemma mem_canonical_stub (S T : Finset V) (d : G.Dart) :
    Sum.inr d ∈ canonicalDeletion q G S T ↔ d.fst ∈ T := by
  simp [canonicalDeletion]

lemma dartsAt_card (T : Finset V) : #(dartsAt G T) = ∑ v ∈ T, G.degree v := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun d : G.Dart => d.fst) (t := T)
    (fun d hd => (mem_dartsAt G T d).mp hd)]
  apply sum_congr rfl
  intro v hv
  have he : (dartsAt G T).filter (fun d => d.fst = v) =
      univ.filter (fun d : G.Dart => d.fst = v) := by
    ext d
    simp only [mem_filter, mem_dartsAt, mem_univ, true_and]
    exact ⟨And.right, fun h => ⟨h ▸ hv,h⟩⟩
  rw [he, G.dart_fst_fiber_card_eq_degree]

/-- The removed vertices are counted with ORIGINAL degree incidences. -/
theorem canonical_card (S T : Finset V) :
    #(canonicalDeletion q G S T) = q * #S + ∑ v ∈ T, G.degree v := by
  rw [canonicalDeletion, card_disjSum, card_product, card_univ, Fintype.card_fin,
    dartsAt_card]
  ring

end Erdos585.EvenFactorCriterion
