import EvenFactor.Defs
import NEQAssembly.Partial

/-! Alignment of original retained components, counts and shores.
These alignment lemmas do not establish the full factor criterion.
Verification of that criterion is separate. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
namespace Erdos585.NEQAssembly
universe u

lemma criterion_original_component_support {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V)
    (C : (G.induce (R : Set V)).ConnectedComponent) :
    EvenFactorCriterion.componentVerts G R C = NEQ.componentVerts G R C := by
  rfl

lemma criterion_original_odd_cardinality {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T R : Finset V) :
    EvenFactorCriterion.oddTo G T R = NEQ.oddCount G T R := by
  rfl

lemma criterion_original_delta_alignment {V : Type u} [Fintype V] [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (S T : Finset V) :
    EvenFactorCriterion.standardDelta G q S T = NEQ.delta q G univ T S := by
  rw [original_shore_swap]
  unfold EvenFactorCriterion.standardDelta
  rw [criterion_original_odd_cardinality]

#print axioms criterion_original_component_support
#print axioms criterion_original_odd_cardinality
#print axioms criterion_original_delta_alignment
end Erdos585.NEQAssembly
