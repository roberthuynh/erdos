import EvenFactor.Extremal
import FactorMatching.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Finset SimpleGraph
namespace Erdos585.EvenFactorCriterion
universe u
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Actual matching obstruction. No original-barrier normalization is asserted. -/
theorem no_factor_gadget_violator (hq : 0 < q)
    (hno : ¬ SpanningFactor G q) :
    ∃ X : Set (FactorMatching.Vertex q G),
      (FactorMatching.gadget q G).IsTutteViolator X := by
  classical
  have hm : ¬ ∃ M : (FactorMatching.gadget q G).Subgraph, M.IsPerfectMatching := by
    intro h
    have hf := (FactorMatching.spanning_q_factor_iff_matching q G hq).mpr h
    obtain ⟨H, hspan, hreg⟩ := hf
    apply hno
    refine ⟨H, hspan, ?_⟩
    intro v
    exact (FactorMatching.degree_fintype_irrel H.coe v _ _).trans (hreg v)
  have hh : ¬ ∀ X : Set (FactorMatching.Vertex q G),
      ¬ (FactorMatching.gadget q G).IsTutteViolator X := by
    intro h
    exact hm ((SimpleGraph.tutte (G := FactorMatching.gadget q G)).mpr h)
  push_neg at hh
  exact hh

/-- Positive finite extremal deletion produced internally from the original host. -/
theorem no_factor_gadget_extremal (hq : 0 < q)
    (hno : ¬ SpanningFactor G q) :
    ∃ X : Finset (FactorMatching.Vertex q G),
      ExtremalDeletion (FactorMatching.gadget q G) X ∧
        0 < gadgetDeficiency (FactorMatching.gadget q G) X := by
  classical
  apply exists_positive_extremal
  intro h
  have hf := (FactorMatching.spanning_q_factor_iff_matching q G hq).mpr h
  obtain ⟨H, hspan, hreg⟩ := hf
  apply hno
  refine ⟨H, hspan, ?_⟩
  intro v
  exact (FactorMatching.degree_fintype_irrel H.coe v _ _).trans (hreg v)

end Erdos585.EvenFactorCriterion
