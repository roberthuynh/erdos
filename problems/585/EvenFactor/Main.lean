import EvenFactor.DegreeCount
import GadgetNormalization.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset SimpleGraph
namespace Erdos585.EvenFactorCriterion
open FactorMatching
universe u
local instance criterionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The extremal deletion is represented by original shores, with literal vertex membership. -/
theorem extremal_original_sets (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hq : 0 < q) (hmin : ∀ v : V, q ≤ G.degree v)
    (X : Finset (Vertex q G)) (hX : ExtremalDeletion (gadget q G) X) :
    ∃ S T : Finset V, Disjoint S T ∧ X = canonicalDeletion q G S T := by
  obtain ⟨S,T,hST,hslots,hstubs⟩ := GadgetNormalization.extremal_canonical q G hq hmin X hX
  refine ⟨S,T,hST,?_⟩
  ext x
  cases x with
  | inl s => exact (hslots s.1 s.2).trans (mem_canonical_slot q G S T s.1 s.2).symm
  | inr d => exact (hstubs d).trans (mem_canonical_stub q G S T d).symm

/-- A bare original constant-even factor barrier, with no criterion, min-degree,
normalization or matching supplier premise. -/
theorem even_no_spanning_factor_barrier (q : ℕ) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hq : 6 ≤ q) (heven : Even q)
    (hcap : G.maxDegree ≤ 2*q-2)
    (hno : ¬ (∃ H : G.Subgraph, H.IsSpanning ∧ H.coe.IsRegularOfDegree q)) :
    ∃ S T : Finset V, Disjoint S T ∧ standardDelta G q S T < 0 := by
  have hqpos : 0 < q := by omega
  by_cases hlow : ∃ v : V, G.degree v < q
  · obtain ⟨v,hv⟩ := hlow
    exact low_degree_barrier G q v hv
  · have hmin : ∀ v : V, q ≤ G.degree v := by
      intro v
      by_contra h
      exact hlow ⟨v,by omega⟩
    have hn : ¬ SpanningFactor G q := by
      intro ⟨H,hspan,hreg⟩
      apply hno
      refine ⟨H,hspan,?_⟩
      intro v
      exact (FactorMatching.degree_fintype_irrel H.coe v _ _).trans (hreg v)
    obtain ⟨X,hX,hpositive⟩ := no_factor_gadget_extremal q G hqpos hn
    obtain ⟨S,T,hST,hcanonical⟩ := extremal_original_sets q G hqpos hmin X hX
    refine ⟨S,T,hST,canonical_positive_negative G q hqpos heven hmin S T hST ?_⟩
    rw [← hcanonical]
    exact hpositive

end Erdos585.EvenFactorCriterion
