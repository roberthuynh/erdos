import Openmath.Erdos643R3.CoefficientOneHanani

/-! Exact forcing values at the admissible orders, with the extremal/forcing
convention stated explicitly. -/
set_option autoImplicit false

namespace Erdos643R3.CoefficientOneFullSolution

/-- The forcing threshold is the extremal number plus one. -/
theorem forcing_eq (n : ℕ) (hn : n % 20 = 1 ∨ n % 20 = 5) :
    Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) + 1 =
      n.choose 2 + 1 := by
  rw [CoefficientOneHanani.extremal_eq n hn]

end Erdos643R3.CoefficientOneFullSolution
