import Openmath.Erdos643Design.HananiExistence
import Openmath.Erdos643R3.CoefficientOneFinal
import Openmath.Erdos643R3.PublicSmallOrders
import Openmath.Erdos643R3.FCBridge
import Openmath.Erdos643R3.G3Interface

/-! Exact residue-class extremal equality using unconditional design existence.
The qualified small-order import retains the complete existing coefficient-one proof graph. -/
set_option autoImplicit false
namespace Erdos643R3.CoefficientOneHanani

/-- Exact extremal equality for every order admitting the five-block design construction. -/
theorem extremal_eq (n : ℕ) (hn : n % 20 = 1 ∨ n % 20 = 5) :
    Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) = n.choose 2 := by
  obtain ⟨D,hD⟩ := Erdos643Design.HananiExistence.exists_design n hn
  exact CoefficientOneFinal.extremal_eq_of_supplied_design n D hD

end Erdos643R3.CoefficientOneHanani
