import Openmath.Erdos643R3.CoefficientOneFinal
import Openmath.Erdos643R3.DesignBaseOrders
import Openmath.Erdos643R3.FCBridge
import Openmath.Erdos643R3.G3Interface

/-! Exact extremal values obtained from the supplied one- and five-vertex designs. -/
namespace Erdos643R3.PublicSmallOrders

theorem extremal_one :
    Hypergraph.extremalNumber 1 3 (fun H => ¬ H.HasRepeatedDisjointUnion) =
      (1 : ℕ).choose 2 :=
  CoefficientOneFinal.extremal_eq_of_supplied_design 1 ∅ Erdos643Design.design_one

theorem extremal_five :
    Hypergraph.extremalNumber 5 3 (fun H => ¬ H.HasRepeatedDisjointUnion) =
      (5 : ℕ).choose 2 :=
  CoefficientOneFinal.extremal_eq_of_supplied_design 5 {Finset.univ} Erdos643Design.design_five

end Erdos643R3.PublicSmallOrders
