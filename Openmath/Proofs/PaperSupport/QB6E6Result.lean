import Openmath.Proofs.PaperSupport.QB6CoveredFive
import Openmath.Proofs.PaperSupport.QB6FiveSelection

/- 




-/

universe u
namespace Erdos585.QB6E6Result

theorem e6_repair : QB6Assembly.E6Repair.{u} :=
  QB6E6Lean.e6_of_physical_producers
    QB6CoveredFive.covered_five_supply
    QB6FiveSelection.actual_five_selection

#print axioms e6_repair
#check e6_repair
#print QB6Assembly.E6Repair
#print QB6Assembly.E6Input
#print QB4.Quartic

end Erdos585.QB6E6Result
