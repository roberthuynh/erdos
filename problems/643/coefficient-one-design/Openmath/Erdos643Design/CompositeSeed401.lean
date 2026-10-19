import Openmath.Erdos643Design.CompositeDesigns
import Openmath.Erdos643Design.CyclicSeed81

/-! Exact composite order401, isolated from the other seed orders. -/
set_option autoImplicit false
namespace Erdos643Design.CompositeSeeds

theorem exists_design401 : ∃ B : Finset (Finset (Fin 401)), B.IsBlockDesign 2 5 :=
  design401_of_81 CyclicSeed81.exists_design

end Erdos643Design.CompositeSeeds
