import Openmath.Erdos643Design.CompositeDesigns
import Openmath.Erdos643Design.DesignPrime41
import Openmath.Erdos643Design.DesignPrime61
import Openmath.Erdos643Design.DesignSeed21
import Openmath.Erdos643Design.FieldFamily9
import Openmath.Erdos643Design.FieldFamily17

/-! Concrete composite seed orders from actual upstream block designs. -/
set_option autoImplicit false
namespace Erdos643Design.CompositeSeeds

theorem exists_design165 : ∃ B : Finset (Finset (Fin 165)), B.IsBlockDesign 2 5 :=
  design165_of_41_21 Seed41.exists_design Seed21.exists_design

theorem exists_design181 : ∃ B : Finset (Finset (Fin 181)), B.IsBlockDesign 2 5 :=
  design181_of_45_21 FieldFamily9.exists_design Seed21.exists_design

theorem exists_design201 : ∃ B : Finset (Finset (Fin 201)), B.IsBlockDesign 2 5 :=
  design201_of_41 Seed41.exists_design

theorem exists_design301 : ∃ B : Finset (Finset (Fin 301)), B.IsBlockDesign 2 5 :=
  design301_of_61 Seed61.exists_design

theorem exists_design421 : ∃ B : Finset (Finset (Fin 421)), B.IsBlockDesign 2 5 :=
  design421_of_85 FieldFamily17.exists_design

theorem exists_design425 : ∃ B : Finset (Finset (Fin 425)), B.IsBlockDesign 2 5 :=
  design425_of_85 FieldFamily17.exists_design

end Erdos643Design.CompositeSeeds
