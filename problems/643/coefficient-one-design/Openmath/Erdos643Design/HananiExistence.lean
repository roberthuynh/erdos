import Openmath.Erdos643Design.FiniteBaseOrders
import Openmath.Erdos643Design.CyclicSeed161
import Openmath.Erdos643Design.DesignSeed285

/-! General 2-(n,5,1) design existence from explicit finite seeds and the actual recursive construction. -/
set_option autoImplicit false
namespace Erdos643Design.HananiExistence

/-- Every admissible order admits an actual upstream two-design with blocks of size five. -/
theorem exists_design (n : ℕ) (hn : n % 20 = 1 ∨ n % 20 = 5) :
    ∃ D : Finset (Finset (Fin n)), D.IsBlockDesign 2 5 :=
  FiniteBaseOrders.residue_designs_of_two_seeds
    CyclicSeed161.exists_design Seed285.exists_design n hn

end Erdos643Design.HananiExistence
