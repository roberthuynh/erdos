import Openmath.Erdos643Design.SharedBlockFill
import Openmath.Erdos643Design.CompositeRows
import Openmath.Erdos643Design.DesignPrime61

/-! The order-285 shared-five-point construction from actual finite inputs. -/
set_option autoImplicit false
namespace Erdos643Design.Seed285

/-- No assumed local design or transversal remains in the final endpoint. -/
theorem exists_design : ∃ H : Finset (Finset (Fin 285)), H.IsBlockDesign 2 5 := by
  obtain ⟨D,hD⟩ := Seed61.exists_design
  exact Foundation.SharedBlockFill.finite_exists (n := 56) (k := 5) (by decide)
    CompositeSeeds.td5_56 D hD

end Erdos643Design.Seed285
