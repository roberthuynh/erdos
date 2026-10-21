import Openmath.Erdos643R3.CPrimeMain
import Openmath.Erdos643R3.CoefficientOne

/-!
# Conditional assembly from the anchor inequality

The mathematical input below is the global G3h' anchor inequality, expressed
by the explicit G3hPrimeAt hypothesis. This module proves the conditional reduction.
-/

set_option autoImplicit false

namespace Erdos643R3
namespace CoefficientOneAssembly

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- The G3h' anchor inequality, quantified over all avoiding uniform hosts. -/
def G3hPrimeAt : Prop :=
  ∀ H : Finset (Finset V), Identity.Uniform H →
    ¬ Erdos643.HypergraphBasics.Forbidden H → CPrime.G3hPrime H

/-- The actual G1 and C' modules discharge recovery from the sole G3h' input. -/
theorem recovery_of_G3hPrimeAt (hG3 : G3hPrimeAt V) :
    CoefficientOne.RecoveryAt V := by
  intro H hH hav
  exact CPrimeMain.recovery_of_G3hPrime hH hav (hG3 H hH hav)

/-- Once G3h' is proved, the exact finite coefficient-one target follows. -/
theorem coefficient_one_of_G3hPrimeAt (hG3 : G3hPrimeAt V) :
    CoefficientOne.CoefficientOneAt V :=
  CoefficientOne.coefficient_one_of_recovery V (recovery_of_G3hPrimeAt V hG3)

end CoefficientOneAssembly
end Erdos643R3
