import Openmath.Erdos643R3.G1Check
set_option autoImplicit false
namespace Erdos643R3.G1C1
open Erdos643R3.G1Check
theorem cert_a : allT = true := by decide +kernel
theorem cert_v1 : runV 1 = true := by decide +kernel
theorem cert_v2 : runV 2 = true := by decide +kernel
theorem cert_v3 : runV 3 = true := by decide +kernel
theorem cert_v4 : runV 4 = true := by decide +kernel
end Erdos643R3.G1C1
