import Openmath.Erdos643R3.G1Check2
set_option autoImplicit false
namespace Erdos643R3.G1C2
open Erdos643R3.G1Check2
theorem cert_a : allT2 = true := by decide +kernel
theorem cert_v1 : runV2 1 = true := by decide +kernel
theorem cert_v2 : runV2 2 = true := by decide +kernel
theorem cert_v3 : runV2 3 = true := by decide +kernel
theorem cert_v4 : runV2 4 = true := by decide +kernel
theorem cert_v5 : runV2 5 = true := by decide +kernel
end Erdos643R3.G1C2
