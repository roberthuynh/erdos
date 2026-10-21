import Mathlib
import Openmath.Erdos643R3.PwCheck

/-!
# pw2312 Computation C2, kernel-checked

`c2_cert` evaluates the branch-and-bound checker `PwCheck.allT2` (all 364 type-2 triples with `t ≤ 11`, the box
`[0,92]^4` of `(ab, ba, cb, ca)`, target `G + k(ab + tA, tA) + k(ba + tB, tB) ≥ 11/12`, with `k` bounded through
`PwCheck.kdC`) in the Lean kernel with `decide +kernel`, and `caseIII` turns it into Case III of pw2312 Theorem 2
with the big relation `ρ_0 = R_c` through `PwCheck.caseIII_of_allT2`.
-/

set_option autoImplicit false

namespace Erdos643R3
namespace PwC2

open Erdos643R3.Pw2312 Erdos643R3.PwCheck

/-- The C2 certificate, re-derived by the kernel. -/
theorem c2_cert : allT2 = true := by decide +kernel

/-- **Case III of Theorem 2** with `ρ_0` big and the other relations' counts `≤ 92`, `t ≤ 11`: `Φ ≥ 23/12`. -/
theorem caseIII (π : Profile) (hF : Feas π) (ht : π.t0 + π.t1 + π.t2 ≤ 11) (hf0 : 23 ≤ π.f0) (hg1 : 23 ≤ π.g1)
    (hbox : π.g0 ≤ 92 ∧ π.f1 ≤ 92 ∧ π.f2 ≤ 92 ∧ π.g2 ≤ 92) : 23 / 12 ≤ Phi π :=
  caseIII_of_allT2 c2_cert π hF ht hf0 hg1 hbox

end PwC2
end Erdos643R3
