import Mathlib
import Openmath.Erdos643R3.PwCheck

/-!
# pw2312 Computation C1, kernel-checked

`c1_cert` evaluates the branch-and-bound checker `PwCheck.allT` (all 364 type-2 triples with `t ≤ 11`, the box
`[0,92]^6`, target `23/12`) in the Lean kernel with `decide +kernel` (no `native_decide`, no extra axioms), and
`caseII` turns it into Case II of pw2312 Theorem 2 through `PwCheck.caseII_of_allT`.
-/

set_option autoImplicit false

namespace Erdos643R3
namespace PwC1

open Erdos643R3.Pw2312 Erdos643R3.PwCheck

/-- The C1 certificate, re-derived by the kernel. -/
theorem c1_cert : allT = true := by decide +kernel

/-- **Case II of Theorem 2** (no big relation, all type-1 counts `≤ 92`, `t ≤ 11`): `Φ ≥ 23/12`. -/
theorem caseII (π : Profile) (hF : Feas π) (ht : π.t0 + π.t1 + π.t2 ≤ 11)
    (hbox : π.f0 ≤ 92 ∧ π.g0 ≤ 92 ∧ π.f1 ≤ 92 ∧ π.g1 ≤ 92 ∧ π.f2 ≤ 92 ∧ π.g2 ≤ 92)
    (hnb : ¬ (Big0 π ∨ Big1 π ∨ Big2 π)) : 23 / 12 ≤ Phi π :=
  caseII_of_allT c1_cert π hF ht hbox hnb

end PwC1
end Erdos643R3
