/-
Copyright 2026 Robert Huynh.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import AllHQuotaNonstrict.Intersections

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section

namespace Erdos585.AllHQuotaNonstrict
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Data
variable {h q j ξ : ℕ} {A B : Finset V} (d : Data h q j ξ G A B)
include d

open Classical in
lemma high_compare_union {Z K T : Finset V} (hk : AllHTopTwo.HighAbove q j G A B Z K)
    (hT : LargePositive q j G A B T) (hZT : Z ⊆ T) :
    thetaJ q j G A B T ≤ thetaJ q j G A B (K ∪ T) := by
  classical
  have hI := d.large_intersection hk.positive.1 hk.positive.2.1 hk.positive.2.2
    hT.1 hT.2.1 hT.2.2
  have hzi : Z ⊆ K ∩ T := subset_inter hk.contains hZT
  have hθi : thetaJ q j G A B (K ∩ T) ≤ thetaJ q j G A B K := by
    classical
    by_cases hp : 0 < thetaJ q j G A B (K ∩ T)
    · exact hk.height _ ⟨inter_subset_left.trans hk.positive.1, hI, hp⟩ hzi
    · have hpk := hk.positive.2.2
      omega
  have hs := H3Unequal.Input.theta_supermod (G := G) q j A B K T
  omega

end Data
end Erdos585.AllHQuotaNonstrict
