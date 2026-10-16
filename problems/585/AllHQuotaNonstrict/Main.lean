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
import AllHQuotaNonstrict.Local
import AllHQuotaNonstrict.ActualSelection

/-! R280: the exact R265 uniform nonstrict fragile-quota original-host endpoint.
One internally selected omission pays every original cut and determines
the exact support of the returned original regular subgraph. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section

namespace Erdos585.AllHQuotaNonstrict
open QB4 B5 L34 H3Unequal
universe u

open Classical in
/-- The variable-offset nonstrict endpoint for every original finite host. -/
theorem uniform_quota_nonstrict (h q j ξ : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (host : Host h q j ξ G A B)
    (quota : ∃ O0 : Finset V, O0⊆B ∧ #O0=j ∧ ∀ x∈A,
      G.degree x≤q+2*h-5 → dg G O0 x≤G.degree x-q) :
    ∃ O : Finset V, O ⊆ B ∧ #O = j ∧
      (∀ T ⊆ B, O ⊆ T → thetaJ q j G A B T ≤ 0) ∧
      ∃ H : G.Subgraph, H.verts = (↑(A ∪ (B \ O)) : Set V) ∧
        H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  classical
  have d := host.to_data
  have hquota : ∃ O, d.QuotaFeasible O := by
    obtain ⟨O0,hOB,hOj,hq0⟩ := quota
    refine ⟨O0,hOB,hOj,?_⟩
    intro x hx
    have hxA := (d.mem_fragile.mp hx).1
    have hd : dg G B x=G.degree x := dg_eq_degree host.bipartite hxA
    rw [hd]
    exact hq0 x hxA (by rw [←hd];exact (d.mem_fragile.mp hx).2)
  obtain ⟨O, hOB, hOj, hcuts⟩ := ActualSelection.common_omission d hquota
  have hfactor := factor_of_common_omission q j host.card hOB hOj hcuts
  have hq := host.parameters.q_pos
  have hA : A.Nonempty := card_pos.mp (by have hh := d.shores_large.1; omega)
  obtain ⟨H, hverts, hnonempty, hregular⟩ :=
    factor_exact_subgraph hq hA (host.disjoint.mono_right sdiff_subset) hfactor
  exact ⟨O, hOB, hOj, hcuts, H, hverts, hnonempty, hregular⟩

end Erdos585.AllHQuotaNonstrict
