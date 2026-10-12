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
import AllHQuotaNonstrict.Geometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section

namespace Erdos585.AllHQuotaNonstrict
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {h q j ξ : ℕ} {A B : Finset V}

namespace Host

open Classical in
lemma shore_order (host : Host h q j ξ G A B) : #A + #B = Fintype.card V := by
  have hc := card_union_of_disjoint host.disjoint
  rw [host.cover, card_univ] at hc
  exact hc.symm

open Classical in
/-- All paired resources are proved from the literal original host. -/
theorem to_data (host : Host h q j ξ G A B) :
    letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
    Data h q j ξ G A B := by
  classical
  have horder := host.shore_order
  have hq := host.parameters.q_pos
  refine ⟨host.parameters, host.disjoint, host.card, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [dg_eq_degree host.bipartite ha]
    exact host.min_degree a
  · intro a ha
    rw [dg_eq_degree host.bipartite ha]
    exact host.cap_degree a
  · intro b hb
    rw [dg_eq_degree host.bipartite.symm hb]
    exact host.min_degree b
  · intro b hb
    rw [dg_eq_degree host.bipartite.symm hb]
    exact host.cap_degree b
  · rw [deficiency_eq, ec_eq_ncard host.bipartite]
    have he := host.edges
    have hc := host.card
    have hqm : q - 1 + 1 = q := by omega
    have hcm : constant h q ξ + ξ = h * q := by
      exact Nat.sub_add_cancel host.parameters.offset_le_product
    zify at he hc horder hqm hcm
    nlinarith
  · intro X hX Y hY hlarge hproper
    have hXY := host.disjoint.mono hX hY
    have hc := card_union_of_disjoint hXY
    have hf := host.proper (X ∪ Y) (by omega) (by omega)
    rw [induced_edges_eq_ec host.disjoint host.bipartite hX hY, hc] at hf
    have hconst := host.parameters.constant_cast
    unfold potential
    push_cast at hf ⊢
    nlinarith

end Host
end Erdos585.AllHQuotaNonstrict
