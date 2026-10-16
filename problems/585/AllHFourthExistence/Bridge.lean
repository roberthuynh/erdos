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
import AllHFourthQuotaFailure.Main
import AllHQuotaSurplus.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section

namespace Erdos585.AllHFourthExistence
open QB4 B5 L34 H3Unequal
open AllHFourthQuotaFailure (Host MinimalFailed Failed ThreeFailure)
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {h q j : ℕ} {A B T I : Finset V}

open Classical in
/-- The literal fourth-surplus host also meets the uniform positive-surplus contract. -/
lemma quota_host (host : Host h q j G A B) : AllHQuotaSurplus.Host h q j G A B := by
  have hn := AllHFourthQuotaFailure.Host.numeric host
  refine ⟨⟨by have hh := host.height; omega, host.large, by omega, by omega⟩,
    host.disjoint, host.cover, host.bipartite, host.card, host.order,
    host.min_degree, host.cap_degree, host.edges, host.proper⟩

open Classical in
/-- This is the original A-shore scar identity, obtained from the full original edge equation. -/
lemma original_scar (host : Host h q j G A B) :
    deficiency (2*(q:ℤ)-2) G B A = 4*(q:ℤ)-AllHFourthQuotaFailure.offset h+j := by
  have he := host.edges
  have hc := host.card
  have hs := AllHFourthQuotaFailure.Host.shore_order host
  have hn := AllHFourthQuotaFailure.Host.numeric host
  have hj := host.surplus
  have hh := host.height
  have hqm : q-1+1=q := by omega
  have hcm : AllHFourthQuotaFailure.constant h q + AllHFourthQuotaFailure.offset h = h*q := by
    apply Nat.sub_add_cancel
    have hlarge := host.large
    unfold AllHFourthQuotaFailure.offset
    have hprod : q≤h*q := by nlinarith
    nlinarith
  have hje : (j:ℤ)=(h:ℤ)-4 := by omega
  rw [deficiency_eq,ec_eq_ncard host.bipartite]
  zify at he hc hs hqm hcm
  nlinarith

open Classical in
/-- Every inclusion-minimal actual quota failure has at most three original A rows. -/
lemma minimal_failed_card (host : Host h q j G A B)
    (hi : MinimalFailed G q j B T I) (hT : T⊆A) : #I≤3 := by
  have hIA : I⊆A := hi.subset.trans hT
  have hlo : ((q:ℤ)-j-1)*#I ≤ deficiency (2*(q:ℤ)-2) G B I := by
    calc
      _ = ∑ _x∈I, ((q:ℤ)-j-1) := by simp only [sum_const,nsmul_eq_mul]; ring
      _ ≤ _ := by
        apply sum_le_sum
        intro x hx
        have ht := hi.quota_lt hx
        have hm := host.min_degree x
        have hd := dg_eq_degree host.bipartite (hIA hx)
        change (q:ℤ)-j-1 ≤ 2*(q:ℤ)-2-dg G B x
        omega
  have hcap : ∀ x∈A, (dg G B x:ℤ)≤2*(q:ℤ)-2 := by
    intro x hx
    have hc := host.cap_degree x
    have hd := dg_eq_degree host.bipartite hx
    have hn := AllHFourthQuotaFailure.Host.numeric host
    omega
  have hhi := deficiency_le_subset (2*(q:ℤ)-2) hIA hcap
  have he := original_scar host
  rw [he] at hhi
  have hn := AllHFourthQuotaFailure.Host.numeric host
  have hh := host.height
  have hj := host.surplus
  have hnonneg : (0:ℤ)≤q-j-1 := by omega
  by_contra! hc
  have hfour : (4:ℤ)≤#I := by omega
  have hmul := mul_le_mul_of_nonneg_left hfour hnonneg
  have hbound : (AllHFourthQuotaFailure.offset h:ℤ)≤5*(h:ℤ)-16 := by
    have hje : (j:ℤ)=(h:ℤ)-4 := by omega
    nlinarith
  unfold AllHFourthQuotaFailure.offset at hbound
  push_cast at hbound
  nlinarith [sq_nonneg (h:ℤ)]

open Classical in
/-- A failed family can be padded with redundant constraints to three distinct original rows. -/
lemma failed_three (host : Host h q j G A B) (hf : Failed G q j B T) (hT : T⊆A) :
    ∃ x∈A, ∃ y∈A, ∃ z∈A, x≠y ∧ x≠z ∧ y≠z ∧ ThreeFailure G q j B x y z := by
  have hn := AllHFourthQuotaFailure.Host.numeric host
  have hcard := host.card
  obtain ⟨b,hb⟩ := card_pos.mp (show 0<#B by omega)
  have hA : q≤#A := calc
    q ≤ G.degree b := host.min_degree b
    _ = dg G A b := (dg_eq_degree host.bipartite.symm hb).symm
    _ ≤ #A := dg_le_card A b
  obtain ⟨I,hi⟩ := AllHFourthQuotaFailure.exists_minimal_failed hf
  have hc := minimal_failed_card host hi hT
  obtain ⟨U,hIU,hUA,hUc⟩ := exists_subsuperset_card_eq (hi.subset.trans hT) hc
    (show 3≤#A by omega)
  obtain ⟨x,y,z,hxy,hxz,hyz,hU⟩ := card_eq_three.mp hUc
  subst U
  have hx : x∈A := hUA (by simp)
  have hy : y∈A := hUA (by simp)
  have hz : z∈A := hUA (by simp)
  refine ⟨x,hx,y,hy,z,hz,hxy,hxz,hyz,?_⟩
  intro hgood
  obtain ⟨O,hOB,hOj,hpay⟩ := hgood
  exact hi.failed ⟨O,hOB,hOj,fun v hv => hpay v (hIU hv)⟩

end Erdos585.AllHFourthExistence
