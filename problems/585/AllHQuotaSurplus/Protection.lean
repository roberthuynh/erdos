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
import AllHQuotaSurplus.Geometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section

namespace Erdos585.AllHQuotaSurplus
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Data
variable {h q j : ℕ} {A B : Finset V} (d : Data h q j G A B)
include d

open Classical in
/-- The actual fragile scars bound the entire original fragile family. -/
lemma fragile_card : #d.fragileRows ≤ h-j := by
  have hlo : ((q:ℤ)-2*h+3)*#d.fragileRows ≤
      deficiency (2*(q:ℤ)-2) G B d.fragileRows := by
    calc
      _ = ∑ _x∈d.fragileRows, ((q:ℤ)-2*h+3) := by simp [mul_comm]
      _ ≤ _ := by
        apply sum_le_sum
        intro x hx
        have hd := (d.mem_fragile.mp hx).2
        have hh := d.parameters.height
        omega
  have hhi := d.scar_le d.fragile_subset
  have hj := d.parameters.j_bounds
  have hn := d.parameters.numeric
  have hh := d.parameters.height_int
  by_contra! hbad
  have hc : (h:ℤ)-j+1 ≤ #d.fragileRows := by omega
  have hp := mul_le_mul_of_nonneg_left hc (show (0:ℤ) ≤ q-2*h+3 by omega)
  have hm := mul_nonneg (show (0:ℤ) ≤ j-1 by omega) (show (0:ℤ) ≤ 2*h-3 by omega)
  nlinarith

open Classical in
/-- Every actual fragile row lies in EVERY positive large optimizer. -/
lemma fragile_in_optimizer {K C : Finset V} (opt : Optimizer q G A B K C)
    (hK : K⊆B) (hl : q-1≤#K) (hp : 0<thetaJ q j G A B K)
    {x : V} (hx : x∈d.fragileRows) : x∈C := by
  by_contra hn
  have hv : x∈A\C := mem_sdiff.mpr ⟨(d.mem_fragile.mp hx).1,hn⟩
  have hs := single_le_sum (f := fun v => 2*(q:ℤ)-2-dg G B v)
    (fun v hv => by have hc := d.capA_int (mem_sdiff.mp hv).1; omega) hv
  change 2*(q:ℤ)-2-dg G B x≤deficiency (2*(q:ℤ)-2) G B (A\C) at hs
  have ho := d.outside_scar_le opt hK hl hp
  have hd := (d.mem_fragile.mp hx).2
  have hq := d.parameters.numeric
  have hh := d.parameters.height
  omega

open Classical in
lemma neighbor_residual_card {K : Finset V} (hK : K⊆B)
    (hl : q-1≤#K) (hp : 0<thetaJ q j G A B K)
    {x : V} (hx : x∈d.fragileRows) : #(d.neighbors x\K)≤3*h+j-7 := by
  have opt := strict_optimizer (G:=G) q A B K
  have hroot := d.fragile_in_optimizer opt hK hl hp hx
  have hi := d.optimizer_internal_min opt hK hl hp hroot
  have hs := d.positive_shape opt hK hl hp
  have hout := d.scar_nonneg (sdiff_subset : A\canonical q G A B K ⊆ A)
  dsimp only at hs
  have hd := (d.mem_fragile.mp hx).2
  have hsplit := dg_sdiff_add (G:=G) hK x
  have he : d.neighbors x\K=(B\K).filter (fun z => G.Adj x z) := by
    ext z
    simp only [mem_sdiff,mem_filter,neighbors]
    tauto
  rw [he]
  change dg G (B\K) x≤3*h+j-7
  have hh := d.parameters.height
  omega

open Classical in
lemma protected_residual_card {K : Finset V} (hK : K⊆B)
    (hl : q-1≤#K) (hp : 0<thetaJ q j G A B K) : #(d.protectedCols\K)≤(h-j)*(3*h+j-7) := by
  have he : d.protectedCols\K=d.fragileRows.biUnion (fun x => d.neighbors x\K) := by
    ext z
    simp only [protectedCols,mem_sdiff,mem_biUnion]
    tauto
  calc
    _ = #(d.fragileRows.biUnion (fun x => d.neighbors x\K)) := congrArg Finset.card he
    _ ≤ ∑ x∈d.fragileRows, #(d.neighbors x\K) := card_biUnion_le
    _ ≤ ∑ _x∈d.fragileRows, (3*h+j-7) :=
      sum_le_sum (fun x hx => d.neighbor_residual_card hK hl hp hx)
    _ = #d.fragileRows*(3*h+j-7) := by simp
    _ ≤ (h-j)*(3*h+j-7) := Nat.mul_le_mul_right _ d.fragile_card

open Classical in
omit [DecidableEq V] in
lemma protected_product_lt : (h-j)*(3*h+j-7)<4*h^2 := by
  have hh := d.parameters.height_int
  have hj := d.parameters.j_bounds
  have he : ((h-j : ℕ):ℤ)=(h:ℤ)-j := by omega
  have he' : ((3*h+j-7 : ℕ):ℤ)=3*(h:ℤ)+j-7 := by omega
  have hmul := mul_nonneg (show (0:ℤ)≤j by omega) (show (0:ℤ)≤3*h+j-7 by omega)
  have hmul' := mul_nonneg (show (0:ℤ)≤h by omega) (show (0:ℤ)≤h-j+7 by omega)
  zify
  rw [he,he']
  nlinarith

open Classical in
lemma protected_residual_lt {K : Finset V} (hK : K⊆B)
    (hl : q-1≤#K) (hp : 0<thetaJ q j G A B K) : #(d.protectedCols\K)<4*h^2 :=
  (d.protected_residual_card hK hl hp).trans_lt d.protected_product_lt

open Classical in
lemma protected_ban_card {K : Finset V} (hK : K⊆B)
    (hl : q-1≤#K) (hp : 0<thetaJ q j G A B K) : #(d.protectedCols\K)≤4*h^2 :=
  (d.protected_residual_lt hK hl hp).le

open Classical in
/-- Contraction restricts the SAME full original neighborhood union exactly. -/
lemma protected_contract (K P : Finset V) :
    (d.protectedCols\K)\P=d.protectedCols\(K∪P) := by
  ext v
  simp only [mem_sdiff,mem_union]
  tauto

open Classical in
/-- Paying all actual fragile quotas pays every original row quota. -/
lemma quota_all {O : Finset V} (hq : d.QuotaFeasible O) :
    ∀ x∈A, dg G O x≤dg G B x-q := by
  intro x hx
  by_cases hw : x∈d.fragileRows
  · exact hq.2.2 x hw
  · have hhigh : q+2*h-4≤dg G B x := by
      have hn : ¬dg G B x≤q+2*h-5 := fun hn => hw (d.mem_fragile.mpr ⟨hx,hn⟩)
      omega
    have hd := dg_le_card (G:=G) O x
    have hc := hq.2.1
    have hj := d.parameters.j_bounds
    have hh := d.parameters.height
    omega

open Classical in
/-- Exact padding remains within the SAME protected original residual carrier. -/
lemma allowed_residual_card {K : Finset V} (hK : K⊆B) (hl : q-1≤#K)
    (hp : 0<thetaJ q j G A B K) : j≤#((B\K)\d.protectedCols) := by
  have hR := d.positive_complement hK hp
  have hb := d.protected_ban_card hK hl hp
  have he : (B\K)\(d.protectedCols\K)=(B\K)\d.protectedCols := by
    ext z
    simp only [mem_sdiff]
    tauto
  have hc := card_sdiff_add_card_eq_card (sdiff_subset_sdiff_left K d.protected_subset)
  rw [he] at hc
  have hn := d.parameters.numeric
  have hj := d.parameters.j_bounds
  have hh := d.parameters.height_int
  have hquad : (4*h^2:ℕ)+j < q+1 := by
    zify
    nlinarith [sq_nonneg (h:ℤ)]
  omega

open Classical in
lemma quota_of_disjoint {O : Finset V} (hOB : O⊆B) (hOj : #O=j)
    (havoid : Disjoint O d.protectedCols) : d.QuotaFeasible O := by
  refine ⟨hOB,hOj,?_⟩
  intro x hx
  have hz : dg G O x=0 := by
    change #(O.filter (fun z => G.Adj x z))=0
    apply card_eq_zero.mpr
    apply filter_eq_empty_iff.mpr
    intro z hz hadj
    exact (disjoint_left.mp havoid hz) (d.mem_protected.mpr ⟨x,hx,hadj,hOB hz⟩)
  rw [hz]
  exact Nat.zero_le _

end Data
end Erdos585.AllHQuotaSurplus
