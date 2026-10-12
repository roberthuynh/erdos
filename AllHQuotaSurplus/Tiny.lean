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
import AllHQuotaSurplus.Protection

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
omit [DecidableEq V] in
lemma theta_small_bound {T : Finset V} (hsize : #T≤q-2) :
    thetaJ q j G A B T≤(h:ℤ)*q-offset h+j-q*#T := by
  have hq := d.parameters.q_ge_height
  have hphi : ∀ a∈A, max 0 (row q G B T a)≤2*(q:ℤ)-2-dg G B a := by
    intro a ha
    have hd := dg_le_card (G:=G) T a
    have hc := d.capA_int ha
    unfold row
    omega
  have hsum : (∑ a∈A, max 0 (row q G B T a))≤
      (h:ℤ)*q-offset h-((q:ℤ)-1)*j := by
    calc
      _ ≤ deficiency (2*(q:ℤ)-2) G B A := sum_le_sum hphi
      _ = _ := d.deficient
  unfold thetaJ theta
  nlinarith

open Classical in
omit [DecidableEq V] in
lemma theta_intermediate {T : Finset V} (hlo : h≤#T) (hhi : #T≤q-2) :
    thetaJ q j G A B T≤(j:ℤ)-offset h := by
  have hh := d.theta_small_bound hhi
  have hp : 0≤(q:ℤ)*((#T:ℤ)-h) := mul_nonneg (Nat.cast_nonneg _) (by omega)
  nlinarith

open Classical in
omit [DecidableEq V] in
lemma theta_tiny_eq {T : Finset V} (htiny : #T<h) :
    thetaJ q j G A B T=(q:ℤ)*j-q*#T+
      ∑ v∈d.fragileRows, max 0 (row q G B T v) := by
  have he : (∑ v∈A, max 0 (row q G B T v))=
      ∑ v∈d.fragileRows, max 0 (row q G B T v) := by
    symm
    apply sum_subset d.fragile_subset
    intro v hv hn
    have hhigh : q+2*h-4≤dg G B v := by
      have hw : ¬dg G B v≤q+2*h-5 := fun hw => hn (d.mem_fragile.mpr ⟨hv,hw⟩)
      omega
    have hd := dg_le_card (G:=G) T v
    have hh := d.parameters.height
    apply max_eq_left
    unfold row
    omega
  unfold thetaJ theta
  rw [he]
  ring

open Classical in
/-- Every tiny height is globally bounded, without any below-h support floor. -/
lemma theta_tiny_le {T : Finset V} (htiny : #T<h) : thetaJ q j G A B T≤(q:ℤ)*j := by
  rw [d.theta_tiny_eq htiny]
  have hsum : (∑ v∈d.fragileRows, max 0 (row q G B T v))≤
      (#d.fragileRows:ℤ)*#T := by
    calc
      _ ≤ ∑ _v∈d.fragileRows, (#T:ℤ) := by
        apply sum_le_sum
        intro v hv
        have hd := dg_le_card (G:=G) T v
        have hm := d.minA v (d.fragile_subset hv)
        unfold row
        omega
      _ = _ := by simp [mul_comm]
  have hc : (#d.fragileRows:ℤ)≤(h:ℤ)-j := by have hh := d.fragile_card; have hj := d.parameters.j_bounds; omega
  have hp := mul_nonneg (show (0:ℤ)≤h-j-#d.fragileRows by omega) (Nat.cast_nonneg #T)
  have hq := d.parameters.q_ge_height
  have hqt := mul_nonneg (show (0:ℤ)≤q-(h-j) by omega) (Nat.cast_nonneg #T)
  nlinarith

open Classical in
/-- The SAME actual quota-feasible omission pays every tiny and intermediate test. -/
lemma small_good {O T : Finset V} (hquota : d.QuotaFeasible O) (hOT : O⊆T)
    (hsmall : #T≤q-2) : thetaJ q j G A B T≤0 := by
  have hOj := hquota.2.1
  have hjt : j≤#T := by rw [←hOj]; exact card_le_card hOT
  by_cases htiny : #T<h
  · have hsum : (∑ v∈d.fragileRows, max 0 (row q G B T v))≤
        (#d.fragileRows:ℤ)*((#T:ℤ)-j) := by
      calc
        _ ≤ ∑ _v∈d.fragileRows, ((#T:ℤ)-j) := by
          apply sum_le_sum
          intro v hv
          have hbudget := hquota.2.2 v hv
          have hd := dg_le_card (G:=G) (T\O) v
          have hs := dg_sdiff_add (G:=G) hOT v
          have hc := card_sdiff_add_card_eq_card hOT
          have hm := d.minA v (d.fragile_subset hv)
          unfold row
          omega
        _ = _ := by rw [sum_const,nsmul_eq_mul]
    have hc : (#d.fragileRows:ℤ)≤(h:ℤ)-j := by have hh := d.fragile_card; have hj := d.parameters.j_bounds; omega
    have hp := mul_nonneg (show (0:ℤ)≤h-j-#d.fragileRows by omega)
      (show (0:ℤ)≤(#T:ℤ)-j by omega)
    have hq := d.parameters.q_ge_height
    have hqt := mul_nonneg (show (0:ℤ)≤q-(h-j) by omega)
      (show (0:ℤ)≤(#T:ℤ)-j by omega)
    rw [d.theta_tiny_eq htiny]
    nlinarith
  · have ht := d.theta_intermediate (by omega) hsmall
    have hn := d.parameters.numeric
    have hj := d.parameters.j_bounds
    omega

open Classical in
omit [DecidableEq V] in
/-- All original cut payments force the quota on every actual fragile row. -/
lemma quota_of_cuts {O : Finset V} (hOB : O⊆B) (hOj : #O=j)
    (hcuts : ∀ T⊆B, O⊆T → thetaJ q j G A B T≤0) : d.QuotaFeasible O := by
  refine ⟨hOB,hOj,?_⟩
  have ht := hcuts O hOB Subset.rfl
  have hsum : (∑ v∈A, max 0 (row q G B O v))≤0 := by
    unfold thetaJ theta at ht
    rw [hOj] at ht
    nlinarith
  intro x hx
  have hi := single_le_sum (f:=fun v => max 0 (row q G B O v))
    (fun v _ => le_max_left _ _) (d.fragile_subset hx)
  have hm := d.minA x (d.fragile_subset hx)
  have hr : row q G B O x≤0 := (le_max_right _ _).trans (hi.trans hsum)
  unfold row at hr
  omega

end Data
end Erdos585.AllHQuotaSurplus
