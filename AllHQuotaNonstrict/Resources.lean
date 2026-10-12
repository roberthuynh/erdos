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
import AllHQuotaNonstrict.PetalEscape
import AllHNextNonstrict.TopEscape

/-! R280 actual original resources for the R265 full nonstrict uniform height band. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Finset SimpleGraph
noncomputable section
namespace Erdos585.AllHQuotaNonstrict
open QB4 B5 L34 H3Unequal
open AllHNextNonstrict.TopEscape
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace Resources

open Classical in
/-- The changed imbalance and original outside scar remain coupled. -/
lemma high_shape {h q j ξ s : ℕ} {A B K C : Finset V}
    (d : Data h q j ξ G A B) (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (hp : thetaJ q j G A B K = 2*(j : ℤ)+s-1) :
    let k : ℤ := (#C : ℤ)-#K
    let z : ℤ := k-j-s
    1 ≤ (h : ℤ)-k ∧ -1 ≤ z ∧
      z = coreDefect q G C K-((h : ℤ)*q-ξ)+
        deficiency (2*(q : ℤ)-2) G B (A\C)-1 := by
  classical
  have hj := d.parameters.j_pos
  have hs := d.positive_shape opt hK hl (by omega)
  have hn := d.scar_nonneg (sdiff_subset : A\C ⊆ A)
  dsimp only at hs ⊢
  omega

open Classical in
/-- Actual incoming original edges and scars have this exact joint bound. -/
lemma incoming_bound {h q j ξ : ℕ} {A B K C : Finset V}
    (d : Data h q j ξ G A B) (opt : Optimizer q G A B K C) (hK : K ⊆ B) :
    (ec G (A\C) K : ℤ)+deficiency (2*(q : ℤ)-2) G B (A\C) ≤
      ((h : ℤ)-((#C : ℤ)-#K))*q+j+2*((#C : ℤ)-#K)-
        thetaJ q j G A B K-ξ := by
  classical
  have hi := opt.cross_scar_identity (j:=j)
  have hs := d.scar_split opt.subset
  have hb : 0 ≤ deficiency (2*(q : ℤ)-2) G A K :=
    deficiency_nonneg _ fun v hv => d.capB_int (hK hv)
  nlinarith

open Classical in
def weakRows (q H : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K C : Finset V) : Finset V :=
  (A\C).filter fun v => -row q G B K v ≤ H

open Classical in
/-- Every weak original row consumes its incoming edges PLUS its full scar. -/
lemma weak_charge {q H : ℕ} {A B K C : Finset V} :
    ((q : ℤ)-2-H)*#(weakRows q H G A B K C) ≤
      (ec G (weakRows q H G A B K C) K : ℤ)+
        deficiency (2*(q : ℤ)-2) G B (weakRows q H G A B K C) := by
  classical
  rw [ec,Nat.cast_sum,deficiency,←sum_add_distrib]
  calc
    _ = ∑ _v ∈ weakRows q H G A B K C, ((q : ℤ)-2-H) := by
      rw [sum_const,nsmul_eq_mul];ring
    _ ≤ _ := by
      apply sum_le_sum
      intro v hv
      have hh := (mem_filter.mp hv).2
      unfold row at hh
      omega

open Classical in
/-- The weak-row count and original outside slack cannot be maximized independently. -/
lemma weak_slack_coupling {h q j ξ s : ℕ} {A B K C : Finset V}
    (d : Data h q j ξ G A B) (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (hp : thetaJ q j G A B K = 2*(j : ℤ)+s-1) :
    let k : ℤ := (#C : ℤ)-#K
    let u : ℤ := #(weakRows q (h+j+s) G A B K C)
    u ≤ (h : ℤ)-k-1 ∧ u+(k-j-s) ≤ (h : ℤ)-j-s-1 := by
  classical
  have hs := high_shape d opt hK hl hp
  have hinc := incoming_bound d opt hK
  let W := weakRows q (h+j+s) G A B K C
  have hW : W ⊆ A\C := filter_subset _ _
  have hch := weak_charge (G:=G) (q:=q) (H:=h+j+s) (A:=A) (B:=B) (K:=K) (C:=C)
  have he : ec G W K ≤ ec G (A\C) K := by
    rw [ec_comm (G:=G) W K,ec_comm (G:=G) (A\C) K]
    exact ec_mono_right (G:=G) K hW
  have hscar := deficiency_le_subset (2*(q : ℤ)-2) hW
    (fun v hv => d.capA_int (mem_sdiff.mp hv).1)
  have hh := d.parameters.height_int
  have hj := d.parameters.j_bounds
  have hn := d.parameters.numeric
  have ha : (h : ℤ)^2+3*h+8 ≤ ξ := by exact_mod_cast d.parameters.lower
  let k : ℤ := (#C : ℤ)-#K
  let t : ℤ := h-k
  have ht : 1 ≤ t := hs.1
  have htz : t ≤ (h : ℤ)-j-s+1 := by dsimp [t,k];dsimp only at hs;omega
  have hH : 0 ≤ (h : ℤ)+j+s := by omega
  have hqH : 0 < (q : ℤ)-2-(h+j+s) := by omega
  have hbound : (h : ℤ)-k-1 ≥ #W := by
    by_contra! hbad
    have hu : t ≤ (#W : ℤ) := by dsimp [t];omega
    have hm := mul_le_mul_of_nonneg_left hu (le_of_lt hqH)
    have htH := mul_le_mul_of_nonneg_right htz hH
    change ((q : ℤ)-2-(h+j+s))*#W ≤ _ at hch
    zify at he
    dsimp only [k,t] at *
    nlinarith
  dsimp only
  change (#W : ℤ) ≤ (h : ℤ)-k-1 ∧ (#W : ℤ)+(k-j-s) ≤ (h : ℤ)-j-s-1
  omega

open Classical in
/-- Every actual expansion below the current height has the literal imbalance bounds. -/
lemma eta_bounds {h q j ξ : ℕ} {A B K C P : Finset V}
    (d : Data h q j ξ G A B) (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hl : q-1 ≤ #K) (hP : P ⊆ B\K)
    (hc : extensionCost q j G A B K P < thetaJ q j G A B K) :
    ((#C : ℤ)-#K)-(h : ℤ)+1 ≤ (#P : ℤ)-#(residualRows q G A B K C P) ∧
      (#P : ℤ)-#(residualRows q G A B K C P) ≤
        j+((#C : ℤ)-#K)-thetaJ q j G A B K+extensionCost q j G A B K P := by
  classical
  let J := residualRows q G A B K C P
  have hJ : J ⊆ A\C := filter_subset _ _
  have hdC : Disjoint C J := disjoint_left.mpr fun v hv hj => (mem_sdiff.mp (hJ hj)).2 hv
  have hdK : Disjoint K P := disjoint_left.mpr fun v hv hp => (mem_sdiff.mp (hP hp)).2 hv
  have hxp : 0 < thetaJ q j G A B (K∪P) := by unfold extensionCost at hc;omega
  have hs := d.positive_shape (expanded_optimizer opt hP)
    (union_subset hK (hP.trans sdiff_subset)) (hl.trans (card_le_card subset_union_left)) hxp
  have hcc := card_union_of_disjoint hdC
  have hcp := card_union_of_disjoint hdK
  have hn := d.scar_nonneg (sdiff_subset : A\(C∪J) ⊆ A)
  dsimp only at hs
  change _ ≤ (#P : ℤ)-#J ∧ (#P : ℤ)-#J ≤ _
  zify at hcc hcp
  unfold extensionCost
  dsimp only [J] at hcc hcp hn ⊢
  omega

open Classical in
/-- Original singleton positivity bounds outgoing edges on every repeated column. -/
lemma repeated_outgoing {q j : ℕ} {A B K C P : Finset V}
    (opt : Optimizer q G A B K C)
    (hmin : ∀ P ⊆ B\K, P.Nonempty → 1 ≤ extensionCost q j G A B K P)
    (hP : P ⊆ B\K) : (ec G C P : ℤ) ≤ ((q : ℤ)-1)*#P := by
  classical
  rw [ec_comm,ec,Nat.cast_sum]
  calc
    _ ≤ ∑ _v∈P, ((q : ℤ)-1) := by
      apply sum_le_sum
      intro v hv
      have hh := singleton_weight_pos opt hmin (hP hv)
      omega
    _ = _ := by rw [sum_const,nsmul_eq_mul];ring

end Resources
end Erdos585.AllHQuotaNonstrict
