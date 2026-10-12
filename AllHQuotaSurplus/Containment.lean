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
import AllHQuotaSurplus.Owners

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Finset SimpleGraph
noncomputable section
namespace Erdos585.AllHQuotaSurplus
open QB4 B5 L34 H3Unequal
open AllHNextNonstrict.TopEscape
open Resources Owners
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace Containment

open Classical in
def Big (q H : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K C P : Finset V) : Prop :=
  ∃ v ∈ residualRows q G A B K C P, (H : ℤ) < -row q G B K v

open Classical in
/-- Actual maximal original sets of cost at most s. -/
structure Owner (q j s : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K P : Finset V) : Prop where
  subset : P ⊆ B\K
  nonempty : P.Nonempty
  cost : extensionCost q j G A B K P ≤ s
  strict : ∀ Q ⊆ B\K, P ⊆ Q → P ≠ Q → (s : ℤ)+1 ≤ extensionCost q j G A B K Q

open Classical in
/-- Original weak/slack coupling bounds the actual low-cost intersection. -/
lemma intersection_small {h q j s : ℕ} {A B K P Q : Finset V}
    (d : Data h q j G A B) (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (hp : thetaJ q j G A B K=2*(j : ℤ)+s-1) (hs : 1 ≤ s)
    (hP : P ⊆ B\K) (hcP : extensionCost q j G A B K P ≤ s)
    (hQ : Owner q j s G A B K Q) (hn : ¬P ⊆ Q)
    (hminimal : ∀ Z ⊆ B\K, Big q (h+j+s) G A B K (weakCore q G A B K) Z →
      extensionCost q j G A B K P ≤ extensionCost q j G A B K Z) :
    #(P∩Q) ≤ h-j-2 ∧
      extensionCost q j G A B K (P∩Q) ≤ extensionCost q j G A B K P-1 := by
  classical
  let C := weakCore q G A B K
  let I := P∩Q
  have opt : Optimizer q G A B K C := weak_optimizer q A B K
  have hI : I ⊆ B\K := inter_subset_left.trans hP
  have hneU : Q ≠ P∪Q := by
    intro he
    exact hn (he ▸ subset_union_left)
  have hU := hQ.strict (P∪Q) (union_subset hP hQ.subset) subset_union_right hneU
  have hsub := extensionCost_submod (G:=G) q j A B K P Q
  have hQi := hQ.cost
  have hell : extensionCost q j G A B K I ≤ extensionCost q j G A B K P-1 := by
    dsimp [I];omega
  have hj := d.parameters.j_bounds
  have hshape := high_shape d opt hK hl hp
  have hcouple := weak_slack_coupling d opt hK hl hp
  have hIcard : (#I : ℤ) ≤ (h : ℤ)-j-2 := by
    by_cases he : I=∅
    · simp only [he,card_empty,Nat.cast_zero]
      dsimp only at hshape
      omega
    · have hnb : ¬Big q (h+j+s) G A B K C I := by
        intro hb
        have hh := hminimal I hI hb
        omega
      have hrows : residualRows q G A B K C I ⊆ weakRows q (h+j+s) G A B K C := by
        intro v hv
        apply mem_filter.mpr
        refine ⟨(mem_filter.mp hv).1,?_⟩
        by_contra! ht
        exact hnb ⟨v,hv,ht⟩
      have hrc := card_le_card hrows
      have heta := eta_bounds d opt hK hl hI (show extensionCost q j G A B K I < thetaJ q j G A B K by omega)
      dsimp only at hshape hcouple
      omega
  have hnat : #(P∩Q) ≤ h-j-2 := by dsimp [I] at hIcard;omega
  exact ⟨hnat,hell⟩

open Classical in
/-- All actual shared strict rows are weak, including empty intersections. -/
lemma shared_weak {h q j s : ℕ} {A B K P Q : Finset V}
    (hP : P ⊆ B\K) (_hs : 1 ≤ s)
    (hcP : extensionCost q j G A B K P ≤ s) (hQ : Owner q j s G A B K Q)
    (hn : ¬P ⊆ Q) (hI : #(P∩Q) ≤ h-j-2)
    (_hell : extensionCost q j G A B K (P∩Q) ≤ extensionCost q j G A B K P-1)
    (hmin : ∀ Z ⊆ B\K, Z.Nonempty → 1 ≤ extensionCost q j G A B K Z) :
    residualRows q G A B K (weakCore q G A B K) P ∩
      residualRows q G A B K (weakCore q G A B K) Q ⊆
      weakRows q (h+j+s) G A B K (weakCore q G A B K) := by
  classical
  have hneU : Q ≠ P∪Q := by intro he;exact hn (he ▸ subset_union_left)
  have hU := hQ.strict (P∪Q) (union_subset hP hQ.subset) subset_union_right hneU
  have hIn := cost_nonneg (G:=G) hmin (inter_subset_left.trans hP : P∩Q ⊆ B\K)
  intro v hv
  obtain ⟨hvP,hvQ⟩ := mem_inter.mp hv
  have ht := shared_threshold (j:=j) hP hvP hvQ
  have hd := dg_le_card (G:=G) (P∩Q) v
  have hcQ := hQ.cost
  refine mem_filter.mpr ⟨(mem_filter.mp hvP).1,?_⟩
  omega

open Classical in
/-- Every maximal big low-cost owner contains the least-cost big original owner. -/
lemma least_big_contained {h q j s : ℕ} {A B K P Q : Finset V}
    (d : Data h q j G A B) (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (hp : thetaJ q j G A B K=2*(j : ℤ)+s-1) (hs : 1 ≤ s)
    (hmin : ∀ Z ⊆ B\K, Z.Nonempty → 1 ≤ extensionCost q j G A B K Z)
    (hP : P ⊆ B\K) (hcP : extensionCost q j G A B K P ≤ s)
    (hbP : Big q (h+j+s) G A B K (weakCore q G A B K) P)
    (hminimal : ∀ Z ⊆ B\K, Big q (h+j+s) G A B K (weakCore q G A B K) Z →
      extensionCost q j G A B K P ≤ extensionCost q j G A B K Z)
    (hQ : Owner q j s G A B K Q)
    (hbQ : Big q (h+j+s) G A B K (weakCore q G A B K) Q) : P ⊆ Q := by
  classical
  by_contra hn
  let C := weakCore q G A B K
  let Y := residualRows q G A B K C P ∩ residualRows q G A B K C Q
  let I := P∩Q
  let k : ℤ := (#C : ℤ)-#K
  let u : ℤ := #(weakRows q (h+j+s) G A B K C)
  let i : ℤ := #I
  have opt : Optimizer q G A B K C := weak_optimizer q A B K
  have hsmall := intersection_small d hK hl hp hs hP hcP hQ hn hminimal
  have hweak := shared_weak hP hs hcP hQ hn hsmall.1 hsmall.2 hmin
  have hYc : (#Y : ℤ) ≤ u := by
    dsimp [Y,u,C]
    exact_mod_cast card_le_card hweak
  have hcp := big_columns hP hbP
  have hcq := big_columns hQ.subset hbQ
  have hpcharge := charge_delete d opt hK hl hP (by omega) (inter_subset_left : Y ⊆ _)
  have hqcharge := charge_delete d opt hK hl hQ.subset (by omega) (inter_subset_right : Y ⊆ _)
  have hpool := Owners.pair_pool (C:=C) d hP hQ.subset
  have hrefund := repeated_refund (G:=G) (q:=q) (Y:=Y) hK hP hQ.subset
  have hbudget := PetalEscape.pool_bound d opt hK
  have heI := repeated_outgoing opt hmin (inter_subset_left.trans hP : I ⊆ B\K)
  have hetaP := eta_bounds d opt hK hl hP (show extensionCost q j G A B K P < thetaJ q j G A B K by have hj:=d.parameters.j_pos;omega)
  have hetaQ := eta_bounds d opt hK hl hQ.subset (show extensionCost q j G A B K Q < thetaJ q j G A B K by have hj:=d.parameters.j_pos;have hc:=hQ.cost;omega)
  have hYI : (ec G Y I : ℤ) ≤ i*u := by
    have hsimple : (ec G Y I : ℤ) ≤ (#Y : ℤ)*#I := by
      rw [ec,Nat.cast_sum]
      calc
        _ ≤ ∑ _v∈Y, (#I : ℤ) := sum_le_sum fun v _ => by exact_mod_cast dg_le_card (G:=G) I v
        _ = _ := by rw [sum_const,nsmul_eq_mul]
    have hi0 : 0 ≤ i := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left hYc hi0
    dsimp [i] at hm
    nlinarith
  have hshape := high_shape d opt hK hl hp
  have hcouple := weak_slack_coupling d opt hK hl hp
  have hqc := hQ.cost
  have hh := d.parameters.height_int
  have hj := d.parameters.j_bounds
  have hnum := d.parameters.numeric
  have ha := offset_cast h
  have hi : 0 ≤ i ∧ i ≤ (h : ℤ)-j-2 := by
    dsimp [i,I]
    constructor
    · positivity
    · have hbound := hsmall.1
      have hs' : (j : ℤ)+s ≤ h-1 := by dsimp only at hshape;omega
      omega
  have hu : 0 ≤ u ∧ u ≤ (h : ℤ)-2 := by
    dsimp only at hshape hcouple
    dsimp [u,k,C] at *
    constructor
    · positivity
    · omega
  have hiu : i*u ≤ (h : ℤ)^2 := by
    have hm := mul_nonneg (show 0≤(h : ℤ)-i by omega) (show 0≤u by omega)
    have hn := mul_nonneg (show 0≤(h : ℤ)-u by omega) (show 0≤(h : ℤ) by omega)
    nlinarith
  have hiq : 2*(q : ℤ) ≤ ((h : ℤ)-j-i)*q := by
    have hm := mul_nonneg (show 0≤(h : ℤ)-j-i-2 by omega) (Nat.cast_nonneg q : (0 : ℤ)≤q)
    nlinarith
  dsimp only at hpool
  dsimp only [Y,I,k,i,u] at *
  nlinarith

end Containment
end Erdos585.AllHQuotaSurplus
