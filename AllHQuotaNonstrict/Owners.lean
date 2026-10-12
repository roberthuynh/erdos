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
import AllHQuotaNonstrict.Resources

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Finset SimpleGraph
noncomputable section
namespace Erdos585.AllHQuotaNonstrict
open QB4 B5 L34 H3Unequal
open AllHNextNonstrict.TopEscape
open Resources
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace Owners

open Classical in
/-- Every shared strict original row is paid by the exact original convex gap. -/
lemma shared_threshold {q j : ℕ} {A B K C P Q : Finset V}
    (hP : P⊆B\K) {v : V}
    (hvP : v∈residualRows q G A B K C P)
    (hvQ : v∈residualRows q G A B K C Q) :
    -row q G B K v≤(dg G (P∩Q) v : ℤ)+
      (extensionCost q j G A B K P+extensionCost q j G A B K Q-
        extensionCost q j G A B K (P∪Q)-extensionCost q j G A B K (P∩Q)) := by
  classical
  have hvA := (mem_sdiff.mp (mem_filter.mp hvP).1).1
  have hvcan : v∈canonical q G A B (K∪P)∩canonical q G A B (K∪Q) :=
    mem_inter.mpr ⟨mem_filter.mpr ⟨hvA,(mem_filter.mp hvP).2⟩,
      mem_filter.mpr ⟨hvA,(mem_filter.mp hvQ).2⟩⟩
  have hi : (K∪P)∩(K∪Q)=K∪(P∩Q) := (union_inter_distrib_left K P Q).symm
  have hu : (K∪P)∪(K∪Q)=K∪(P∪Q) := by ext w; simp only [mem_union]; tauto
  have hb := bonus_shared (G:=G) q hvcan
  rw [hi] at hb
  have hdis : Disjoint K (P∩Q) := disjoint_left.mpr fun w hwK hwI =>
    (mem_sdiff.mp (hP (mem_inter.mp hwI).1)).2 hwK
  have hd := dg_union_of_disjoint (G:=G) hdis v
  have hsum : bonus q G B (K∪P) (K∪Q) v≤∑ w∈A, bonus q G B (K∪P) (K∪Q) w :=
    single_le_sum (fun w _ => bonus_nonneg q B (K∪P) (K∪Q) w) hvA
  have hid := bonus_sum (G:=G) q A B (K∪P) (K∪Q)
  rw [hi,hu] at hid
  have hmax := le_max_right (0 : ℤ) ((dg G B v : ℤ)-q-dg G (K∪(P∩Q)) v)
  rw [←hb] at hmax
  unfold row extensionCost thetaJ
  zify at hd
  linarith


open Classical in
/-- Big owners retain more than h original columns after deleting any shared rows. -/
lemma big_columns {h q j s : ℕ} {A B K C P : Finset V}
    (hP : P ⊆ B\K)
    (hbig : ∃ v ∈ residualRows q G A B K C P, (h+j+s : ℤ) < -row q G B K v) :
    h+j+s+2 ≤ #P := by
  classical
  obtain ⟨v,hv,ht⟩ := hbig
  have hr := (mem_filter.mp hv).2
  rw [residual_row_add q hP v] at hr
  have hd := dg_le_card (G:=G) P v
  omega

open Classical in
/-- Delete ALL repeated rows, with literal original proper-support guards. -/
lemma charge_delete {h q j ξ : ℕ} {A B K C P Y : Finset V}
    (d : Data h q j ξ G A B) (opt : Optimizer q G A B K C)
    (hK : K ⊆ B) (hl : q-1 ≤ #K) (hP : P ⊆ B\K)
    (hlarge : h ≤ #P) (hY : Y ⊆ residualRows q G A B K C P) :
    (h : ℤ)*q-ξ-extensionCost q j G A B K P+
      ((#P : ℤ)-#(residualRows q G A B K C P))+
      ((q : ℤ)-1)*#Y-ec G Y P ≤ petalWeight q G A B K C P := by
  classical
  let J := residualRows q G A B K C P
  have hJ : J ⊆ A := (filter_subset _ _).trans sdiff_subset
  have hpc := card_le_card hP
  have hkc := card_sdiff_add_card_eq_card hK
  have hjc := card_le_card (sdiff_subset : J\Y ⊆ J)
  have hja := card_le_card hJ
  have hq := d.parameters.q_ge_height
  have hf := d.sparse (J\Y) (sdiff_subset.trans hJ) P (hP.trans sdiff_subset)
    (by omega) (by omega)
  have hh := twice_coreDefect (G:=G) q (J\Y) P
  have hi := petal_resource_identity (j:=j) opt hP
  dsimp only at hi
  change coreDefect q G J P=petalWeight q G A B K C P+
    extensionCost q j G A B K P-((#P : ℤ)-#J) at hi
  have hc := card_sdiff_add_card_eq_card hY
  have he := ec_sdiff_add_left (G:=G) hY P
  unfold coreDefect at hi hh
  zify at hc he
  dsimp only [J] at hf hh hi hc he ⊢
  nlinarith

open Classical in
/-- Both original charges use one pool, with every repeated unit explicit. -/
lemma pair_pool {h q j ξ : ℕ} {A B K C P Q : Finset V}
    (d : Data h q j ξ G A B) (hP : P ⊆ B\K) (hQ : Q ⊆ B\K) :
    let Y := residualRows q G A B K C P ∩ residualRows q G A B K C Q
    petalWeight q G A B K C P+petalWeight q G A B K C Q ≤
      (ec G C (B\K) : ℤ)+ec G (A\C) K+deficiency (2*(q : ℤ)-2) G B (A\C)+
      ec G C (P∩Q)+ec G Y K+deficiency (2*(q : ℤ)-2) G B Y := by
  classical
  dsimp only
  let JP := residualRows q G A B K C P
  let JQ := residualRows q G A B K C Q
  have hJP : JP ⊆ A\C := filter_subset _ _
  have hJQ : JQ ⊆ A\C := filter_subset _ _
  have he := ec_modular (G:=G) C P Q
  have hi := ec_modular (G:=G) K JP JQ
  have hs : deficiency (2*(q : ℤ)-2) G B (JP∪JQ)+
      deficiency (2*(q : ℤ)-2) G B (JP∩JQ)=
      deficiency (2*(q : ℤ)-2) G B JP+deficiency (2*(q : ℤ)-2) G B JQ := sum_union_inter
  have hE := ec_mono_right (G:=G) C (union_subset hP hQ)
  have hI := ec_mono_right (G:=G) K (union_subset hJP hJQ)
  have hscar := deficiency_le_subset (2*(q : ℤ)-2) (union_subset hJP hJQ)
    (fun v hv => d.capA_int (mem_sdiff.mp hv).1)
  simp only [ec_comm (G:=G) K] at hi hI
  unfold petalWeight
  zify at he hi hE hI
  dsimp only [JP,JQ] at *
  linarith

open Classical in
/-- Literal rowwise identity pays repeated incoming units and scars in full. -/
lemma repeated_row_refund {q : ℕ} {B K P Q : Finset V}
    (hK : K ⊆ B) (hPQ : P∪Q ⊆ B\K) (v : V) :
    (2*((q : ℤ)-1)-dg G P v-dg G Q v)-dg G K v-
      (2*(q : ℤ)-2-dg G B v) ≥ -(dg G (P∩Q) v : ℤ) := by
  classical
  have hd := dg_union_add_dg_inter (G:=G) P Q v
  have hm := dg_mono (G:=G) hPQ v
  have hs := dg_sdiff_add (G:=G) hK v
  zify at hd hm hs
  linarith

open Classical in
/-- The sum of ALL repeated original row units is paid, with no weak-row choice. -/
lemma repeated_refund {q : ℕ} {B K P Q Y : Finset V}
    (hK : K ⊆ B) (hP : P ⊆ B\K) (hQ : Q ⊆ B\K) :
    2*((q : ℤ)-1)*#Y-ec G Y P-ec G Y Q-ec G Y K-
      deficiency (2*(q : ℤ)-2) G B Y ≥ -(ec G Y (P∩Q) : ℤ) := by
  classical
  have hs := sum_le_sum (s:=Y) (fun v _ => repeated_row_refund (G:=G) (q:=q) hK (union_subset hP hQ) v)
  simp only [ec,Nat.cast_sum,deficiency] at *
  simp only [sum_sub_distrib,sum_neg_distrib,sum_const,nsmul_eq_mul] at *
  nlinarith


open Classical in
/-- Deleting one actual column loses at most one unit per actual strict row. -/
lemma deletion_marginal {q j : ℕ} {A B K C P : Finset V}
    (opt : Optimizer q G A B K C) (hP : P ⊆ B\K) {v : V} (hv : v ∈ P) :
    (q : ℤ)-dg G C v ≤ extensionCost q j G A B K P-
      extensionCost q j G A B K (P.erase v)+#(residualRows q G A B K C P) := by
  classical
  let f := fun a => max 0 (row q G B K a+dg G P a)
  let g := fun a => max 0 (row q G B K a+dg G (P.erase v) a)
  have hsplit : ∀ a, dg G (P.erase v) a+dg G {v} a=dg G P a := by
    intro a
    have hd : Disjoint (P.erase v) {v} := disjoint_singleton_right.mpr (notMem_erase _ _)
    have hset : P.erase v ∪ {v}=P := by
      ext w
      simp only [mem_union,mem_erase,mem_singleton]
      constructor
      · rintro (⟨_,hw⟩|rfl)
        · exact hw
        · exact hv
      · intro hw
        by_cases he : w=v
        · exact Or.inr he
        · exact Or.inl ⟨he,hw⟩
    simpa only [hset] using (dg_union_of_disjoint (G:=G) hd a).symm
  have hsum : (∑ a∈A\C, (f a-g a)) ≤ #(residualRows q G A B K C P) := by
    calc
      _ ≤ ∑ a∈A\C, if 0 < row q G B (K∪P) a then (1 : ℤ) else 0 := by
        apply sum_le_sum
        intro a _
        have hd := hsplit a
        have h1 := dg_le_card (G:=G) ({v} : Finset V) a
        simp only [card_singleton] at h1
        have hrow := residual_row_add (G:=G) q hP a
        dsimp [f,g]
        split_ifs with hh <;> omega
      _ = _ := by
        simp only [residualRows,card_eq_sum_ones,sum_filter,Nat.cast_sum,
          Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hu := extensionCost_units (j:=j) opt hP
  have he := extensionCost_units (j:=j) opt ((erase_subset v P).trans hP)
  have hcard : #(P.erase v)+1=#P := by rw [card_erase_of_mem hv];have hh:=card_pos.mpr ⟨v,hv⟩;omega
  have hne : 0<#P := card_pos.mpr ⟨v,hv⟩
  have hec : ec G C (P.erase v)+dg G C v=ec G C P := by
    rw [ec_comm (G:=G) C (P.erase v),ec_comm (G:=G) C P,ec,ec]
    exact sum_erase_add P (fun w => dg G C w) hv
  rw [sum_sub_distrib] at hsum
  zify at hcard hec
  dsimp only [f,g] at hsum
  nlinarith

open Classical in
/-- ALL nonbig bad sets are covered by the one fixed heavy-column family. -/
lemma nonbig_heavy {h q j ξ s : ℕ} {A B K P : Finset V}
    (d : Data h q j ξ G A B) (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (hp : thetaJ q j G A B K=2*(j : ℤ)+s-1)
    (hmin : ∀ P ⊆ B\K, P.Nonempty → 1 ≤ extensionCost q j G A B K P)
    (hP : P ⊆ B\K) (hc : extensionCost q j G A B K P ≤ s)
    (hnb : ∀ v ∈ residualRows q G A B K (weakCore q G A B K) P,
      -row q G B K v ≤ h+j+s) :
    ∀ v ∈ P, (q : ℤ)-dg G (weakCore q G A B K) v ≤ (h : ℤ)-j := by
  classical
  let C := weakCore q G A B K
  have opt : Optimizer q G A B K C := weak_optimizer q A B K
  have hs := weak_slack_coupling d opt hK hl hp
  have hJ : residualRows q G A B K C P ⊆ weakRows q (h+j+s) G A B K C := by
    intro v hv
    exact mem_filter.mpr ⟨(mem_filter.mp hv).1,hnb v hv⟩
  have hjc := card_le_card hJ
  have hshape := high_shape d opt hK hl hp
  intro v hv
  by_cases he : P={v}
  · have hrows : residualRows q G A B K C {v}=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      have hh := weak_outside_strict (G:=G) q A B K (mem_filter.mp ha).1
      have hp' := (mem_filter.mp ha).2
      rw [residual_row_add q (singleton_subset_iff.mpr (hP hv)) a] at hp'
      have hd := dg_le_card (G:=G) ({v} : Finset V) a
      simp only [card_singleton] at hd
      omega
    have hu := extensionCost_linear_of_no_rows (j:=j) opt
      (singleton_subset_iff.mpr (hP hv)) hrows
    have hec : ec G C {v}=dg G C v := by rw [ec_comm];simp [ec]
    rw [he] at hc
    simp only [card_singleton,Nat.cast_one,mul_one,hec] at hu
    dsimp only at hs hshape
    change (q : ℤ)-dg G C v ≤ _
    omega
  · have hne : (P.erase v).Nonempty := by
      by_contra hn
      have hz := not_nonempty_iff_eq_empty.mp hn
      apply he
      ext w
      simp only [mem_singleton]
      constructor
      · intro hw
        by_contra hwv
        have hh : w ∈ P.erase v := mem_erase.mpr ⟨hwv,hw⟩
        rw [hz] at hh
        exact notMem_empty _ hh
      · rintro rfl
        exact hv
    have hm := hmin (P.erase v) ((erase_subset _ _).trans hP) hne
    have hd := deletion_marginal (j:=j) opt hP hv
    dsimp only at hs hshape
    change (q : ℤ)-dg G C v ≤ _
    omega

end Owners
end Erdos585.AllHQuotaNonstrict
