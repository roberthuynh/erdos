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
import AllHQuotaSurplus.Containment

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Finset SimpleGraph
noncomputable section
namespace Erdos585.AllHQuotaSurplus
open QB4 B5 L34 H3Unequal
open AllHNextNonstrict.TopEscape
open Resources Owners Containment
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace UniformEscape

open Classical in
def heavy (h q j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B K : Finset V) : Finset V :=
  (B\K).filter fun v => (q : ℤ)-((h : ℤ)-j-1) ≤ dg G (weakCore q G A B K) v

open Classical in
/-- The fixed heavy threshold leaves an actual original light column. -/
lemma light_exists {h q j s : ℕ} {A B K : Finset V}
    (d : Data h q j G A B) (hK : K ⊆ B) (hl : q-1 ≤ #K)
    (hp : thetaJ q j G A B K=2*(j : ℤ)+s-1)
    (ban : Finset V) (hban : #ban ≤ 4*h^2) :
    ∃ z ∈ B\K, z ∉ ban ∧ (dg G (weakCore q G A B K) z : ℤ) < (q : ℤ)-((h : ℤ)-j-1) := by
  classical
  let C := weakCore q G A B K
  let Z := heavy h q j G A B K
  have opt : Optimizer q G A B K C := weak_optimizer q A B K
  have hj := d.parameters.j_bounds
  have hh := d.parameters.height_int
  have hn := d.parameters.numeric
  have hs := d.positive_shape opt hK hl (show 0<thetaJ q j G A B K by omega)
  have hR := d.positive_complement hK (show 0<thetaJ q j G A B K by omega)
  have he := opt.outward_edges (j:=j) hK
  have hZ : Z ⊆ B\K := filter_subset _ _
  have hE := ec_mono_right (G:=G) C hZ
  have hout : ((q : ℤ)-((h : ℤ)-j-1))*#Z ≤ (ec G C Z : ℤ) := by
    rw [ec_comm,ec,Nat.cast_sum]
    calc
      _ = ∑ _v∈Z, ((q : ℤ)-((h : ℤ)-j-1)) := by rw [sum_const,nsmul_eq_mul];ring
      _ ≤ _ := sum_le_sum fun v hv => (mem_filter.mp hv).2
  have hcard : (#Z : ℤ) ≤ j+((#C : ℤ)-#K) := by
    by_contra! hb
    have hm := mul_le_mul_of_nonneg_left
      (show (j : ℤ)+((#C : ℤ)-#K)+1 ≤ #Z by omega)
      (show 0≤(q : ℤ)-((h : ℤ)-j-1) by omega)
    have hk : ((#C : ℤ)-#K) ≤ (h : ℤ)-1 := hs.2.2.2.1
    have hprod := mul_nonneg (show 0≤2*(h : ℤ)-1-(j+((#C : ℤ)-#K)+1) by omega)
      (show 0≤(h : ℤ)-j-1 by omega)
    have hprod' := mul_nonneg (show 0≤(h : ℤ)-2 by omega) (show 0≤2*(h : ℤ)-1 by omega)
    zify at hE
    nlinarith
  have hcard' : #Z ≤ 2*h-2 := by
    have hk : ((#C : ℤ)-#K) ≤ (h : ℤ)-1 := hs.2.2.2.1
    omega
  have hquad : 2*h+4*h^2 < q+1 := by
    zify
    nlinarith [sq_nonneg (h : ℤ)]
  have houtside : #(Z∪ban) < #(B\K) := by
    have hc := card_union_le Z ban
    omega
  obtain ⟨z,hz,hnot⟩ := PetalEscape.exists_outside (B\K) (Z∪ban) houtside
  refine ⟨z,hz,fun hb => hnot (mem_union_right _ hb),?_⟩
  by_contra! hb
  exact hnot (mem_union_left _ (mem_filter.mpr ⟨hz,hb⟩))

open Classical in
omit [DecidableEq V] in
lemma weakCore_mono {q : ℕ} {A B K T : Finset V} (hKT : K ⊆ T) :
    weakCore q G A B K ⊆ weakCore q G A B T := by
  classical
  intro v hv
  obtain ⟨hvA,hr⟩ := mem_filter.mp hv
  have hd := dg_mono (G:=G) hKT v
  apply mem_filter.mpr
  refine ⟨hvA,?_⟩
  unfold row at *
  omega

open Classical in
lemma exists_owner {q j s : ℕ} {A B K P : Finset V}
    (hP : P ⊆ B\K) (hne : P.Nonempty) (hc : extensionCost q j G A B K P ≤ s) :
    ∃ Q, P ⊆ Q ∧ Containment.Owner q j s G A B K Q := by
  classical
  let F := (B\K).powerset.filter fun Q => P ⊆ Q ∧ extensionCost q j G A B K Q ≤ s
  have hF : F.Nonempty := ⟨P,mem_filter.mpr ⟨mem_powerset.mpr hP,Subset.rfl,hc⟩⟩
  obtain ⟨Q,hQ,hmax⟩ := exists_max_image F Finset.card hF
  obtain ⟨hqr,hpq,hqc⟩ := mem_filter.mp hQ
  have hQr := mem_powerset.mp hqr
  refine ⟨Q,hpq,hQr,hne.mono hpq,hqc,?_⟩
  intro Z hZ hQZ hneQZ
  by_contra! hbad
  have hzF : Z ∈ F := mem_filter.mpr ⟨mem_powerset.mpr hZ,hpq.trans hQZ,by omega⟩
  have hle := hmax Z hzF
  have hlt : #Q < #Z := card_lt_card ⟨hQZ,fun hZQ => hneQZ (Subset.antisymm hQZ hZQ)⟩
  omega

open Classical in
/-- Select the actual least-cost big set and maximize its original column support. -/
lemma least_big {q j s H : ℕ} {A B K C : Finset V}
    (hex : ∃ P ⊆ B\K, extensionCost q j G A B K P ≤ s ∧ Big q H G A B K C P) :
    ∃ P ⊆ B\K, extensionCost q j G A B K P ≤ s ∧ Big q H G A B K C P ∧
      (∀ Z ⊆ B\K, Big q H G A B K C Z →
        extensionCost q j G A B K P ≤ extensionCost q j G A B K Z) ∧
      (∀ Z ⊆ B\K, P ⊆ Z → P ≠ Z →
        extensionCost q j G A B K P+1 ≤ extensionCost q j G A B K Z) := by
  classical
  let F := (B\K).powerset.filter fun P => Big q H G A B K C P
  have hF : F.Nonempty := by
    obtain ⟨P,hP,_,hb⟩ := hex
    exact ⟨P,mem_filter.mpr ⟨mem_powerset.mpr hP,hb⟩⟩
  obtain ⟨M,hMF,hmin⟩ := exists_min_image F (extensionCost q j G A B K) hF
  let E := F.filter fun P => extensionCost q j G A B K P=extensionCost q j G A B K M
  have hE : E.Nonempty := ⟨M,mem_filter.mpr ⟨hMF,rfl⟩⟩
  obtain ⟨P,hPE,hmax⟩ := exists_max_image E Finset.card hE
  obtain ⟨hPF,hcost⟩ := mem_filter.mp hPE
  obtain ⟨hpr,hbig⟩ := mem_filter.mp hPF
  have hP := mem_powerset.mp hpr
  have hleast : ∀ Z ⊆ B\K, Big q H G A B K C Z →
      extensionCost q j G A B K P ≤ extensionCost q j G A B K Z := by
    intro Z hZ hb
    rw [hcost]
    exact hmin Z (mem_filter.mpr ⟨mem_powerset.mpr hZ,hb⟩)
  have hc : extensionCost q j G A B K P ≤ s := by
    obtain ⟨Z,hZ,hc,hb⟩ := hex
    exact (hleast Z hZ hb).trans hc
  refine ⟨P,hP,hc,hbig,hleast,?_⟩
  intro Z hZ hPZ hne
  have hbZ : Big q H G A B K C Z := by
    obtain ⟨v,hv,ht⟩ := hbig
    exact ⟨v,residualRows_mono hPZ hv,ht⟩
  have hle := hleast Z hZ hbZ
  by_contra! hbad
  have he : extensionCost q j G A B K Z=extensionCost q j G A B K M := by omega
  have hZE : Z ∈ E := mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr hZ,hbZ⟩,he⟩
  have hcard := hmax Z hZE
  have hlt : #P < #Z := card_lt_card ⟨hPZ,fun hZP => hne (Subset.antisymm hPZ hZP)⟩
  omega


open Classical in
/-- The complete R254 arbitrary-ban uniform high-height escape, derived from the original graph. -/
theorem escape {h q j : ℕ} {A B : Finset V} (d : Data h q j G A B) :
    ∀ (s : ℕ) (K ban : Finset V), K ⊆ B → q-1 ≤ #K →
      thetaJ q j G A B K=2*(j : ℤ)+s-1 →
      (∀ T ⊆ B, K ⊆ T → K ≠ T → thetaJ q j G A B T ≤ thetaJ q j G A B K-1) →
      ban ⊆ B\K → #ban ≤ 4*h^2 →
      ∃ z ∈ B\K, z ∉ ban ∧ (dg G (weakCore q G A B K) z : ℤ) < (q : ℤ)-((h : ℤ)-j-1) ∧
        ∀ P ⊆ B\K, z ∈ P → (s : ℤ)+1 ≤ extensionCost q j G A B K P := by
  classical
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro K ban hK hl hp hstrict hban hbanCard
    let C := weakCore q G A B K
    have opt : Optimizer q G A B K C := weak_optimizer q A B K
    have hmin := strict_extension_cost_min hK hstrict
    by_cases hex : ∃ P ⊆ B\K, extensionCost q j G A B K P ≤ s ∧ Big q (h+j+s) G A B K C P
    · obtain ⟨P,hP,hcP,hbP,hleast,hPstrict⟩ := least_big hex
      have hcols := big_columns hP hbP
      have hneP : P.Nonempty := card_pos.mp (by omega)
      have hcostlo := hmin P hP hneP
      let t := (extensionCost q j G A B K P).toNat
      have ht : (t : ℤ)=extensionCost q j G A B K P := Int.toNat_of_nonneg (by omega)
      have htpos : 1 ≤ t := by omega
      have htupper : t ≤ s := by omega
      have hspos : 1 ≤ s := by omega
      have hnewK : K∪P ⊆ B := union_subset hK (hP.trans sdiff_subset)
      have hnewl : q-1 ≤ #(K∪P) := hl.trans (card_le_card subset_union_left)
      have hnewp : thetaJ q j G A B (K∪P)=2*(j : ℤ)+((s-t : ℕ) : ℤ)-1 := by
        have hc : thetaJ q j G A B K-thetaJ q j G A B (K∪P)=(t : ℤ) := by
          unfold extensionCost at ht
          omega
        rw [Nat.cast_sub htupper]
        omega
      have hnewstrict : ∀ T ⊆ B, K∪P ⊆ T → K∪P ≠ T →
          thetaJ q j G A B T ≤ thetaJ q j G A B (K∪P)-1 := by
        intro T hT hKT hne
        have hPT : P ⊆ T\K := by
          intro v hv
          exact mem_sdiff.mpr ⟨hKT (mem_union_right _ hv),(mem_sdiff.mp (hP hv)).2⟩
        have hKT' : K ⊆ T := subset_union_left.trans hKT
        have hneP' : P ≠ T\K := by
          intro he
          exact hne (by rw [he,union_sdiff_of_subset hKT'])
        have hc := hPstrict (T\K) (sdiff_subset_sdiff_left K hT) hPT hneP'
        unfold extensionCost at hc
        rw [union_sdiff_of_subset hKT'] at hc
        omega
      have hnewban : ban\P ⊆ B\(K∪P) := by
        intro v hv
        have hr := mem_sdiff.mp (hban (mem_sdiff.mp hv).1)
        exact mem_sdiff.mpr ⟨hr.1,fun hu => (mem_union.mp hu).elim hr.2 (mem_sdiff.mp hv).2⟩
      have hnewbanCard : #(ban\P) ≤ 4*h^2 :=
        (card_le_card sdiff_subset).trans hbanCard
      obtain ⟨z,hz,hnotban,hlight,hgain⟩ := ih (s-t) (by omega) (K∪P) (ban\P)
        hnewK hnewl hnewp hnewstrict hnewban hnewbanCard
      have hzP : z ∉ P := fun hv => (mem_sdiff.mp hz).2 (mem_union_right _ hv)
      have hzK : z ∉ K := fun hv => (mem_sdiff.mp hz).2 (mem_union_left _ hv)
      have hzR : z ∈ B\K := mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1,hzK⟩
      have hCmono := weakCore_mono (G:=G) (q:=q) (A:=A) (B:=B) (subset_union_left : K ⊆ K∪P)
      have hdeg := dg_mono (G:=G) hCmono z
      have hlightOld : (dg G C z : ℤ) < (q : ℤ)-((h : ℤ)-j-1) := by dsimp [C];omega
      refine ⟨z,hzR,fun hb => hnotban (mem_sdiff.mpr ⟨hb,hzP⟩),hlightOld,?_⟩
      intro Z hZ hzZ
      by_contra! hbad
      obtain ⟨Q,hZQ,hQ⟩ := exists_owner hZ ⟨z,hzZ⟩ (show extensionCost q j G A B K Z ≤ s by omega)
      have hzQ := hZQ hzZ
      by_cases hbQ : Big q (h+j+s) G A B K C Q
      · have hPQ := least_big_contained d hK hl hp hspos hmin hP hcP hbP hleast hQ hbQ
        have hQP : Q\P ⊆ B\(K∪P) := by
          intro v hv
          have hvR := mem_sdiff.mp (hQ.subset (mem_sdiff.mp hv).1)
          exact mem_sdiff.mpr ⟨hvR.1,fun hu => (mem_union.mp hu).elim hvR.2 (mem_sdiff.mp hv).2⟩
        have hc := hgain (Q\P) hQP (mem_sdiff.mpr ⟨hzQ,hzP⟩)
        have he := cost_contract (G:=G) (q:=q) (j:=j) (A:=A) (B:=B) (K:=K) (H:=P) (P:=Q\P)
        rw [union_sdiff_of_subset hPQ] at he
        have hqc := hQ.cost
        rw [Nat.cast_sub htupper] at hc
        omega
      · have hnb : ∀ v ∈ residualRows q G A B K C Q, -row q G B K v ≤ h+j+s := by
          intro v hv
          by_contra! ht'
          exact hbQ ⟨v,hv,ht'⟩
        have hh := nonbig_heavy d hK hl hp hmin hQ.subset hQ.cost hnb z hzQ
        omega
    · obtain ⟨z,hz,hnotban,hlight⟩ := light_exists d hK hl hp ban hbanCard
      refine ⟨z,hz,hnotban,hlight,?_⟩
      intro P hP hzP
      by_contra! hbad
      have hc : extensionCost q j G A B K P ≤ s := by omega
      have hnb : ∀ v ∈ residualRows q G A B K C P, -row q G B K v ≤ h+j+s := by
        intro v hv
        by_contra! ht
        exact hex ⟨P,hP,hc,v,hv,ht⟩
      have hh := nonbig_heavy d hK hl hp hmin hP hc hnb z hzP
      omega

end UniformEscape
end Erdos585.AllHQuotaSurplus
