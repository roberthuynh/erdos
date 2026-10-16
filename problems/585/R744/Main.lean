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
import AllHQuotaNonstrict.Caller
import AllHThirdQuotaFailure.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.R744
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {q a : ℕ} {A B : Finset V}

abbrev Host (q a : ℕ) (G : SimpleGraph V) (A B : Finset V) :=
  AllHQuotaNonstrict.Host 4 q 1 a G A B

open Classical in
def lowRows (q : ℕ) (G : SimpleGraph V) (A : Finset V) : Finset V :=
  A.filter (fun x => G.degree x = q)

open Classical in
lemma lowRows_card (host : Host q a G A B) (ha : a = 42 ∨ a = 43) :
    #(lowRows q G A) ≤ 2 := by
  classical
  let L := lowRows q G A
  have hLA : L ⊆ A := filter_subset _ _
  have hq : 25600 ≤ q := host.parameters.large
  have hd := host.to_data
  have hcap : ∀ x ∈ A, (dg G B x : ℤ) ≤ 2*(q:ℤ)-2 := by
    intro x hx
    have hc := hd.capA x hx
    have he : (2*q-2:ℕ)+2=2*q := by omega
    zify at hc he
    omega
  have hle := deficiency_le_subset (G:=G) (2*(q:ℤ)-2) hLA hcap
  have hl : deficiency (2*(q:ℤ)-2) G B L = ((q:ℤ)-2)*#L := by
    unfold deficiency
    calc (∑ x ∈ L, (2*(q:ℤ)-2-(dg G B x:ℤ))) = ∑ _x ∈ L, ((q:ℤ)-2) := by
          apply sum_congr rfl
          intro x hx
          have hm := mem_filter.mp hx
          have he : dg G B x=q := (dg_eq_degree host.bipartite hm.1).trans hm.2
          rw [he]
          ring
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
  rw [hl,hd.deficient] at hle
  norm_num at hle
  by_contra! hn
  have hn' : (3:ℤ)≤#L := by exact_mod_cast hn
  have hp := mul_le_mul_of_nonneg_left hn' (show (0:ℤ)≤q-2 by omega)
  change #L>2 at hn
  rcases ha with rfl | rfl <;> norm_num at hle <;> nlinarith

open Classical in
lemma singleton_quota (host : Host q a G A B) {b : V} (hb : b∈B)
    (havoid : ∀ x∈lowRows q G A, ¬G.Adj x b) :
    ∃ O0 : Finset V, O0⊆B ∧ #O0=1 ∧ ∀ x∈A,
      G.degree x≤q+3 → dg G O0 x≤G.degree x-q := by
  classical
  refine ⟨{b},singleton_subset_iff.mpr hb,card_singleton _,?_⟩
  intro x hx _
  have hd := host.min_degree x
  by_cases he : G.degree x=q
  · have hn := havoid x (mem_filter.mpr ⟨hx,he⟩)
    simp [dg,hn,he]
  · have hc := dg_le_card (G:=G) ({b}:Finset V) x
    simp only [card_singleton] at hc
    omega

open Classical in
lemma failed_shore (host : Host q a G A B) (ha : a = 42 ∨ a = 43)
    (hf : ¬∃ O0 : Finset V, O0⊆B ∧ #O0=1 ∧ ∀ x∈A,
      G.degree x≤q+3 → dg G O0 x≤G.degree x-q) : #A < 2*q := by
  classical
  let L := lowRows q G A
  have hl := lowRows_card host ha
  have hcover : ∀ b∈B, ∃ x∈L, G.Adj x b := by
    intro b hb
    by_contra! hn
    exact hf (singleton_quota host hb hn)
  have he : #B≤ec G B L := by
    calc #B = ∑ _b∈B,1 := by simp
      _ ≤ _ := sum_le_sum (by
        intro b hb
        obtain ⟨x,hx,hxb⟩ := hcover b hb
        exact card_pos.mpr ⟨x,mem_filter.mpr ⟨hx,(G.adj_comm x b).mp hxb⟩⟩)
  have hel : ec G L B=q*#L := by
    unfold ec
    calc (∑ x ∈ L,dg G B x) = ∑ _x∈L,q := by
          apply sum_congr rfl
          intro x hx
          have hm := mem_filter.mp hx
          exact (dg_eq_degree host.bipartite hm.1).trans hm.2
      _ = _ := by simp [sum_const,smul_eq_mul,mul_comm]
  rw [ec_comm,hel] at he
  have hm : q*#L≤q*2 := Nat.mul_le_mul_left q hl
  have hc := host.card
  omega

open AllHThirdQuotaFailure (scar marked Cleanup)

open Classical in
lemma scar_sum (host : Host q a G A B) :
    ∑ v:V,scar (G:=G) q v = 2*AllHQuotaNonstrict.constant 4 q a := by
  classical
  have hd : ∀ v:V, scar (G:=G) q v+G.degree v=2*q-2 :=
    fun v => Nat.sub_add_cancel (host.cap_degree v)
  have hs : (∑ v:V,scar (G:=G) q v)+(∑ v:V,G.degree v)=
      (2*q-2)*Fintype.card V := by
    rw [← sum_add_distrib]
    calc ∑ v:V,(scar (G:=G) q v+G.degree v) = ∑ _v:V,(2*q-2) :=
          sum_congr rfl (fun v _ => hd v)
      _ = _ := by simp [sum_const,smul_eq_mul,mul_comm]
  have he : (∑ v:V,G.degree v)=2*G.edgeSet.ncard := by
    simpa only [G.edgeFinset_card,Set.ncard_eq_toFinset_card',Set.toFinset_card] using
      G.sum_degrees_eq_twice_card_edges
  have hc := host.edges
  have hq : 25600≤q := host.parameters.large
  have hD : 2*q-2=2*(q-1) := by omega
  rw [hD,he] at hs
  nlinarith

open Classical in
lemma marked_card (host : Host q a G A B) (ha : a=42 ∨ a=43) :
    #(marked G q)≤31 := by
  classical
  have hq : 25600≤q := host.parameters.large
  have hm : q*#(marked G q)≤∑ v∈marked G q,4*scar (G:=G) q v := by
    calc q*#(marked G q) = ∑ _v∈marked G q,q := by simp [sum_const,smul_eq_mul,mul_comm]
      _ ≤ _ := sum_le_sum (fun v hv => (AllHThirdQuotaFailure.mem_marked v).mp hv |>.le)
  have hsub : (∑ v∈marked G q,scar (G:=G) q v)≤∑ v:V,scar (G:=G) q v :=
    sum_le_sum_of_subset (subset_univ _)
  rw [← mul_sum] at hm
  have hs := scar_sum host
  have hc : AllHQuotaNonstrict.constant 4 q a < 4*q := by
    unfold AllHQuotaNonstrict.constant
    rcases ha with rfl|rfl <;> omega
  have hh : #(marked G q)<32 := by
    have hp : q*#(marked G q)<q*32 := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left hp
  omega

open Classical in
lemma cleanup_factor (host : Host q a G A B) (ha : a=42 ∨ a=43)
    (hupper : #A<2*q) :
    ∃ P Q : Finset V, P⊆A ∧ Q⊆B ∧ q≤#P ∧ #P=#Q ∧
      ∃ H:G.Subgraph,H.verts=(↑(P∪Q):Set V) ∧
        H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  classical
  have hq : 25600≤q := host.parameters.large
  have hcard := host.card
  have hord := host.shore_order
  have hn := host.order
  have hlarge : q≤#A ∧ q≤#B := by omega
  have hmarks := marked_card host ha
  obtain ⟨P,Q,d⟩ := AllHThirdQuotaFailure.exists_cleanup (G:=G) q A B
  have hPA := d.left_original
  have hQB := d.right_original
  have hbalance := d.balanced
  have homit := d.omission_counts hcard
  have hlossA : #(A\P)≤31 := by omega
  have hlossB : #(B\Q)≤32 := by omega
  have hsize : q≤#P ∧ #P<2*q := by
    have hsd := card_sdiff_add_card_eq_card hPA
    have hle := card_le_card hPA
    have hA := AllHThirdQuotaFailure.card_le_unmarked (G:=G) (q:=q) A
    have hB := AllHThirdQuotaFailure.card_le_unmarked (G:=G) (q:=q) B
    -- Nonemptiness follows from the original shore sizes and the mark bound.
    have hPne : P.Nonempty := by
      apply card_pos.mp
      rw [d.size]
      exact lt_min (by omega) (by omega)
    obtain ⟨v,hv⟩ := hPne
    have hnot := (mem_sdiff.mp (d.left hv)).2
    have hscar : 4*scar (G:=G) q v≤q := by
      by_contra! hb
      exact hnot ((AllHThirdQuotaFailure.mem_marked v).mpr hb)
    have hcap := Nat.sub_add_cancel (host.cap_degree v)
    have hdeg : dg G B v=G.degree v := dg_eq_degree host.bipartite (hPA hv)
    have hsplit := dg_sdiff_add (G:=G) hQB v
    have hloss := dg_le_card (G:=G) (B\Q) v
    have hd : 3*q≤2*dg G Q v := by unfold scar at hscar; omega
    have hbnd := dg_le_card (G:=G) Q v
    omega
  have hl : ∀ v∈P,#P+q≤2*dg G Q v := by
    intro v hv
    have hnot := (mem_sdiff.mp (d.left hv)).2
    have hscar : 4*scar (G:=G) q v≤q := by
      by_contra! hb
      exact hnot ((AllHThirdQuotaFailure.mem_marked v).mpr hb)
    have hcap := Nat.sub_add_cancel (host.cap_degree v)
    have hdeg : dg G B v=G.degree v := dg_eq_degree host.bipartite (hPA hv)
    have hsplit := dg_sdiff_add (G:=G) hQB v
    have hloss := dg_le_card (G:=G) (B\Q) v
    unfold scar at hscar
    omega
  have hr : ∀ v∈Q,#P+q≤2*dg G P v := by
    intro v hv
    have hnot := (mem_sdiff.mp (d.right hv)).2
    have hscar : 4*scar (G:=G) q v≤q := by
      by_contra! hb
      exact hnot ((AllHThirdQuotaFailure.mem_marked v).mpr hb)
    have hcap := Nat.sub_add_cancel (host.cap_degree v)
    have hdeg : dg G A v=G.degree v := dg_eq_degree host.bipartite.symm (hQB hv)
    have hsplit := dg_sdiff_add (G:=G) hPA v
    have hloss := dg_le_card (G:=G) (A\P) v
    unfold scar at hscar
    omega
  have hfactor := AllHThirdQuotaFailure.dense_factor q hbalance hsize.1 hl hr
  have hPne : P.Nonempty := card_pos.mp (by omega)
  have hsub := factor_exact_subgraph (show 0<q by omega) hPne
    (host.disjoint.mono hPA hQB) hfactor
  exact ⟨P,Q,hPA,hQB,hsize.1,hbalance,hsub⟩

open Classical in
lemma balanced_proper (host : Host q a G A B) {P Q : Finset V}
    (hP : P⊆A) (hQ : Q⊆B) (hbalance : #P=#Q)
    (H : G.Subgraph) (hverts : H.verts=(↑(P∪Q):Set V)) :
    H.verts⊂(Set.univ:Set V) := by
  classical
  rw [hverts]
  apply Set.ssubset_univ_iff.mpr
  intro he
  have hfull : P∪Q=(univ:Finset V) := Finset.coe_injective (by simpa using he)
  have hc := card_union_of_disjoint (host.disjoint.mono hP hQ)
  rw [hfull,card_univ] at hc
  have hp := card_le_card hP
  have hAB := host.card
  have hn := host.shore_order
  omega

open Classical in
/-- Exact R733-J1: internally selected balanced proper original q-factor. -/
theorem original_factor (q a : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V)
    (large : 25600≤q) (offset : a=42 ∨ a=43)
    (disjoint : Disjoint A B) (cover : A∪B=univ)
    (bipartite : G.IsBipartiteWith (A:Set V) (B:Set V))
    (card : #B=#A+1) (order : 2*q≤Fintype.card V)
    (min_degree : ∀ v:V,q≤G.degree v)
    (cap_degree : ∀ v:V,G.degree v≤2*q-2)
    (edges : (G.edgeSet.ncard:ℤ)=((q:ℤ)-1)*Fintype.card V-((4:ℤ)*q-a))
    (proper : ∀ X:Finset V,4≤#X → #X<Fintype.card V →
      (4:ℤ)*q-a≤((q:ℤ)-1)*#X-((G.induce (X:Set V)).edgeSet.ncard:ℤ)) :
    ∃ P Q:Finset V,P⊆A ∧ Q⊆B ∧ q≤#P ∧ #P=#Q ∧
      ∃ H:G.Subgraph,H.verts=(↑(P∪Q):Set V) ∧ H.verts.Nonempty ∧
        H.coe.IsRegularOfDegree q ∧ H.verts⊂(Set.univ:Set V) := by
  classical
  have p : AllHQuotaNonstrict.Parameters 4 q 1 a :=
    ⟨by decide,by norm_num; exact large,by decide,by decide,by rcases offset with rfl|rfl <;> decide,
      by rcases offset with rfl|rfl <;> decide⟩
  have hconst := p.constant_cast
  have hedge : G.edgeSet.ncard+AllHQuotaNonstrict.constant 4 q a=
      (q-1)*Fintype.card V := by
    have hqm : q-1+1=q := by omega
    zify at hqm ⊢
    norm_num at hconst
    nlinarith
  have host : Host q a G A B :=
    ⟨p,disjoint,cover,bipartite,card,order,min_degree,cap_degree,hedge,by
      intro X hX hXproper
      have hf := proper X hX hXproper
      norm_num at hconst
      omega⟩
  by_cases quota : ∃ O0:Finset V,O0⊆B ∧ #O0=1 ∧ ∀ x∈A,
      G.degree x≤q+3 → dg G O0 x≤G.degree x-q
  · obtain ⟨O,hOB,hOc,_cuts,H,hverts,hnonempty,hregular⟩ :=
      AllHQuotaNonstrict.original_host_caller 4 q 1 a G A B p.height p.large
        p.positive p.surplus p.lower p.upper disjoint cover bipartite card order
        min_degree cap_degree edges proper
        (by simpa only [show q+2*4-5=q+3 by omega] using quota)
    have hQ : B\O⊆B := sdiff_subset
    have hc := card_sdiff_add_card_eq_card hOB
    have hb : #A=#(B\O) := by omega
    have hord := host.shore_order
    have hsize : q≤#A := by omega
    have hproper := balanced_proper host (Subset.refl A) hQ hb H hverts
    exact ⟨A,B\O,Subset.refl A,hQ,hsize,hb,H,hverts,hnonempty,hregular,hproper⟩
  · have hsmall := failed_shore host offset quota
    obtain ⟨P,Q,hPA,hQB,hsize,hbalance,H,hverts,hnonempty,hregular⟩ :=
      cleanup_factor host offset hsmall
    have hproper := balanced_proper host hPA hQB hbalance H hverts
    exact ⟨P,Q,hPA,hQB,hsize,hbalance,H,hverts,hnonempty,hregular,hproper⟩

#print axioms original_factor
end Erdos585.R744
