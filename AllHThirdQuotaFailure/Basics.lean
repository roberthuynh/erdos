import AllHThirdQuotaFailure.Interface

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.AllHThirdQuotaFailure
open QB4 B5 L34 H3Unequal
open AllHThirdFragileFree (Host offset constant)
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {h q j : ℕ} {A B : Finset V}

def scar (q : ℕ) (v : V) : ℕ := (2*q-2)-G.degree v

lemma mem_marked (v : V) : v∈marked G q ↔ q<4*scar (G:=G) q v := by
  simp [marked,scar]

namespace Host

lemma numeric (host : Host h q j G A B) :
    0<q ∧ 36*h+8≤q ∧ 9*h<q ∧ j<h ∧ 0<j := by
  have hh := host.parameters.height
  have hq := host.parameters.large
  have hj := host.parameters.surplus
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith [Nat.sub_add_cancel (show 3≤h by omega)]

lemma constant_lt (host : Host h q j G A B) : constant h q (offset h)<h*q := by
  have p := host.parameters.to_parameters
  have he : constant h q (offset h)+offset h=h*q := Nat.sub_add_cancel p.offset_le_product
  have hp := p.lower
  have hh := p.height
  omega

lemma shore_order (host : Host h q j G A B) : #A+#B=Fintype.card V := by
  classical
  have hc := card_union_of_disjoint host.disjoint
  rw [host.cover,card_univ] at hc
  exact hc.symm

lemma shores_large (host : Host h q j G A B) {x : V} (hx : x∈A) : q≤#A ∧ q≤#B := by
  classical
  have hb : q≤#B := calc
    q ≤ G.degree x := host.min_degree x
    _ = dg G B x := (dg_eq_degree host.bipartite hx).symm
    _ ≤ #B := dg_le_card B x
  have hq := (Host.numeric host).1
  obtain ⟨b,hbmem⟩ := card_pos.mp (show 0<#B by omega)
  have ha : q≤#A := calc
    q ≤ G.degree b := host.min_degree b
    _ = dg G A b := (dg_eq_degree host.bipartite.symm hbmem).symm
    _ ≤ #A := dg_le_card A b
  exact ⟨ha,hb⟩

/-- The failed quota bounds the actual original shore; no iff supplier is used. -/
lemma shore_lt (host : Host h q j G A B) {x y : V} (hx : x∈A) (hy : y∈A)
    (hf : QuotaFailure G q j B x y) : #A<2*q := by
  classical
  let NX := B.filter (fun z => G.Adj x z)
  let NY := B.filter (fun z => G.Adj y z)
  let Z := B.filter (fun z => ¬G.Adj x z ∧ ¬G.Adj y z)
  have hsub : B⊆(NX∪NY)∪Z := by
    intro z hz
    by_cases hzx : G.Adj x z
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hz,hzx⟩))
    · by_cases hzy : G.Adj y z
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hz,hzy⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hz,hzx,hzy⟩)
  have hc : #B≤#NX+#NY+#Z :=
    (card_le_card hsub).trans (by have h1:=card_union_le (NX∪NY) Z; have h2:=card_union_le NX NY; omega)
  have hNX : #NX=G.degree x := dg_eq_degree host.bipartite hx
  have hNY : #NY=G.degree y := dg_eq_degree host.bipartite hy
  have hdx := Nat.sub_add_cancel (host.min_degree x)
  have hdy := Nat.sub_add_cancel (host.min_degree y)
  have hcard := host.card
  change #Z+(G.degree x-q)+(G.degree y-q)<j at hf
  omega

lemma root_marked (host : Host h q j G A B) {x y : V}
    (hf : QuotaFailure G q j B x y) : x∈marked G q ∧ y∈marked G q := by
  have hn := Host.numeric host
  have hj := host.parameters.surplus
  have hdx := Nat.sub_add_cancel (host.min_degree x)
  have hdy := Nat.sub_add_cancel (host.min_degree y)
  have hcx := host.cap_degree x
  have hcy := host.cap_degree y
  unfold QuotaFailure at hf
  rw [mem_marked,mem_marked]
  unfold scar
  constructor <;> omega

lemma scar_sum (host : Host h q j G A B) :
    ∑ v:V,scar (G:=G) q v = 2*constant h q (offset h) := by
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
  have hD : 2*q-2=2*(q-1) := by have hp:=(Host.numeric host).1; omega
  rw [hD,he] at hs
  nlinarith

lemma marked_card (host : Host h q j G A B) : #(marked G q)≤8*h-1 := by
  classical
  have hq := (Host.numeric host).1
  have hm : q*#(marked G q)≤∑ v∈marked G q,4*scar (G:=G) q v := by
    calc q*#(marked G q) = ∑ _v∈marked G q,q := by simp [sum_const,smul_eq_mul,mul_comm]
      _ ≤ _ := sum_le_sum (fun v hv => (mem_marked v).mp hv |>.le)
  have hsub : (∑ v∈marked G q,scar (G:=G) q v)≤∑ v:V,scar (G:=G) q v :=
    sum_le_sum_of_subset (subset_univ _)
  rw [← mul_sum] at hm
  have hs := Host.scar_sum host
  have hc := Host.constant_lt host
  have hh : #(marked G q)<8*h := by
    have hp : q*#(marked G q)<q*(8*h) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left hp
  omega

end Host
end Erdos585.AllHThirdQuotaFailure
