import AllHFourthQuotaFailure.Interface

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] r248InterfaceDecidableEq
namespace Erdos585.AllHFourthQuotaFailure
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {h q j : ℕ} {A B : Finset V}

def scar (q : ℕ) (v : V) : ℕ := (2*q-2)-G.degree v

lemma mem_marked (v : V) : v∈marked G q ↔ q<4*scar (G:=G) q v := by
  simp [marked,scar]

namespace Host

lemma numeric (host : Host h q j G A B) :
    0<q ∧ 72*h+16≤q ∧ 24*h≤q ∧ 9*h<q ∧ j<h ∧ 0<j := by
  have hh := host.height
  have hq := host.large
  have hj := host.surplus
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith [Nat.sub_add_cancel (show 4≤h by omega)]

lemma constant_lt (host : Host h q j G A B) : constant h q<h*q := by
  have hn := Host.numeric host
  have hh := host.height
  have hp : 0<h*q := Nat.mul_pos (by omega) hn.1
  have ho : 0<offset h := by unfold offset; omega
  unfold constant
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

lemma scar_sum (host : Host h q j G A B) :
    ∑ v:V,scar (G:=G) q v = 2*constant h q := by
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
end Erdos585.AllHFourthQuotaFailure
