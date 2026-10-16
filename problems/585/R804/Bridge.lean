import R804.Failure
import AllHQuotaNonstrict.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section

namespace Erdos585.R804
open QB4 B5 L34 H3Unequal

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {h q j ξ : ℕ} {A B T I : Finset V}

open Classical in
/-- The literal fourth-surplus host also meets the uniform positive-surplus contract. -/
lemma quota_host (host : Host h q j ξ G A B) : AllHQuotaNonstrict.Host h q j ξ G A B := by
  have hn := Host.numeric host
  have hh := host.height
  have hl := host.lower
  have hu := host.upper
  refine ⟨⟨by omega,host.large,host.positive,by omega,by omega,by omega⟩,
    host.disjoint,host.cover,host.bipartite,host.card,host.order,
    host.min_degree,host.cap_degree,host.edges,?_⟩
  intro X hX hXp
  have hf := host.proper X hX hXp
  change (constant h q ξ : ℤ) ≤ _
  omega

open Classical in
/-- The literal variable-offset original shore scar, using banked incidence transport. -/
lemma original_scar (host : Host h q j ξ G A B) :
    deficiency (2*(q:ℤ)-2) G B A = (h:ℤ)*q-ξ-((q:ℤ)-1)*j := by
  exact (quota_host host).to_data.deficient

open Classical in
/-- Every inclusion-minimal actual quota failure has at most three original A rows. -/
lemma minimal_failed_card (host : Host h q j ξ G A B)
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
    have hn := Host.numeric host
    omega
  have hhi := deficiency_le_subset (2*(q:ℤ)-2) hIA hcap
  have he := original_scar host
  rw [he] at hhi
  have hn := Host.numeric host
  have hh := host.height
  have hj := host.surplus
  have hl := host.lower
  have hnonneg : (0:ℤ)≤q-j-1 := by omega
  by_contra! hc
  have hfour : (4:ℤ)≤#I := by omega
  have hmul := mul_le_mul_of_nonneg_left hfour hnonneg
  have hjbound : (h:ℤ)≤j+4 := by rcases hj with hj|hj <;> omega
  have hprod := mul_le_mul_of_nonneg_right hjbound (show (0:ℤ)≤q by positivity)
  have hξ : (h:ℤ)^2+4*h+10≤ξ := by
    have hh' : h^2+5*h+8-h+2=h^2+4*h+10 := by omega
    rw [hh'] at hl
    exact_mod_cast hl
  have hsmall : (ξ:ℤ)≤5*j+4 := by nlinarith
  have hjh : (j:ℤ)≤h := by omega
  nlinarith [sq_nonneg ((h:ℤ)-1)]

open Classical in
/-- A failed family can be padded with redundant constraints to three distinct original rows. -/
lemma failed_three (host : Host h q j ξ G A B) (hf : Failed G q j B T) (hT : T⊆A) :
    ∃ x∈A, ∃ y∈A, ∃ z∈A, x≠y ∧ x≠z ∧ y≠z ∧ ThreeFailure G q j B x y z := by
  have hn := Host.numeric host
  have hcard := host.card
  obtain ⟨b,hb⟩ := card_pos.mp (show 0<#B by omega)
  have hA : q≤#A := calc
    q ≤ G.degree b := host.min_degree b
    _ = dg G A b := (dg_eq_degree host.bipartite.symm hb).symm
    _ ≤ #A := dg_le_card A b
  obtain ⟨I,hi⟩ := exists_minimal_failed hf
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

end Erdos585.R804
