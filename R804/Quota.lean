import R804.Basics

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] r804DecidableEq
namespace Erdos585.R804
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {h q j ξ : ℕ} {A B T I : Finset V}

lemma exists_minimal_failed (hf : Failed G q j B T) :
    ∃ I, MinimalFailed G q j B T I := by
  let S := T.powerset.filter (Failed G q j B)
  have hS : T∈S := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl,hf⟩
  obtain ⟨I,hI,hmin⟩ := exists_min_image S card ⟨T,hS⟩
  have hi := mem_filter.mp hI
  refine ⟨I,⟨mem_powerset.mp hi.1,hi.2,?_⟩⟩
  intro J hJ hc hfJ
  have hh := hmin J (mem_filter.mpr ⟨mem_powerset.mpr
    (hJ.trans (mem_powerset.mp hi.1)),hfJ⟩)
  omega

namespace MinimalFailed
variable (hi : MinimalFailed G q j B T I)
include hi

lemma nonempty (hb : j≤#B) : I.Nonempty := by
  by_contra hn
  have he : I=∅ := not_nonempty_iff_eq_empty.mp hn
  obtain ⟨O,hO,hOc⟩ := exists_subset_card_eq hb
  exact hi.failed ⟨O,hO,hOc,by simp [he]⟩

lemma quota_lt {v : V} (hv : v∈I) : G.degree v-q<j := by
  by_contra! hn
  have hcard := card_erase_of_mem hv
  have hpos : 0<#I := card_pos.mpr ⟨v,hv⟩
  have hf := hi.minimal (I.erase v) (erase_subset v I) (by omega)
  unfold Failed at hf
  push Not at hf
  obtain ⟨O,hO,hOc,hgood⟩ := hf
  apply hi.failed
  refine ⟨O,hO,hOc,?_⟩
  intro w hw
  by_cases he : w=v
  · subst w
    exact (card_filter_le O _).trans (by omega)
  · exact hgood w (mem_erase.mpr ⟨he,hw⟩)

lemma outside_lt : #(B.filter (fun z => ∀ v∈I, ¬G.Adj v z))<j := by
  by_contra! hn
  obtain ⟨O,hO,hOc⟩ := exists_subset_card_eq hn
  apply hi.failed
  refine ⟨O,hO.trans (filter_subset _ _),hOc,?_⟩
  intro v hv
  have he : O.filter (G.Adj v)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hh := mem_filter.mp hz
    exact (mem_filter.mp (hO hh.1)).2 v hv hh.2
  simp [he]

lemma marked (host : Host h q j ξ G A B) : I ⊆ marked G q := by
  intro v hv
  have ht := hi.quota_lt hv
  have hn := Host.numeric host
  have hs := host.surplus
  have hd := Nat.sub_add_cancel (host.min_degree v)
  have hc := host.cap_degree v
  rw [mem_marked]
  unfold scar
  omega

lemma shore_bound (host : Host h q j ξ G A B) (hT : T⊆A) (hTc : #T≤3) :
    #A≤3*q+3*h := by
  let N : V → Finset V := fun v => B.filter (G.Adj v)
  let Z := B.filter (fun z => ∀ v∈I, ¬G.Adj v z)
  have hcover : B ⊆ I.biUnion N ∪ Z := by
    intro z hz
    by_cases hh : ∃ v∈I, G.Adj v z
    · obtain ⟨v,hv,hadj⟩ := hh
      exact mem_union_left _ (mem_biUnion.mpr ⟨v,hv,mem_filter.mpr ⟨hz,hadj⟩⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hz,by simpa using hh⟩)
  have hcount : #B ≤ (∑ v∈I,#(N v))+#Z :=
    (card_le_card hcover).trans ((card_union_le _ _).trans (Nat.add_le_add_right card_biUnion_le _))
  have hs : ∑ v∈I,#(N v) ≤ #I*(q+j-1) := by
    calc ∑ v∈I,#(N v) ≤ ∑ _v∈I,(q+j-1) := by
          apply sum_le_sum
          intro v hv
          have hd : #(N v)=G.degree v := dg_eq_degree host.bipartite (hT (hi.subset hv))
          have ht := hi.quota_lt hv
          have he := Nat.sub_add_cancel (host.min_degree v)
          have hn := Host.numeric host
          omega
      _ = _ := by simp [sum_const,smul_eq_mul]
  have hIc : #I≤3 := (card_le_card hi.subset).trans hTc
  have hprod := Nat.mul_le_mul_right (q+j-1) hIc
  have hz := hi.outside_lt
  have hc := host.card
  have hn := Host.numeric host
  have hj := host.surplus
  change #Z<j at hz
  omega

end MinimalFailed
end Erdos585.R804
