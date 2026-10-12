/- Full literal S0012 assembly. 
-/
import R782
import R792
import R805
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
open Finset
namespace Erdos585.QB7S0012R894
open QB4 QB7SmallLobeR643 QB7MixedOmissionR700
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

lemma original_deficiencies {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hs : ∀ s ∈ S, dg G U s = 4 ∨ dg G U s = 5 ∨ dg G U s = 6)
    (hs4 : #{s ∈ S | dg G U s = 4} = 1)
    (hs5 : #{s ∈ S | dg G U s = 5} = 1) :
    df G U W₁ = 5 ∧ df G U W₂ = 5 := by
  have hds : df G U S = 3 := by rw [df_four_five_six hs,hs4,hs5]; norm_num
  have hd := hi.defW
  unfold df at hd
  rw [← h.rightCover,sum_union (show Disjoint (W₁ ∪ W₂) S from
    disjoint_union_left.mpr ⟨h.rightSep₁,h.rightSep₂⟩),sum_union h.rightDisjoint] at hd
  change df G U W₁+df G U W₂+df G U S = 13 at hd
  have h₁ := h.interior_scar hi
  have h₂ := h.swap.interior_scar hi
  exact ⟨by omega,by omega⟩

omit [DecidableEq V] in
lemma original_profile {U W K : Finset V} (hi : U2Input G U W) (hK : K ⊆ W) :
    ∀ z ∈ K, dg G U z = 4 ∨ dg G U z = 5 ∨ dg G U z = 6 := by
  intro z hz
  have hl := hi.minW z (hK hz)
  have hu := hi.capW z (hK hz)
  omega

omit [DecidableEq V] in
lemma five_six_of_no_four {U K : Finset V}
    (hp : ∀ z ∈ K, dg G U z = 4 ∨ dg G U z = 5 ∨ dg G U z = 6)
    (ha : #{z ∈ K | dg G U z = 4} = 0) :
    ∀ z ∈ K, dg G U z = 5 ∨ dg G U z = 6 := by
  intro z hz
  rcases hp z hz with hd|hd|hd
  · have hh : z ∈ K.filter (fun z => dg G U z = 4) := mem_filter.mpr ⟨hz,hd⟩
    have hn := card_pos.mpr ⟨z,hh⟩
    omega
  · exact Or.inl hd
  · exact Or.inr hd

lemma original_scar_exists {U W : Finset V} (hi : U2Input G U W) :
    ∃ u0 ∈ U, dg G W u0 = 5 := by
  by_contra hn
  push Not at hn
  have hz : df G W U = 0 := by
    unfold df
    apply sum_eq_zero
    intro u hu
    have hmin := hi.minU_five u hu
    have hmax := hi.capU u hu
    have hne := hn u hu
    have he : dg G W u = 6 := by omega
    rw [he]
    norm_num
  rw [hi.defU] at hz
  omega

omit [DecidableRel G.Adj] in
lemma fixed_factor_swap {U W : Finset V} {z₁ z₂ : V}
    (hf : FixedOmissionFactor G U W z₁ z₂) : FixedOmissionFactor G U W z₂ z₁ := by
  have he : (W.erase z₁).erase z₂ = (W.erase z₂).erase z₁ := by
    ext y
    simp only [mem_erase]
    tauto
  unfold FixedOmissionFactor at hf ⊢
  rwa [he] at hf

/-- The literal edge set from the fixed factor supplies a nonempty allowed-support Quartic. -/
lemma quartic_of_fixed_factor {U W S U₁ U₂ W₁ W₂ : Finset V} {z₁ z₂ : V}
    (hi : U2Input G U W) (h : Split G U W S U₁ U₂ W₁ W₂)
    (hf : FixedOmissionFactor G U W z₁ z₂) : Quartic G U W := by
  obtain ⟨F,hF,hadj,hFU,hFQ⟩ := hf
  have hU₁ : U₁.Nonempty := card_pos.mp (by have hh := h.left_large hi; omega)
  obtain ⟨u,hu⟩ := hU₁
  have huU := h.subsets.1 hu
  have hne : F.Nonempty := by
    obtain ⟨e,he⟩ := card_pos.mp (show 0 < #{e ∈ F | e.1 = u} by rw [hFU u huU]; omega)
    exact ⟨e,(mem_filter.mp he).1⟩
  refine ⟨F,hne,?_,hadj,?_,?_⟩
  · intro e he
    have hh := mem_product.mp (hF he)
    exact mem_product.mpr ⟨hh.1,(erase_subset z₁ W) ((erase_subset z₂ (W.erase z₁)) hh.2)⟩
  · intro x
    by_cases hx : x ∈ U
    · exact Or.inr (hFU x hx)
    · exact Or.inl (card_eq_zero.mpr (filter_eq_empty_iff.mpr (fun e he hex => by
        exact hx (hex ▸ (mem_product.mp (hF he)).1))))
  · intro y
    by_cases hy : y ∈ (W.erase z₁).erase z₂
    · exact Or.inr (hFQ y hy)
    · exact Or.inl (card_eq_zero.mpr (filter_eq_empty_iff.mpr (fun e he hey => by
        exact hy (hey ▸ (mem_product.mp (hF he)).2))))

#print axioms original_deficiencies
#print axioms original_profile
#print axioms five_six_of_no_four
#print axioms original_scar_exists
#print axioms fixed_factor_swap
#print axioms quartic_of_fixed_factor
end Erdos585.QB7S0012R894
