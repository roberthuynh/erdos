import R763
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
open Finset
namespace Erdos585.QB7ReverseExtensionR805
open QB4 QB7SmallLobeR643 QB7Reversed0012R763 QB7MixedOmissionR700
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

/-- The tail-capacity argument needs deficit five, not a particular scarred profile. -/
theorem original_at_most_two_of_deficits
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hdf₁ : df G U W₁ = 5) (hdf₂ : df G U W₂ = 5)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 5 ∨ dg G U y = 6)
    (hz₁ : z₁ ∈ W₁) (hd₁ : dg G U z₁ = 4) :
    #{z ∈ W₂ | dg G U z = 5 ∧ ¬ FixedOmissionFactor G U W z₁ z} ≤ 2 := by
  classical
  have hi' := U2Input.of_original hi
  by_contra hn
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := two_lt_card_iff.mp (by omega :
    2 < #{z ∈ W₂ | dg G U z = 5 ∧ ¬ FixedOmissionFactor G U W z₁ z})
  rcases mem_filter.mp ha with ⟨haW,haD,haF⟩
  rcases mem_filter.mp hb with ⟨hbW,hbD,hbF⟩
  rcases mem_filter.mp hc with ⟨hcW,hcD,hcF⟩
  obtain ⟨ta,hta⟩ := failed_pair_port_tail h hi' hu hdu hdf₁ hdf₂ hs6 hz₁ haW hd₁ haD haF
  obtain ⟨tb,htb⟩ := failed_pair_port_tail h hi' hu hdu hdf₁ hdf₂ hs6 hz₁ hbW hd₁ hbD hbF
  obtain ⟨tc,htc⟩ := failed_pair_port_tail h hi' hu hdu hdf₁ hdf₂ hs6 hz₁ hcW hd₁ hcD hcF
  obtain ⟨tab,_,htab⟩ := ta.union h.swap hi' hdf₂ (filter_subset _ _) hs6 tb
  obtain ⟨tabc,_,htabc⟩ := tab.union h.swap hi' hdf₂ (filter_subset _ _) hs6 tc
  have hbound := tabc.marker_bound h.swap hi' hw₂
  have hsub : {a,b,c} ⊆ tabc.B.filter (fun z => dg G U z = 5) := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl|rfl
    · exact mem_filter.mpr ⟨by rw [htabc,htab]; exact mem_union_left _ (mem_union_left _ hta),haD⟩
    · exact mem_filter.mpr ⟨by rw [htabc,htab]; exact mem_union_left _ (mem_union_right _ htb),hbD⟩
    · exact mem_filter.mpr ⟨by rw [htabc]; exact mem_union_right _ htc,hcD⟩
  have hthree : #({a,b,c} : Finset V) = 3 := by simp [hab,hac,hbc]
  have hh := card_le_card hsub
  omega

/-- At least three exact original factors under the minimal deficit interface. -/
theorem original_at_least_three_of_deficits
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hdf₁ : df G U W₁ = 5) (hdf₂ : df G U W₂ = 5)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c : #{y ∈ W₂ | dg G U y = 5} = 5)
    (hz₁ : z₁ ∈ W₁) (hd₁ : dg G U z₁ = 4) :
    3 ≤ #{z ∈ W₂ | dg G U z = 5 ∧ FixedOmissionFactor G U W z₁ z} := by
  classical
  have hb := original_at_most_two_of_deficits hi h hu hdu hdf₁ hdf₂ hs6 hw₂ hz₁ hd₁
  have he := card_filter_add_card_filter_not
    (s := W₂.filter fun z => dg G U z = 5) (fun z => FixedOmissionFactor G U W z₁ z)
  simp only [filter_filter] at he
  omega

/-- Literal remaining S0012 D5-5 A2-0 caller, for any fixed scarred degree-four vertex. -/
theorem original_reverse_extension_target
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (_hn₁ : 6 ≤ #U₁) (_hn₂ : 6 ≤ #U₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (_hs : ∀ s ∈ S, dg G U s = 4 ∨ dg G U s = 5 ∨ dg G U s = 6)
    (_hs4 : #{s ∈ S | dg G U s = 4} = 1)
    (_hs5 : #{s ∈ S | dg G U s = 5} = 1)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c : #{y ∈ W₂ | dg G U y = 5} = 5)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c₄ : #{y ∈ W₁ | dg G U y = 4} = 2)
    (hw₁c₅ : #{y ∈ W₁ | dg G U y = 5} = 1)
    (hz₁ : z₁ ∈ W₁) (hd₁ : dg G U z₁ = 4) :
    #{z ∈ W₂ | dg G U z = 5 ∧ ¬ FixedOmissionFactor G U W z₁ z} ≤ 2 ∧
    3 ≤ #{z ∈ W₂ | dg G U z = 5 ∧ FixedOmissionFactor G U W z₁ z} := by
  have hdf₂ : df G U W₂ = 5 := by rw [df_five_six hw₂,hw₂c]; norm_num
  have hdf₁ : df G U W₁ = 5 := by rw [df_four_five_six hw₁,hw₁c₄,hw₁c₅]; norm_num
  exact ⟨original_at_most_two_of_deficits hi h hu hdu hdf₁ hdf₂ hs6 hw₂ hz₁ hd₁,
    original_at_least_three_of_deficits hi h hu hdu hdf₁ hdf₂ hs6 hw₂ hw₂c hz₁ hd₁⟩

#print axioms original_at_most_two_of_deficits
#print axioms original_at_least_three_of_deficits
#print axioms original_reverse_extension_target
end Erdos585.QB7ReverseExtensionR805
