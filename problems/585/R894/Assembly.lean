import R894.Basics
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
open Finset
namespace Erdos585.QB7S0012R894
open QB4 QB7SmallLobeR643 QB7MixedOmissionR700
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

/-- Four proved arguments cover every ordered lobe profile, with no size guard. -/
theorem oriented_exists {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 : V}
    (hi : QB7Conditional.U2Input G U W) (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hdf₁ : df G U W₁ = 5) (hdf₂ : df G U W₂ = 5)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2) :
    ∃ z₁ ∈ W₁, ∃ z₂ ∈ W₂, dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      FixedOmissionFactor G U W z₁ z₂ := by
  have hi' := U2Input.of_original hi
  have hp₁ := original_profile hi' h.subsets.2.2.1
  have hp₂ := original_profile hi' h.subsets.2.2.2
  have he₁ := df_four_five_six hp₁
  have he₂ := df_four_five_six hp₂
  by_cases ha₂ : #{z ∈ W₂ | dg G U z = 4} = 0
  · have h56₂ := five_six_of_no_four hp₂ ha₂
    have hb₂ : #{z ∈ W₂ | dg G U z = 5} = 5 := by omega
    by_cases ha₁ : #{z ∈ W₁ | dg G U z = 4} = 0
    · have h56₁ := five_six_of_no_four hp₁ ha₁
      have hb₁ : #{z ∈ W₁ | dg G U z = 5} = 5 := by omega
      have hh := QB7AllFive0012R792.original_allfive0012_count hi h hu hdu hs6 h56₁ hb₁ h56₂ hb₂
      obtain ⟨p,hp⟩ := card_pos.mp (show 0 < #{p ∈ (W₁.filter (fun z => dg G U z = 5)) ×ˢ
        (W₂.filter (fun z => dg G U z = 5)) | FixedOmissionFactor G U W p.1 p.2} by omega)
      rcases mem_filter.mp hp with ⟨hpW,hpF⟩
      rcases mem_product.mp hpW with ⟨hp₁',hp₂'⟩
      rcases mem_filter.mp hp₁' with ⟨hz₁,hd₁⟩
      rcases mem_filter.mp hp₂' with ⟨hz₂,hd₂⟩
      exact ⟨p.1,hz₁,p.2,hz₂,by omega,by omega,hpF⟩
    · obtain ⟨z₁,hz₁⟩ := card_pos.mp (show 0 < #{z ∈ W₁ | dg G U z = 4} by omega)
      rcases mem_filter.mp hz₁ with ⟨hz₁,hd₁⟩
      have hh := QB7ReverseExtensionR805.original_at_least_three_of_deficits
        hi h hu hdu hdf₁ hdf₂ hs6 h56₂ hb₂ hz₁ hd₁
      obtain ⟨z₂,hz₂⟩ := card_pos.mp (show 0 < #{z ∈ W₂ |
        dg G U z = 5 ∧ FixedOmissionFactor G U W z₁ z} by omega)
      rcases mem_filter.mp hz₂ with ⟨hz₂,hd₂,hf⟩
      exact ⟨z₁,hz₁,z₂,hz₂,by omega,by omega,hf⟩
  · obtain ⟨z₂,hz₂⟩ := card_pos.mp (show 0 < #{z ∈ W₂ | dg G U z = 4} by omega)
    rcases mem_filter.mp hz₂ with ⟨hz₂,hd₂⟩
    by_cases ha₁ : 2 ≤ #{z ∈ W₁ | dg G U z = 4}
    · obtain ⟨z₁,hz₁,z₁',hz₁',hne⟩ := one_lt_card.mp (show 1 < #{z ∈ W₁ | dg G U z = 4} by omega)
      rcases mem_filter.mp hz₁ with ⟨hz₁,hd₁⟩
      rcases mem_filter.mp hz₁' with ⟨hz₁',hd₁'⟩
      rcases QB7TwoDegreeFourR676.original_two_degreefour_choices hi h hu hdu
        hz₁ hz₁' hne hz₂ hd₁ hd₁' hd₂ with hf|hf
      · exact ⟨z₁,hz₁,z₂,hz₂,by omega,by omega,hf⟩
      · exact ⟨z₁',hz₁',z₂,hz₂,by omega,by omega,hf⟩
    · have hb₁ : 3 ≤ #{z ∈ W₁ | dg G U z = 5} := by omega
      have hh := QB7Weighted0012R782.original_weighted0012_count hi h hu hdu hs6 hdf₁ hdf₂ hp₁ hz₂ hd₂
      obtain ⟨z₁,hz₁⟩ := card_pos.mp (show 0 < #{z ∈ W₁ |
        dg G U z = 5 ∧ FixedOmissionFactor G U W z z₂} by omega)
      rcases mem_filter.mp hz₁ with ⟨hz₁,hd₁,hf⟩
      exact ⟨z₁,hz₁,z₂,hz₂,by omega,by omega,hf⟩

#print axioms oriented_exists
end Erdos585.QB7S0012R894
