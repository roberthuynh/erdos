/- R869 full literal S0002 existential repair, all profiles and allocations.

-/
import R869.Assembly
import R869.LocalB
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Finset
namespace Erdos585.QB7S0002R869
open QB4 QB7SmallLobeR643
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

/-- Both the four-containing and six-five profiles follow from literal inputs. -/
lemma safe_d6_marker {U W S P P' L L' : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hdt : dg G U t = 4)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6)
    (hδ : df G U L = 6) :
    ∃ z ∈ L, dg G U z < 6 ∧
      ∀ Y ⊆ L.erase z, ec G P {t} ≤ rankTerm G P Y {t} := by
  by_cases hf : ∃ z ∈ L, dg G U z = 4
  · obtain ⟨z,hz,hdz⟩ := hf
    exact ⟨z,hz,by omega,four_marker_safe h hi ht hδ hz hdz⟩
  · obtain ⟨hprofile,_⟩ := no_four_six_fives h hi hδ hf
    obtain ⟨z,hz,hdz,hcut⟩ := six_five_safe_marker h hi ht hdt hs hδ hprofile
    exact ⟨z,hz,by omega,hcut⟩

lemma original_s0002_oriented {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 t : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (ht : t ∈ S) (hdt : dg G U t = 4)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6) :
    ∃ z₁ ∈ W₁, ∃ z₂ ∈ W₂, dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      FixedOmissionFactor G U W z₁ z₂ := by
  have hd := interior_deficiencies h hi ht hdt hs
  by_cases hdf : df G U W₁ = 5
  · have hδ : df G U W₂ = 6 := by omega
    obtain ⟨z₂,hz₂,hd₂,hcut⟩ := safe_d6_marker h.swap hi ht hdt hs hδ
    obtain ⟨z₁,hz₁,hd₁,hf⟩ := assemble_d5_d6 h hi hu hdu ht hdt hs hdf hz₂ hd₂ hcut
    exact ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,hf⟩
  · have hδ : df G U W₁ = 6 := by omega
    have hdf₂ : df G U W₂ = 5 := by omega
    obtain ⟨z₁,hz₁,hd₁,hcut⟩ := safe_d6_marker h hi ht hdt hs hδ
    obtain ⟨z₂,hz₂,hd₂,hf⟩ := assemble_d6_d5 h hi hu hdu ht hdt hs hdf₂ hz₁ hd₁ hcut
    exact ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,hf⟩

/-- No scar location is supplied: its existence and orientation are derived. -/
theorem original_s0002_exists {U W S U₁ U₂ W₁ W₂ : Finset V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hs : ∀ s ∈ S, dg G U s = 4 ∨ dg G U s = 6)
    (hs4 : #{s ∈ S | dg G U s = 4} = 1) :
    ∃ z₁ ∈ W₁, ∃ z₂ ∈ W₂, dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      FixedOmissionFactor G U W z₁ z₂ := by
  have hi' := U2Input.of_original hi
  obtain ⟨t,hteq⟩ := card_eq_one.mp hs4
  have htf : t ∈ S.filter (fun s => dg G U s = 4) := by rw [hteq]; simp
  obtain ⟨ht,hdt⟩ := mem_filter.mp htf
  have hsat : ∀ s ∈ S, s ≠ t → dg G U s = 6 := by
    intro s hss hst
    rcases hs s hss with hd|hd
    · have hm : s ∈ S.filter (fun s => dg G U s = 4) := mem_filter.mpr ⟨hss,hd⟩
      rw [hteq] at hm
      exact False.elim (hst (mem_singleton.mp hm))
    · exact hd
  obtain ⟨u0,hu,hdu⟩ := original_scar_exists hi'
  have hor : u0 ∈ U₁ ∨ u0 ∈ U₂ := by rw [← h.leftCover] at hu; exact mem_union.mp hu
  rcases hor with hu₁|hu₂
  · exact original_s0002_oriented h hi' hu₁ hdu ht hdt hsat
  · obtain ⟨z₂,hz₂,z₁,hz₁,hd₂,hd₁,hf⟩ := original_s0002_oriented h.swap hi' hu₂ hdu ht hdt hsat
    exact ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,fixed_factor_swap hf⟩

/-- Exact raw original unit-edge quartic on every retained original vertex. -/
theorem original_s0002_raw {U W S U₁ U₂ W₁ W₂ : Finset V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hs : ∀ s ∈ S, dg G U s = 4 ∨ dg G U s = 6)
    (hs4 : #{s ∈ S | dg G U s = 4} = 1) :
    ∃ z₁ ∈ W₁, ∃ z₂ ∈ W₂, dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      ∃ F : Finset (V × V), F ⊆ U ×ˢ (W.erase z₁ |>.erase z₂) ∧
        (∀ e ∈ F, G.Adj e.1 e.2) ∧
        (∀ x ∈ U, #{e ∈ F | e.1 = x} = 4) ∧
        (∀ y ∈ (W.erase z₁ |>.erase z₂), #{e ∈ F | e.2 = y} = 4) := by
  exact original_s0002_exists hi h hs hs4

#print axioms safe_d6_marker
#print axioms original_s0002_oriented
#print axioms original_s0002_exists
#print axioms original_s0002_raw
end Erdos585.QB7S0002R869
