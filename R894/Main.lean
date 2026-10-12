/- Full S0012 endpoint from literal original U2Input and Split only.
-/
import R894.Assembly
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
open Finset
namespace Erdos585.QB7S0012R894
open QB4 QB7SmallLobeR643
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

lemma separator_sixes {U S : Finset V} (hc : #S = 4)
    (hs : ∀ s ∈ S, dg G U s = 4 ∨ dg G U s = 5 ∨ dg G U s = 6)
    (hs4 : #{s ∈ S | dg G U s = 4} = 1)
    (hs5 : #{s ∈ S | dg G U s = 5} = 1) :
    #{s ∈ S | dg G U s = 6} = 2 := by
  have he : S.filter (fun s => ¬ dg G U s = 4) =
      (S.filter fun s => dg G U s = 5) ∪ (S.filter fun s => dg G U s = 6) := by
    ext s
    simp only [mem_filter,mem_union]
    constructor
    · rintro ⟨hS,hn⟩
      rcases hs s hS with hd|hd|hd
      · exact False.elim (hn hd)
      · exact Or.inl ⟨hS,hd⟩
      · exact Or.inr ⟨hS,hd⟩
    · rintro (⟨hS,hd⟩|⟨hS,hd⟩) <;> exact ⟨hS,by omega⟩
  have hd : Disjoint (S.filter fun s => dg G U s = 5) (S.filter fun s => dg G U s = 6) := by
    apply disjoint_left.mpr
    intro s h5 h6
    have h5' := (mem_filter.mp h5).2
    have h6' := (mem_filter.mp h6).2
    omega
  have hh := card_filter_add_card_filter_not (s := S) (fun s => dg G U s = 4)
  rw [he,card_union_of_disjoint hd] at hh
  omega

/-- Full literal S0012 endpoint: scar, deficits, profiles, sizes and pair are internal. -/
theorem original_s0012_exists {U W S U₁ U₂ W₁ W₂ : Finset V}
    (hi : QB7Conditional.U2Input G U W) (h : Split G U W S U₁ U₂ W₁ W₂)
    (hs : ∀ s ∈ S, dg G U s = 4 ∨ dg G U s = 5 ∨ dg G U s = 6)
    (hs4 : #{s ∈ S | dg G U s = 4} = 1)
    (hs5 : #{s ∈ S | dg G U s = 5} = 1) :
    ∃ z₁ ∈ W₁, ∃ z₂ ∈ W₂, dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      FixedOmissionFactor G U W z₁ z₂ := by
  have hi' := U2Input.of_original hi
  have hdf := original_deficiencies h hi' hs hs4 hs5
  have hs6 := separator_sixes h.cardS hs hs4 hs5
  obtain ⟨u0,hu,hdu⟩ := original_scar_exists hi'
  rw [← h.leftCover] at hu
  rcases mem_union.mp hu with hu|hu
  · exact oriented_exists hi h hu hdu hdf.1 hdf.2 hs6
  · obtain ⟨z₂,hz₂,z₁,hz₁,hd₂,hd₁,hf⟩ := oriented_exists hi h.swap hu hdu hdf.2 hdf.1 hs6
    exact ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,fixed_factor_swap hf⟩

/-- Expanded exact original edge witness, including its nonemptiness. -/
theorem original_s0012_raw {U W S U₁ U₂ W₁ W₂ : Finset V}
    (hi : QB7Conditional.U2Input G U W) (h : Split G U W S U₁ U₂ W₁ W₂)
    (hs : ∀ s ∈ S, dg G U s = 4 ∨ dg G U s = 5 ∨ dg G U s = 6)
    (hs4 : #{s ∈ S | dg G U s = 4} = 1)
    (hs5 : #{s ∈ S | dg G U s = 5} = 1) :
    ∃ z₁ ∈ W₁, ∃ z₂ ∈ W₂, dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      ∃ F : Finset (V × V), F.Nonempty ∧ F ⊆ U ×ˢ (W.erase z₁ |>.erase z₂) ∧
        (∀ e ∈ F, G.Adj e.1 e.2) ∧
        (∀ x ∈ U, #{e ∈ F | e.1 = x} = 4) ∧
        (∀ y ∈ (W.erase z₁ |>.erase z₂), #{e ∈ F | e.2 = y} = 4) := by
  obtain ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,F,hF,hadj,hFU,hFQ⟩ := original_s0012_exists hi h hs hs4 hs5
  have hi' := U2Input.of_original hi
  have hU₁ : U₁.Nonempty := card_pos.mp (by have hh := h.left_large hi'; omega)
  obtain ⟨u,hu⟩ := hU₁
  have huU := h.subsets.1 hu
  have hne : F.Nonempty := by
    obtain ⟨e,he⟩ := card_pos.mp (show 0 < #{e ∈ F | e.1 = u} by rw [hFU u huU]; omega)
    exact ⟨e,(mem_filter.mp he).1⟩
  exact ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,F,hne,hF,hadj,hFU,hFQ⟩

/-- The exact original factor supplied above gives the literal nonempty Quartic. -/
theorem original_s0012_quartic {U W S U₁ U₂ W₁ W₂ : Finset V}
    (hi : QB7Conditional.U2Input G U W) (h : Split G U W S U₁ U₂ W₁ W₂)
    (hs : ∀ s ∈ S, dg G U s = 4 ∨ dg G U s = 5 ∨ dg G U s = 6)
    (hs4 : #{s ∈ S | dg G U s = 4} = 1)
    (hs5 : #{s ∈ S | dg G U s = 5} = 1) : Quartic G U W := by
  obtain ⟨z₁,_,z₂,_,_,_,hf⟩ := original_s0012_exists hi h hs hs4 hs5
  exact quartic_of_fixed_factor (U2Input.of_original hi) h hf

/-- A single internally selected deficient pair, its exact factor, and literal Quartic. -/
theorem original_s0012_target {U W S U₁ U₂ W₁ W₂ : Finset V}
    (hi : QB7Conditional.U2Input G U W) (h : Split G U W S U₁ U₂ W₁ W₂)
    (hs : ∀ s ∈ S, dg G U s = 4 ∨ dg G U s = 5 ∨ dg G U s = 6)
    (hs4 : #{s ∈ S | dg G U s = 4} = 1)
    (hs5 : #{s ∈ S | dg G U s = 5} = 1) :
    ∃ z₁ ∈ W₁, ∃ z₂ ∈ W₂, dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      FixedOmissionFactor G U W z₁ z₂ ∧ Quartic G U W := by
  obtain ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,hf⟩ := original_s0012_exists hi h hs hs4 hs5
  exact ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,hf,quartic_of_fixed_factor (U2Input.of_original hi) h hf⟩

#print axioms separator_sixes
#print axioms original_s0012_exists
#print axioms original_s0012_raw
#print axioms original_s0012_quartic
#print axioms original_s0012_target
end Erdos585.QB7S0012R894
