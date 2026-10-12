/- Global assembly with the exact local selector obligation explicit. -/
import R869.Global
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Finset
namespace Erdos585.QB7S0002R869
open QB4 QB7SmallLobeR643 QB7ProfileFreeR854
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

/-- The supplied singleton-safe omission is chosen once, before any global cut. -/
lemma assemble_d5_d6 {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₂ t : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (ht : t ∈ S) (hdt : dg G U t = 4)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6)
    (hdf : df G U W₁ = 5)
    (hz₂ : z₂ ∈ W₂) (hd₂ : dg G U z₂ < 6)
    (hsafe₂ : ∀ Y ⊆ W₂.erase z₂, ec G U₂ {t} ≤ rankTerm G U₂ Y {t}) :
    ∃ z₁ ∈ W₁, dg G U z₁ < 6 ∧ FixedOmissionFactor G U W z₁ z₂ := by
  have hs6 := separator_sixes ht h.cardS hdt hs
  obtain ⟨z₁,hz₁,hd₁,hn⟩ := exists_outside_tailMarkers h hi hdf hs6
  have he : df G U (W₁.erase z₁)+(6-(dg G U z₁ : ℤ)) = df G U W₁ :=
    sum_erase_add W₁ (fun y => 6-(dg G U y : ℤ)) hz₁
  have hsafe₁ : ∀ Y ⊆ W₁.erase z₁, ec G U₁ {t} ≤ rankTerm G U₁ Y {t} :=
    fun Y hY => retained_safe_singleton h hi ht (by omega) hY
  refine ⟨z₁,hz₁,hd₁,?_⟩
  by_contra hf
  obtain ⟨a,b,ha,_⟩ := failed_pair_tails h hi hu hdu ht hdt hs hz₁ hz₂ hd₁ hd₂ hsafe₁ hsafe₂ hf
  exact hn (mem_filter.mpr ⟨mem_filter.mpr ⟨hz₁,hd₁⟩,a,ha⟩)

lemma assemble_d6_d5 {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ t : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (ht : t ∈ S) (hdt : dg G U t = 4)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6)
    (hdf : df G U W₂ = 5)
    (hz₁ : z₁ ∈ W₁) (hd₁ : dg G U z₁ < 6)
    (hsafe₁ : ∀ Y ⊆ W₁.erase z₁, ec G U₁ {t} ≤ rankTerm G U₁ Y {t}) :
    ∃ z₂ ∈ W₂, dg G U z₂ < 6 ∧ FixedOmissionFactor G U W z₁ z₂ := by
  have hs6 := separator_sixes ht h.cardS hdt hs
  obtain ⟨z₂,hz₂,hd₂,hn⟩ := exists_outside_tailMarkers h.swap hi hdf hs6
  have he : df G U (W₂.erase z₂)+(6-(dg G U z₂ : ℤ)) = df G U W₂ :=
    sum_erase_add W₂ (fun y => 6-(dg G U y : ℤ)) hz₂
  have hsafe₂ : ∀ Y ⊆ W₂.erase z₂, ec G U₂ {t} ≤ rankTerm G U₂ Y {t} :=
    fun Y hY => retained_safe_singleton h.swap hi ht (by omega) hY
  refine ⟨z₂,hz₂,hd₂,?_⟩
  by_contra hf
  obtain ⟨a,b,_,hb⟩ := failed_pair_tails h hi hu hdu ht hdt hs hz₁ hz₂ hd₁ hd₂ hsafe₁ hsafe₂ hf
  exact hn (mem_filter.mpr ⟨mem_filter.mpr ⟨hz₂,hd₂⟩,b,hb⟩)

lemma four_marker_safe {U W S U₁ U₂ W₁ W₂ : Finset V} {z t : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (ht : t ∈ S) (hdf : df G U W₁ = 6) (hz : z ∈ W₁) (hdz : dg G U z = 4) :
    ∀ Y ⊆ W₁.erase z, ec G U₁ {t} ≤ rankTerm G U₁ Y {t} := by
  have he : df G U (W₁.erase z)+(6-(dg G U z : ℤ)) = df G U W₁ :=
    sum_erase_add W₁ (fun y => 6-(dg G U y : ℤ)) hz
  intro Y hY
  exact retained_safe_singleton h hi ht (by omega) hY

lemma no_four_six_fives {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ = 6) (hfour : ¬ ∃ z ∈ W₁, dg G U z = 4) :
    (∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6) ∧ #{y ∈ W₁ | dg G U y = 5} = 6 := by
  have hs : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6 := by
    intro y hy
    have hlo := hi.minW y (h.subsets.2.2.1 hy)
    have hup := hi.capW y (h.subsets.2.2.1 hy)
    have hn : dg G U y ≠ 4 := fun he => hfour ⟨y,hy,he⟩
    omega
  have he := QB7MixedOmissionR700.df_five_six hs
  exact ⟨hs,by omega⟩


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

#print axioms assemble_d5_d6
#print axioms assemble_d6_d5
#print axioms four_marker_safe
#print axioms no_four_six_fives
#print axioms original_scar_exists
#print axioms fixed_factor_swap
end Erdos585.QB7S0002R869
