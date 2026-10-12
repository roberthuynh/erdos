/- R883 full literal S0001, all interior profiles and lobe allocations. -/
import R883.Global
import R883.Tails
import R883.LocalB
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Finset
namespace Erdos585.QB7S0001R883
open QB4 QB7SmallLobeR643 QB7ProfileFreeR854
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

lemma fixed_factor_of_safe_pair {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ z₂ t : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (ht : t ∈ S) (hdt : dg G U t = 5)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6)
    (hsingleton : ∀ Y₁ ⊆ W₁.erase z₁, ∀ Y₂ ⊆ W₂.erase z₂,
      4 ≤ rankTerm G U₁ Y₁ {t} + rankTerm G U₂ Y₂ {t})
    (hsafe : z₁ ∉ tailMarkers G U U₁ W₁ S ∨ z₂ ∉ tailMarkers G U U₂ W₂ S) :
    FixedOmissionFactor G U W z₁ z₂ := by
  by_contra hf
  obtain ⟨Q,hQ,hq,a,b,ha,hb,hp₁,hp₂⟩ :=
    full_failed_pair_tails h hi hu hdu ht hdt hs hz₁ hz₂ hd₁ hd₂ hsingleton hf
  have ha' : z₁ ∈ tailMarkers G U U₁ W₁ S :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨hz₁,hd₁⟩,
      ⟨Q,hQ,hq,a,captured_of_saturated a hp₁⟩,ha⟩
  have hb' : z₂ ∈ tailMarkers G U U₂ W₂ S :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨hz₂,hd₂⟩,
      ⟨Q,hQ,hq,b,captured_of_saturated b hp₂⟩,hb⟩
  rcases hsafe with hn|hn
  · exact hn ha'
  · exact hn hb'

lemma singleton_incidence_sum {U W S P P' L L' : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hdt : dg G U t = 5) :
    ec G P {t} + ec G P' {t} = 5 := by
  have he := ec_union_left (G := G) h.leftDisjoint ({t} : Finset V)
  rw [h.leftCover,ec_comm] at he
  simpa [ec,hdt] using he.symm

lemma deficient_marker_outside {U W S P P' L L' B : Finset V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hB : B ⊆ L) (hweight : df G U B < df G U L) :
    ∃ z ∈ L, dg G U z < 6 ∧ z ∉ B := by
  by_contra hn
  push Not at hn
  have hsub : deficientMarkers G U L ⊆ B := by
    intro z hz
    exact hn z (mem_filter.mp hz).1 (mem_filter.mp hz).2
  have hd := df_le_of_subset (G := G) hsub
    (fun z hz => hi.capW z (h.subsets.2.2.1 (hB hz)))
  rw [markers_deficiency (fun z hz => hi.capW z (h.subsets.2.2.1 hz))] at hd
  omega

lemma retained_singleton_rank {U W S P P' L L' Y : Finset V} {t z : V} {c : ℤ}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hY : Y ⊆ L.erase z) (hc : 0 ≤ c)
    (hδ : df G U (L.erase z) ≤ 4+c) :
    (ec G P {t} : ℤ)-c ≤ rankTerm G P Y {t} := by
  have hd := (df_le_of_subset (G := G) hY
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))).trans hδ
  have hh := h.capped_rank_lower hi (hY.trans (erase_subset z L)) (singleton_subset_iff.mpr ht)
  have hm : max 0 (df G U Y+2*#({t} : Finset V)-6) ≤ c := by
    simp only [card_singleton]
    exact max_le hc (by omega)
  omega

lemma d7_selected_marker {U W S P P' L L' : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hdt : dg G U t = 5) (hδ : df G U L = 7) :
    ∃ z ∈ L, dg G U z < 6 ∧
      ∀ Y ⊆ L.erase z, (ec G P {t} : ℤ)-1 ≤ rankTerm G P Y {t} := by
  have hB : badSingletonMarkers G U P L t 7 ⊆ L :=
    (filter_subset _ _).trans (filter_subset _ _)
  have hc := singleton_bad_seven_card h hi ht hdt hδ
  have hw := singleton_bad_deficiency h hi ht hδ (by omega)
  obtain ⟨z,hz,hdz,hgood⟩ := deficient_marker_outside h hi hB (by omega)
  refine ⟨z,hz,hdz,?_⟩
  intro Y hY
  have hh := singleton_not_bad_rank hz hdz hgood hY
  norm_num at hh
  omega

lemma d6_selected_marker {U W S P P' L L' : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hs6 : #{s ∈ S | dg G U s = 6} = 3)
    (hq : ec G P {t} ≤ 2) (hδ : df G U L = 6) :
    ∃ z ∈ L, dg G U z < 6 ∧ z ∉ tailMarkers G U P L S ∧
      ∀ Y ⊆ L.erase z, (ec G P {t} : ℤ) ≤ rankTerm G P Y {t} := by
  have hB : badSingletonMarkers G U P L t 6 ⊆ L :=
    (filter_subset _ _).trans (filter_subset _ _)
  have hc := singleton_bad_six_card h hi ht hq hδ
  have hw := singleton_bad_deficiency h hi ht hδ (by omega)
  obtain ⟨z,hz,hdz,hgood⟩ := exists_outside_tailMarkers_union h hi (by omega) hs6 hB (by omega) (by omega)
  have hnot : z ∉ tailMarkers G U P L S ∧ z ∉ badSingletonMarkers G U P L t 6 := by
    simpa only [mem_union,not_or] using hgood
  refine ⟨z,hz,hdz,hnot.1,?_⟩
  intro Y hY
  have hh := singleton_not_bad_rank hz hdz hnot.2 hY
  norm_num at hh
  exact hh

def SelectedPair (G : SimpleGraph V) [DecidableRel G.Adj]
    (U S P P' L L' : Finset V) (t : V) : Prop :=
  ∃ z₁ ∈ L, ∃ z₂ ∈ L', dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
    (∀ Y₁ ⊆ L.erase z₁, ∀ Y₂ ⊆ L'.erase z₂,
      4 ≤ rankTerm G P Y₁ {t} + rankTerm G P' Y₂ {t}) ∧
    (z₁ ∉ tailMarkers G U P L S ∨ z₂ ∉ tailMarkers G U P' L' S)

lemma selected_pair_swap {U S P P' L L' : Finset V} {t : V}
    (h : SelectedPair G U S P P' L L' t) : SelectedPair G U S P' P L' L t := by
  obtain ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,hcut,hsafe⟩ := h
  refine ⟨z₂,hz₂,z₁,hz₁,hd₂,hd₁,?_,hsafe.symm⟩
  intro Y₂ hY₂ Y₁ hY₁
  have hh := hcut Y₁ hY₁ Y₂ hY₂
  omega

lemma selected_d5_d7 {U W S P P' L L' : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hdt : dg G U t = 5)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6)
    (hδ : df G U L = 5) (hδ' : df G U L' = 7) :
    SelectedPair G U S P P' L L' t := by
  have hs6 := separator_sixes ht h.cardS hdt hs
  obtain ⟨z₁,hz₁,hd₁,hn₁⟩ := exists_outside_tailMarkers h hi (by omega) hs6 (by omega)
  obtain ⟨z₂,hz₂,hd₂,hcut₂⟩ := d7_selected_marker h.swap hi ht hdt hδ'
  have he : df G U (L.erase z₁)+(6-(dg G U z₁ : ℤ)) = df G U L :=
    sum_erase_add L (fun y => 6-(dg G U y : ℤ)) hz₁
  have hsum := singleton_incidence_sum h hdt
  refine ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,?_,Or.inl hn₁⟩
  intro Y₁ hY₁ Y₂ hY₂
  have hc₁ := retained_singleton_rank h hi ht hY₁ (show (0 : ℤ) ≤ 0 by omega) (by omega)
  have hc₂ := hcut₂ Y₂ hY₂
  omega

lemma selected_d6_low_first {U W S P P' L L' : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hdt : dg G U t = 5)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6)
    (hδ : df G U L = 6) (hδ' : df G U L' = 6) (hq : ec G P {t} ≤ 2) :
    SelectedPair G U S P P' L L' t := by
  have hs6 := separator_sixes ht h.cardS hdt hs
  obtain ⟨z₁,hz₁,hd₁,hn₁,hcut₁⟩ := d6_selected_marker h hi ht hs6 hq hδ
  obtain ⟨z₂,hz₂,hd₂,_⟩ := exists_outside_tailMarkers h.swap hi (by omega) hs6 (by omega)
  have he : df G U (L'.erase z₂)+(6-(dg G U z₂ : ℤ)) = df G U L' :=
    sum_erase_add L' (fun y => 6-(dg G U y : ℤ)) hz₂
  have hsum := singleton_incidence_sum h hdt
  refine ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,?_,Or.inl hn₁⟩
  intro Y₁ hY₁ Y₂ hY₂
  have hc₁ := hcut₁ Y₁ hY₁
  have hc₂ := retained_singleton_rank h.swap hi ht hY₂ (show (0 : ℤ) ≤ 1 by omega) (by omega)
  omega

lemma select_full_pair {U W S P P' L L' : Finset V} {t : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (ht : t ∈ S) (hdt : dg G U t = 5)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6) :
    SelectedPair G U S P P' L L' t := by
  have hd := interior_deficiencies h hi ht hdt hs
  by_cases h5 : df G U L = 5
  · exact selected_d5_d7 h hi ht hdt hs h5 (by omega)
  by_cases h7 : df G U L = 7
  · exact selected_pair_swap (selected_d5_d7 h.swap hi ht hdt hs (by omega) h7)
  have h6 : df G U L = 6 := by omega
  have h6' : df G U L' = 6 := by omega
  by_cases hq : ec G P {t} ≤ 2
  · exact selected_d6_low_first h hi ht hdt hs h6 h6' hq
  · have hsum := singleton_incidence_sum h hdt
    have hq' : ec G P' {t} ≤ 2 := by omega
    exact selected_pair_swap (selected_d6_low_first h.swap hi ht hdt hs h6' h6 hq')

lemma original_s0001_oriented {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 t : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (ht : t ∈ S) (hdt : dg G U t = 5)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6) :
    ∃ z₁ ∈ W₁, ∃ z₂ ∈ W₂, dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      FixedOmissionFactor G U W z₁ z₂ := by
  obtain ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,hcut,hsafe⟩ := select_full_pair h hi ht hdt hs
  exact ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,
    fixed_factor_of_safe_pair h hi hu hdu ht hdt hs hz₁ hz₂ hd₁ hd₂ hcut hsafe⟩

/-- Full literal S0001 endpoint. The scar location and omissions are derived. -/
theorem original_s0001_exists {U W S U₁ U₂ W₁ W₂ : Finset V}
    (hi : U2Input G U W) (h : Split G U W S U₁ U₂ W₁ W₂)
    (hs : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (hs5 : #{s ∈ S | dg G U s = 5} = 1) :
    ∃ z₁ ∈ W₁, ∃ z₂ ∈ W₂, dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      FixedOmissionFactor G U W z₁ z₂ := by
  obtain ⟨t,hteq⟩ := card_eq_one.mp hs5
  have htf : t ∈ S.filter (fun s => dg G U s = 5) := by rw [hteq]; simp
  obtain ⟨ht,hdt⟩ := mem_filter.mp htf
  have hsat : ∀ s ∈ S, s ≠ t → dg G U s = 6 := by
    intro s hss hst
    rcases hs s hss with hd|hd
    · have hm : s ∈ S.filter (fun s => dg G U s = 5) := mem_filter.mpr ⟨hss,hd⟩
      rw [hteq] at hm
      exact False.elim (hst (mem_singleton.mp hm))
    · exact hd
  obtain ⟨u0,hu,hdu⟩ := QB7S0002R869.original_scar_exists hi
  have hor : u0 ∈ U₁ ∨ u0 ∈ U₂ := by rw [← h.leftCover] at hu; exact mem_union.mp hu
  rcases hor with hu₁|hu₂
  · exact original_s0001_oriented h hi hu₁ hdu ht hdt hsat
  · obtain ⟨z₂,hz₂,z₁,hz₁,hd₂,hd₁,hf⟩ := original_s0001_oriented h.swap hi hu₂ hdu ht hdt hsat
    exact ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,QB7S0002R869.fixed_factor_swap hf⟩

/-- The original public U2Input formulation has the same full fixed-omission factor. -/
theorem original_s0001_raw {U W S U₁ U₂ W₁ W₂ : Finset V}
    (hi : QB7Conditional.U2Input G U W) (h : Split G U W S U₁ U₂ W₁ W₂)
    (hs : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (hs5 : #{s ∈ S | dg G U s = 5} = 1) :
    ∃ z₁ ∈ W₁, ∃ z₂ ∈ W₂, dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      ∃ F : Finset (V × V), F ⊆ U ×ˢ (W.erase z₁ |>.erase z₂) ∧
        (∀ e ∈ F, G.Adj e.1 e.2) ∧
        (∀ x ∈ U, #{e ∈ F | e.1 = x} = 4) ∧
        (∀ y ∈ (W.erase z₁ |>.erase z₂), #{e ∈ F | e.2 = y} = 4) := by
  exact original_s0001_exists (U2Input.of_original hi) h hs hs5

/-- The same original factor is nonempty and is the literal allowed-support Quartic. -/
theorem original_s0001_quartic {U W S U₁ U₂ W₁ W₂ : Finset V}
    (hi : U2Input G U W) (h : Split G U W S U₁ U₂ W₁ W₂)
    (hs : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (hs5 : #{s ∈ S | dg G U s = 5} = 1) : Quartic G U W := by
  obtain ⟨z₁,_,z₂,_,_,_,F,hF,hadj,hFU,hFQ⟩ := original_s0001_exists hi h hs hs5
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

#print axioms original_s0001_exists
#print axioms original_s0001_raw
#print axioms original_s0001_quartic
end Erdos585.QB7S0001R883
