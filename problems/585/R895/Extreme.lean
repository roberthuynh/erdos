/- R895 final literal S0000 endpoint, all deficiency orientations. -/
import R895.Main
import R895.Joint
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Finset
namespace Erdos585.QB7S0000R895
open QB4 QB7SmallLobeR643 QB7ProfileFreeR854 QB7S0002R869
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

lemma low_rank_d5_d8 {U W S P P' L L' : Finset V} {z₁ z₂ : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hs : ∀ s ∈ S, dg G U s = 6)
    (hD : df G U L = 5) (hz₁ : z₁ ∈ L) (hz₂ : z₂ ∈ L')
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6)
    (hgood : z₂ ∉ badJointMarkers G U P' L' S) :
    ∀ Y₁ ⊆ L.erase z₁, ∀ Y₂ ⊆ L'.erase z₂, ∀ R ⊆ S,
      #R ≤ 1 → 4*(#R : ℤ) ≤ rankTerm G P Y₁ R+rankTerm G P' Y₂ R := by
  intro Y₁ hY₁ Y₂ hY₂ R hR hr
  have he : df G U (L.erase z₁)+(6-(dg G U z₁ : ℤ))=df G U L :=
    sum_erase_add L (fun y => 6-(dg G U y : ℤ)) hz₁
  have ha := retained_rank_lower h hi hY₁ hR (show (0:ℤ)≤0 by omega) (by omega)
  have hb := joint_not_bad_rank h.rightSep₂ hz₂ hd₂ hgood hY₂ hR hr
  have hec := ec_union_left (G := G) h.leftDisjoint R
  rw [h.leftCover] at hec
  have hsat : ec G U R = 6*#R := by
    rw [ec_comm]
    unfold ec
    calc _ = ∑ _s ∈ R, 6 := sum_congr rfl fun s hss => hs s (hR hss)
         _ = _ := by simp [mul_comm]
  omega

lemma select_d5_d8 {U W S P P' L L' : Finset V} {u0 : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hu : u0 ∈ P) (hdu : dg G W u0 = 5)
    (hs : ∀ s ∈ S, dg G U s = 6)
    (hD : df G U L=5) (hD' : df G U L'=8) :
    ∃ z₁ ∈ L, ∃ z₂ ∈ L', dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      FixedOmissionFactor G U W z₁ z₂ := by
  have hA : tailMarkers G U P L u0 ⊆ L :=
    (tailMarkers_subset U P L u0).trans (filter_subset _ _)
  have hAm := tailMarkers_deficiency h hi hdu
  obtain ⟨z₁,hz₁,hd₁,hn₁⟩ := deficient_marker_outside h hi hA (by omega)
  have hB : badJointMarkers G U P' L' S ⊆ L' :=
    (filter_subset _ _).trans (filter_subset _ _)
  have hBc := joint_bad_eight_card h.swap hi hs hD'
  have hBm := joint_bad_deficiency h.swap hi hD'
  obtain ⟨z₂,hz₂,hd₂,hn₂⟩ := deficient_marker_outside h.swap hi hB (by omega)
  exact ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,fixed_factor_of_safe_pair h hi hu hdu hz₁ hz₂ hd₁ hd₂
    (low_rank_d5_d8 h hi hs hD hz₁ hz₂ hd₁ hd₂ hn₂) hn₁⟩

lemma select_d8_d5 {U W S P P' L L' : Finset V} {u0 : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hu : u0 ∈ P) (hdu : dg G W u0 = 5)
    (hs : ∀ s ∈ S, dg G U s = 6)
    (hD : df G U L=8) (hD' : df G U L'=5) :
    ∃ z₁ ∈ L, ∃ z₂ ∈ L', dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      FixedOmissionFactor G U W z₁ z₂ := by
  let A := tailMarkers G U P L u0
  let B := badJointMarkers G U P L S
  have hA : A ⊆ L := (tailMarkers_subset U P L u0).trans (filter_subset _ _)
  have hB : B ⊆ L := (filter_subset _ _).trans (filter_subset _ _)
  have hAm : df G U A ≤ 2 := tailMarkers_deficiency h hi hdu
  have hBc := joint_bad_eight_card h hi hs hD
  have hBm := joint_bad_deficiency h hi hD
  change #B ≤ 4 at hBc
  change df G U B=(#B : ℤ) at hBm
  have hABm : df G U (A ∪ B) ≤ 6 := by
    have he := sum_union_inter (s₁ := A) (s₂ := B) (f := fun z => 6-(dg G U z : ℤ))
    change df G U (A ∪ B)+df G U (A ∩ B)=df G U A+df G U B at he
    have hn : 0 ≤ df G U (A ∩ B) := df_nonneg (G := G)
      (fun z hz => hi.capW z (h.subsets.2.2.1 (hA (mem_inter.mp hz).1)))
    omega
  obtain ⟨z₁,hz₁,hd₁,hn₁⟩ := deficient_marker_outside h hi (union_subset hA hB) (by omega)
  have hnot : z₁ ∉ A ∧ z₁ ∉ B := by simpa only [mem_union,not_or] using hn₁
  have hzero : df G U (∅ : Finset V)=0 := by simp [df]
  obtain ⟨z₂,hz₂,hd₂,_⟩ := deficient_marker_outside h.swap hi (empty_subset L') (by omega)
  have hlow := low_rank_d5_d8 h.swap hi hs hD' hz₂ hz₁ hd₂ hd₁ hnot.2
  refine ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,?_⟩
  apply fixed_factor_of_safe_pair h hi hu hdu hz₁ hz₂ hd₁ hd₂ _ hnot.1
  intro Y₁ hY₁ Y₂ hY₂ R hR hr
  have hh := hlow Y₂ hY₂ Y₁ hY₁ R hR hr
  omega

lemma original_s0000_oriented {U W S P P' L L' : Finset V} {u0 : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hu : u0 ∈ P) (hdu : dg G W u0 = 5)
    (hs : ∀ s ∈ S, dg G U s = 6) :
    ∃ z₁ ∈ L, ∃ z₂ ∈ L', dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      FixedOmissionFactor G U W z₁ z₂ := by
  have hd := interior_deficiencies h hi hs
  by_cases h5 : df G U L=5
  · exact select_d5_d8 h hi hu hdu hs h5 (by omega)
  by_cases h8 : df G U L=8
  · exact select_d8_d5 h hi hu hdu hs h8 (by omega)
  exact select_middle h hi hu hdu hs (by omega) (by omega) hd.2.2.1

/-- Every literal S0000 split has one original deficient pair paying every trace. -/
theorem original_s0000_exists {U W S P P' L L' : Finset V}
    (hi : U2Input G U W) (h : Split G U W S P P' L L')
    (hs : ∀ s ∈ S, dg G U s = 6) :
    ∃ z₁ ∈ L, ∃ z₂ ∈ L', dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      FixedOmissionFactor G U W z₁ z₂ := by
  obtain ⟨u0,hu,hdu⟩ := original_scar_exists hi
  have hor : u0 ∈ P ∨ u0 ∈ P' := by rw [← h.leftCover] at hu; exact mem_union.mp hu
  rcases hor with hu₁|hu₂
  · exact original_s0000_oriented h hi hu₁ hdu hs
  · obtain ⟨z₂,hz₂,z₁,hz₁,hd₂,hd₁,hf⟩ := original_s0000_oriented h.swap hi hu₂ hdu hs
    exact ⟨z₁,hz₁,z₂,hz₂,hd₁,hd₂,fixed_factor_swap hf⟩

theorem original_s0000_raw {U W S P P' L L' : Finset V}
    (hi : QB7Conditional.U2Input G U W) (h : Split G U W S P P' L L')
    (hs : ∀ s ∈ S, dg G U s = 6) :
    ∃ z₁ ∈ L, ∃ z₂ ∈ L', dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      ∃ F : Finset (V × V), F ⊆ U ×ˢ (W.erase z₁ |>.erase z₂) ∧
        (∀ e ∈ F, G.Adj e.1 e.2) ∧
        (∀ x ∈ U, #{e ∈ F | e.1 = x} = 4) ∧
        (∀ y ∈ (W.erase z₁ |>.erase z₂), #{e ∈ F | e.2 = y} = 4) := by
  exact original_s0000_exists (U2Input.of_original hi) h hs

theorem original_s0000_quartic {U W S P P' L L' : Finset V}
    (hi : U2Input G U W) (h : Split G U W S P P' L L')
    (hs : ∀ s ∈ S, dg G U s = 6) : Quartic G U W := by
  obtain ⟨z₁,_,z₂,_,_,_,F,hF,hadj,hFU,hFQ⟩ := original_s0000_exists hi h hs
  have hP : P.Nonempty := card_pos.mp (by have hh := h.left_large hi; omega)
  obtain ⟨u,hu⟩ := hP
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

theorem original_s0000_quartic_raw {U W S P P' L L' : Finset V}
    (hi : QB7Conditional.U2Input G U W) (h : Split G U W S P P' L L')
    (hs : ∀ s ∈ S, dg G U s = 6) : Quartic G U W := by
  exact original_s0000_quartic (U2Input.of_original hi) h hs

#print axioms original_s0000_exists
#print axioms original_s0000_raw
#print axioms original_s0000_quartic
#print axioms original_s0000_quartic_raw
end Erdos585.QB7S0000R895
