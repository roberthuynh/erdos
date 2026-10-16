/- R869 literal global S0002 assembly. -/
import R869.Tails
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Finset
namespace Erdos585.QB7S0002R869
open QB4 QB7SmallLobeR643 QB7TwoDegreeFourR676 QB7MixedOmissionR700
  QB7Separator0111R721 QB7Selector0012R751 QB7ProfileFreeR854
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

lemma separator_deficiency {U S : Finset V} {t : V}
    (ht : t ∈ S) (hdt : dg G U t = 4)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6) : df G U S = 2 := by
  have he := sum_erase_add S (fun s => 6-(dg G U s : ℤ)) ht
  have hz : ∑ s ∈ S.erase t, (6-(dg G U s : ℤ)) = 0 := by
    apply sum_eq_zero
    intro s hss
    rw [hs s (mem_erase.mp hss).2 (mem_erase.mp hss).1]
    norm_num
  change _ = df G U S at he
  rw [hz,hdt] at he
  omega

lemma separator_sixes {U S : Finset V} {t : V}
    (ht : t ∈ S) (hc : #S = 4) (hdt : dg G U t = 4)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6) : #{s ∈ S | dg G U s = 6} = 3 := by
  have he : S.filter (fun s => dg G U s = 6) = S.erase t := by
    ext s
    simp only [mem_filter,mem_erase]
    constructor
    · rintro ⟨hss,hd⟩
      exact ⟨by intro hh; subst s; omega,hss⟩
    · rintro ⟨hne,hss⟩
      exact ⟨hss,hs s hss hne⟩
  rw [he]
  have hh := card_erase_add_one ht
  omega

lemma interior_deficiencies {U W S U₁ U₂ W₁ W₂ : Finset V} {t : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (ht : t ∈ S) (hdt : dg G U t = 4)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6) :
    5 ≤ df G U W₁ ∧ 5 ≤ df G U W₂ ∧
    df G U W₁ + df G U W₂ = 11 ∧ df G U W₁ ≤ 6 ∧ df G U W₂ ≤ 6 := by
  have hds := separator_deficiency ht hdt hs
  have hd := hi.defW
  unfold df at hd
  rw [← h.rightCover,sum_union (show Disjoint (W₁ ∪ W₂) S from disjoint_union_left.mpr ⟨h.rightSep₁,h.rightSep₂⟩),
    sum_union h.rightDisjoint] at hd
  change df G U W₁+df G U W₂+df G U S = 13 at hd
  have h₁ := h.interior_scar hi
  have h₂ := h.swap.interior_scar hi
  exact ⟨h₁,h₂,by omega,by omega,by omega⟩

lemma retained_safe_singleton {U W S U₁ U₂ W₁ W₂ Y : Finset V} {z t : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (ht : t ∈ S) (hb : df G U (W₁.erase z) ≤ 4)
    (hY : Y ⊆ W₁.erase z) : ec G U₁ {t} ≤ rankTerm G U₁ Y {t} := by
  have hdY := (df_le_of_subset (G := G) hY
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))).trans hb
  have hf := h.capped_rank_lower hi (hY.trans (erase_subset z W₁)) (singleton_subset_iff.mpr ht)
  have he : max 0 (df G U Y+2*#({t} : Finset V)-6) = 0 := by simp only [card_singleton]; omega
  rw [he] at hf
  omega

lemma saturated_low_rank {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hb₁ : df G U (W₁.erase z₁) ≤ 5) (hb₂ : df G U (W₂.erase z₂) ≤ 5)
    (hbs : df G U (W₁.erase z₁)+df G U (W₂.erase z₂) ≤ 9)
    (hs : ∀ s ∈ R, 5 ≤ dg G U s)
    (hY₁ : Y₁ ⊆ W₁.erase z₁) (hY₂ : Y₂ ⊆ W₂.erase z₂)
    (hR : R ⊆ S) (hr : #R ≤ 1) :
    4*(#R : ℤ) ≤ rankTerm G U₁ Y₁ R+rankTerm G U₂ Y₂ R := by
  have hd₁ := df_le_of_subset (G := G) hY₁
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))
  have hd₂ := df_le_of_subset (G := G) hY₂
    (fun y hy => hi.capW y (h.subsets.2.2.2 (mem_erase.mp hy).2))
  have hfirst := h.capped_rank_lower hi (hY₁.trans (erase_subset z₁ W₁)) hR
  have hsecond := h.swap.capped_rank_lower hi (hY₂.trans (erase_subset z₂ W₂)) hR
  have hm : max 0 (df G U Y₁+2*#R-6)+max 0 (df G U Y₂+2*#R-6) ≤ (#R : ℤ) := by
    by_cases h₁ : df G U Y₁+2*#R-6 ≤ 0
    · rw [max_eq_left h₁]
      have h₂ := max_le (show (0 : ℤ) ≤ #R by positivity)
        (show df G U Y₂+2*#R-6 ≤ #R by omega)
      omega
    · rw [max_eq_right (by omega : 0 ≤ df G U Y₁+2*#R-6)]
      have h₂ : df G U Y₂+2*#R-6 ≤ 0 := by omega
      rw [max_eq_left h₂]
      omega
  have he := ec_union_left (G := G) h.leftDisjoint R
  rw [h.leftCover] at he
  have hmin : 5*#R ≤ ec G U R := by
    rw [ec_comm]; unfold ec
    calc 5*#R = ∑ _s ∈ R, 5 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun s hsR => hs s hsR
  omega

lemma failed_pair_tails {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ z₂ t : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (ht : t ∈ S) (hdt : dg G U t = 4)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6)
    (hsafe₁ : ∀ Y ⊆ W₁.erase z₁, ec G U₁ {t} ≤ rankTerm G U₁ Y {t})
    (hsafe₂ : ∀ Y ⊆ W₂.erase z₂, ec G U₂ {t} ≤ rankTerm G U₂ Y {t})
    (hfail : ¬ FixedOmissionFactor G U W z₁ z₂) :
    ∃ a : ThreeTail G U U₁ W₁ S, ∃ b : ThreeTail G U U₂ W₂ S,
      z₁ ∈ a.tail.B ∧ z₂ ∈ b.tail.B := by
  have hd := interior_deficiencies h hi ht hdt hs
  have he₁ : df G U (W₁.erase z₁)+(6-(dg G U z₁ : ℤ)) = df G U W₁ :=
    sum_erase_add W₁ (fun y => 6-(dg G U y : ℤ)) hz₁
  have he₂ : df G U (W₂.erase z₂)+(6-(dg G U z₂ : ℤ)) = df G U W₂ :=
    sum_erase_add W₂ (fun y => 6-(dg G U y : ℤ)) hz₂
  have hb₁ : df G U (W₁.erase z₁) ≤ 5 := by omega
  have hb₂ : df G U (W₂.erase z₂) ≤ 5 := by omega
  have hbs : df G U (W₁.erase z₁)+df G U (W₂.erase z₂) ≤ 9 := by omega
  obtain ⟨Y₁,Y₂,R,hY₁,hY₂,hR,hneg⟩ := failed_pair_rank_cut h hi hz₁ hz₂ hfail
  have hrmax : #R ≤ 4 := by have := card_le_card hR; rw [h.cardS] at this; exact this
  by_cases hrlo : #R ≤ 1
  · by_cases htr : t ∈ R
    · have hReq : R = {t} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr htr) (by simpa)).symm
      have hfirst := hsafe₁ Y₁ hY₁
      have hsecond := hsafe₂ Y₂ hY₂
      have he := ec_union_left (G := G) h.leftDisjoint ({t} : Finset V)
      rw [h.leftCover] at he
      have het : ec G U {t} = 4 := by rw [ec_comm]; simp [ec,hdt]
      rw [hReq] at hneg
      simp only [card_singleton,Nat.cast_one] at hneg
      omega
    · have hmin : ∀ s ∈ R, 5 ≤ dg G U s := by
        intro s hss
        have hst : s ≠ t := by intro hh; subst s; exact htr hss
        rw [hs s (hR hss) hst]
        omega
      have hh := saturated_low_rank h hi hb₁ hb₂ hbs hmin hY₁ hY₂ hR hrlo
      omega
  by_cases hr2 : #R = 2
  · obtain ⟨a,b,_,ha,hb,he,_,_⟩ := original_two_trace_tails h hi hu hdu hd.2.2.2.1 hd.2.2.2.2
      hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR hr2 (by omega)
    have hq : #(S \ R) = 2 := by
      have hc := card_sdiff_add_card_eq_card hR
      rw [h.cardS,hr2] at hc
      omega
    have hsub : S \ R ⊆ S.filter (fun s => dg G U s = 6) := by
      have hid := df_eq (G := G) U (S \ R)
      rw [ec_comm (S \ R) U,he,hq] at hid
      have hz : df G U (S \ R) = 0 := by omega
      intro s hss
      exact mem_filter.mpr ⟨(mem_sdiff.mp hss).1,dg_eq_six_of_df_eq_zero
        (fun x hx => hi.capW x (h.separator (mem_sdiff.mp hx).1)) hz hss⟩
    exact ⟨⟨S \ R,hsub,hq,a⟩,⟨S \ R,hsub,hq,b⟩,ha,hb⟩
  by_cases hr3 : #R = 3
  · have := three_rank h hi hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR hr3
    omega
  · have hr4 : #R = 4 := by omega
    have hReq : R = S := eq_of_subset_of_card_le hR (by rw [h.cardS]; omega)
    have hfirst := h.rank_full hi hz₁ (by omega) hY₁
    have hsecond := h.swap.rank_full hi hz₂ (by omega) hY₂
    rw [← hReq] at hfirst hsecond
    omega

#print axioms interior_deficiencies
#print axioms failed_pair_tails
end Erdos585.QB7S0002R869
