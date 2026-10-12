/- R883 full S0001 production.  -/
import R869.Main
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Finset
namespace Erdos585.QB7S0001R883
open QB4 QB7SmallLobeR643 QB7TwoDegreeFourR676 QB7MixedOmissionR700
  QB7Separator0111R721 QB7Selector0012R751 QB7ProfileFreeR854
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

/-- The summed original allowance is sufficient; no individual cap-seven premise. -/
lemma full_allowance_failure {d₁ e₁ m₁ b₁ c₁ v₁ d₂ m₂ b₂ c₂ v₂ : ℤ}
    (h₁ : MixedBounds d₁ e₁ m₁ b₁ c₁ v₁)
    (h₂ : MixedBounds d₂ 0 m₂ b₂ c₂ v₂)
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (hv : v₁+v₂ ≤ 12)
    (hn : c₁+c₂ < 0) :
    d₁ = 2 ∧ e₁ = 1 ∧ b₁ = 5 ∧ v₁ = 6 ∧ d₂ = 2 ∧ b₂ = 6 ∧ v₂ = 6 := by
  have hd1 : d₁ ≤ -1 ∨ d₁ = 0 ∨ d₁ = 1 ∨ d₁ = 2 ∨ 3 ≤ d₁ := by omega
  have hd2 : d₂ ≤ -1 ∨ d₂ = 0 ∨ d₂ = 1 ∨ d₂ = 2 ∨ 3 ≤ d₂ := by omega
  rcases h₁ with ⟨he1,he1',hv1,hc1,hcap1,hs1,hz1,ho1,hf1,ha1⟩
  rcases h₂ with ⟨he2,he2',hv2,hc2,hcap2,hs2,hz2,ho2,hf2,ha2⟩
  rcases hd1 with hd1|hd1|hd1|hd1|hd1 <;>
    rcases hd2 with hd2|hd2|hd2|hd2|hd2
  all_goals try have hz1' := hz1 (by omega)
  all_goals try have ho1' := ho1 (by omega)
  all_goals try have hf1' := hf1 (by omega)
  all_goals try have ha1' := ha1 (by omega)
  all_goals try have hz2' := hz2 (by omega)
  all_goals try have ho2' := ho2 (by omega)
  all_goals try have hf2' := hf2 (by omega)
  all_goals try have ha2' := ha2 (by omega)
  all_goals try omega

lemma full_two_trace_tails {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6)
    (hY₁ : Y₁ ⊆ W₁.erase z₁) (hY₂ : Y₂ ⊆ W₂.erase z₂)
    (hR : R ⊆ S) (hr : #R = 2)
    (hn : rankTerm G U₁ Y₁ R+rankTerm G U₂ Y₂ R < 8) :
    ∃ t₁ : PortTail G U U₁ W₁ (S \ R),
    ∃ t₂ : PortTail G U U₂ W₂ (S \ R),
      u0 ∈ t₁.X ∧ z₁ ∈ t₁.B ∧ z₂ ∈ t₂.B ∧ ec G U (S \ R) = 12 ∧
      ec G U₁ (S \ R) = 6 ∧ ec G U₂ (S \ R) = 6 := by
  obtain ⟨X₁,hX₁,he₁⟩ := capped_partition (G := G) U₁ (Y₁ ∪ R)
  obtain ⟨X₂,hX₂,he₂⟩ := capped_partition (G := G) U₂ (Y₂ ∪ R)
  let B₁ := W₁ \ Y₁
  let B₂ := W₂ \ Y₂
  let Q := S \ R
  have hB₁ : B₁ ⊆ W₁ := sdiff_subset
  have hB₂ : B₂ ⊆ W₂ := sdiff_subset
  have hQ : Q ⊆ S := sdiff_subset
  have hq : #Q = 2 := by
    have hc := card_sdiff_add_card_eq_card hR
    rw [h.cardS,hr] at hc
    dsimp [Q]; omega
  have hzB₁ : z₁ ∈ B₁ := mem_sdiff.mpr ⟨hz₁,fun hh => (mem_erase.mp (hY₁ hh)).1 rfl⟩
  have hzB₂ : z₂ ∈ B₂ := mem_sdiff.mpr ⟨hz₂,fun hh => (mem_erase.mp (hY₂ hh)).1 rfl⟩
  have hb₁ := original_mixed_bounds h hi hX₁ hB₁ hzB₁ hQ hq
  have hb₂ := original_mixed_bounds h.swap hi hX₂ hB₂ hzB₂ hQ hq
  rw [df_opposite_zero h hi hu hdu hX₂] at hb₂
  have hcap : ec G U Q ≤ 12 := by
    rw [ec_comm]; unfold ec
    calc (∑ s ∈ Q, dg G U s) ≤ ∑ _s ∈ Q, 6 :=
          sum_le_sum fun s hs => hi.capW s (h.separator (hQ hs))
      _ = 12 := by simp [hq]
  have hv : (ec G X₁ Q : ℤ)+ec G X₂ Q ≤ 12 := by
    have he := ec_union_left (G := G) h.leftDisjoint Q
    rw [h.leftCover] at he
    have hm₁ := ec_mono_left (G := G) hX₁ Q
    have hm₂ := ec_mono_left (G := G) hX₂ Q
    omega
  have hc₁ := local_cost_of_partition h hi (hY₁.trans (erase_subset z₁ W₁)) hR hX₁ he₁
  have hc₂ := local_cost_of_partition h.swap hi (hY₂.trans (erase_subset z₂ W₂)) hR hX₂ he₂
  have hn' : cutCost G W X₁ B₁ Q+cutCost G W X₂ B₂ Q < 0 := by dsimp [B₁,B₂,Q]; omega
  have hh := full_allowance_failure hb₁ hb₂ (by omega) (by omega) hv hn'
  rcases hh with ⟨hdx₁,heps₁,hbval₁,hport₁,hdx₂,hbval₂,hport₂⟩
  have hscar := (original_scarred_vertex hi (hX₁.trans h.subsets.1) (h.subsets.1 hu) hdu).2 heps₁
  have heps₂ := df_opposite_zero h hi hu hdu hX₂
  have hpot₁ : gv G X₁ B₁ = 16 := by unfold gv; omega
  have hpot₂ : gv G X₂ B₂ = 16 := by unfold gv; omega
  have he : ec G U Q = 12 := by
    have he := ec_union_left (G := G) h.leftDisjoint Q
    rw [h.leftCover] at he
    have hm₁ := ec_mono_left (G := G) hX₁ Q
    have hm₂ := ec_mono_left (G := G) hX₂ Q
    omega
  have hp₁ : ec G U₁ Q = 6 := by
    have he := ec_union_left (G := G) h.leftDisjoint Q
    rw [h.leftCover] at he
    have hm₁ := ec_mono_left (G := G) hX₁ Q
    have hm₂ := ec_mono_left (G := G) hX₂ Q
    omega
  have hp₂ : ec G U₂ Q = 6 := by
    have hec := ec_union_left (G := G) h.leftDisjoint Q
    rw [h.leftCover] at hec
    omega
  exact ⟨⟨X₁,B₁,hX₁,hB₁,hdx₁,hpot₁,by simpa [Q] using (show ec G X₁ Q = 6 by omega)⟩,
    ⟨X₂,B₂,hX₂,hB₂,hdx₂,hpot₂,by simpa [Q] using (show ec G X₂ Q = 6 by omega)⟩,
    hscar,hzB₁,hzB₂,he,hp₁,hp₂⟩

lemma separator_deficiency {U S : Finset V} {t : V}
    (ht : t ∈ S) (hdt : dg G U t = 5)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6) : df G U S = 1 := by
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
    (ht : t ∈ S) (hc : #S = 4) (hdt : dg G U t = 5)
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
    (ht : t ∈ S) (hdt : dg G U t = 5)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6) :
    5 ≤ df G U W₁ ∧ 5 ≤ df G U W₂ ∧
    df G U W₁ + df G U W₂ = 12 ∧ df G U W₁ ≤ 7 ∧ df G U W₂ ≤ 7 := by
  have hds := separator_deficiency ht hdt hs
  have hd := hi.defW
  unfold df at hd
  rw [← h.rightCover,sum_union (show Disjoint (W₁ ∪ W₂) S from disjoint_union_left.mpr ⟨h.rightSep₁,h.rightSep₂⟩),
    sum_union h.rightDisjoint] at hd
  change df G U W₁+df G U W₂+df G U S = 13 at hd
  have h₁ := h.interior_scar hi
  have h₂ := h.swap.interior_scar hi
  exact ⟨h₁,h₂,by omega,by omega,by omega⟩

lemma saturated_low_rank {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hb₁ : df G U (W₁.erase z₁) ≤ 6) (hb₂ : df G U (W₂.erase z₂) ≤ 6)
    (hbs : df G U (W₁.erase z₁)+df G U (W₂.erase z₂) ≤ 10)
    (hs : ∀ s ∈ R, 6 ≤ dg G U s)
    (hY₁ : Y₁ ⊆ W₁.erase z₁) (hY₂ : Y₂ ⊆ W₂.erase z₂)
    (hR : R ⊆ S) (hr : #R ≤ 1) :
    4*(#R : ℤ) ≤ rankTerm G U₁ Y₁ R+rankTerm G U₂ Y₂ R := by
  have hd₁ := df_le_of_subset (G := G) hY₁
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))
  have hd₂ := df_le_of_subset (G := G) hY₂
    (fun y hy => hi.capW y (h.subsets.2.2.2 (mem_erase.mp hy).2))
  have hfirst := h.capped_rank_lower hi (hY₁.trans (erase_subset z₁ W₁)) hR
  have hsecond := h.swap.capped_rank_lower hi (hY₂.trans (erase_subset z₂ W₂)) hR
  have hm : max 0 (df G U Y₁+2*#R-6)+max 0 (df G U Y₂+2*#R-6) ≤ 2*(#R : ℤ) := by
    by_cases h₁ : df G U Y₁+2*#R-6 ≤ 0 <;>
      by_cases h₂ : df G U Y₂+2*#R-6 ≤ 0
    · rw [max_eq_left h₁,max_eq_left h₂]; omega
    · rw [max_eq_left h₁,max_eq_right (by omega : 0 ≤ df G U Y₂+2*#R-6)]; omega
    · rw [max_eq_right (by omega : 0 ≤ df G U Y₁+2*#R-6),max_eq_left h₂]; omega
    · rw [max_eq_right (by omega : 0 ≤ df G U Y₁+2*#R-6),
        max_eq_right (by omega : 0 ≤ df G U Y₂+2*#R-6)]; omega
  have he := ec_union_left (G := G) h.leftDisjoint R
  rw [h.leftCover] at he
  have hmin : 6*#R ≤ ec G U R := by
    rw [ec_comm]; unfold ec
    calc 6*#R = ∑ _s ∈ R, 6 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun s hsR => hs s hsR
  omega

lemma full_failed_pair_tails {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ z₂ t : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (ht : t ∈ S) (hdt : dg G U t = 5)
    (hs : ∀ s ∈ S, s ≠ t → dg G U s = 6)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6)
    (hsingleton : ∀ Y₁ ⊆ W₁.erase z₁, ∀ Y₂ ⊆ W₂.erase z₂,
      4 ≤ rankTerm G U₁ Y₁ {t} + rankTerm G U₂ Y₂ {t})
    (hfail : ¬ FixedOmissionFactor G U W z₁ z₂) :
    ∃ Q ⊆ S.filter (fun s => dg G U s = 6), #Q = 2 ∧
      ∃ a : PortTail G U U₁ W₁ Q, ∃ b : PortTail G U U₂ W₂ Q,
        z₁ ∈ a.B ∧ z₂ ∈ b.B ∧ ec G U₁ Q = 6 ∧ ec G U₂ Q = 6 := by
  have hd := interior_deficiencies h hi ht hdt hs
  have he₁ : df G U (W₁.erase z₁)+(6-(dg G U z₁ : ℤ)) = df G U W₁ :=
    sum_erase_add W₁ (fun y => 6-(dg G U y : ℤ)) hz₁
  have he₂ : df G U (W₂.erase z₂)+(6-(dg G U z₂ : ℤ)) = df G U W₂ :=
    sum_erase_add W₂ (fun y => 6-(dg G U y : ℤ)) hz₂
  have hb₁ : df G U (W₁.erase z₁) ≤ 6 := by omega
  have hb₂ : df G U (W₂.erase z₂) ≤ 6 := by omega
  have hbs : df G U (W₁.erase z₁)+df G U (W₂.erase z₂) ≤ 10 := by omega
  obtain ⟨Y₁,Y₂,R,hY₁,hY₂,hR,hneg⟩ := failed_pair_rank_cut h hi hz₁ hz₂ hfail
  have hrmax : #R ≤ 4 := by have := card_le_card hR; rw [h.cardS] at this; exact this
  by_cases hrlo : #R ≤ 1
  · by_cases htr : t ∈ R
    · have hReq : R = {t} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr htr) (by simpa)).symm
      have hh := hsingleton Y₁ hY₁ Y₂ hY₂
      rw [hReq] at hneg
      simp only [card_singleton,Nat.cast_one] at hneg
      omega
    · have hmin : ∀ s ∈ R, 6 ≤ dg G U s := by
        intro s hss
        have hst : s ≠ t := by intro hh; subst s; exact htr hss
        rw [hs s (hR hss) hst]
      have hh := saturated_low_rank h hi hb₁ hb₂ hbs hmin hY₁ hY₂ hR hrlo
      omega
  by_cases hr2 : #R = 2
  · obtain ⟨a,b,_,ha,hb,he,hp₁,hp₂⟩ := full_two_trace_tails h hi hu hdu
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
    exact ⟨S \ R,hsub,hq,a,b,ha,hb,hp₁,hp₂⟩
  by_cases hr3 : #R = 3
  · have := three_rank h hi hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR hr3
    omega
  · have hr4 : #R = 4 := by omega
    have hReq : R = S := eq_of_subset_of_card_le hR (by rw [h.cardS]; omega)
    have hfirst := h.rank_full hi hz₁ (by omega) hY₁
    have hsecond := h.swap.rank_full hi hz₂ (by omega) hY₂
    rw [← hReq] at hfirst hsecond
    omega


#print axioms full_two_trace_tails
#print axioms full_failed_pair_tails
end Erdos585.QB7S0001R883
