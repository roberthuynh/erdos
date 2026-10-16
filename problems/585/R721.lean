import R700
set_option autoImplicit false
open Finset
namespace Erdos585.QB7Separator0111R721
open QB4 QB7SmallLobeR643 QB7TwoDegreeFourR676 QB7MixedOmissionR700
lemma five_scalar {d₁ e₁ b₁ c₁ v₁ d₂ e₂ b₂ c₂ v₂ : ℤ}
    (h₁ : MixedBounds d₁ e₁ 1 b₁ c₁ v₁)
    (h₂ : MixedBounds d₂ e₂ 1 b₂ c₂ v₂)
    (he : e₁+e₂ ≤ 1) (hv : v₁+v₂ ≤ 11) : 0 ≤ c₁+c₂ := by
  rcases h₁ with ⟨he1,he1',hv1,hc1,hcap1,hs1,hz1,ho1,hf1,ha1⟩
  rcases h₂ with ⟨he2,he2',hv2,hc2,hcap2,hs2,hz2,ho2,hf2,ha2⟩
  have hd1 : d₁ ≤ -1 ∨ d₁ = 0 ∨ d₁ = 1 ∨ 2 ≤ d₁ := by omega
  have hd2 : d₂ ≤ -1 ∨ d₂ = 0 ∨ d₂ = 1 ∨ 2 ≤ d₂ := by omega
  rcases hd1 with hd1|hd1|hd1|hd1 <;>
    rcases hd2 with hd2|hd2|hd2|hd2
  all_goals try have hz1' := hz1 hd1
  all_goals try have ho1' := ho1 hd1
  all_goals try have hf1' := hf1 hd1
  all_goals try have ha1' := ha1 (by omega)
  all_goals try have hz2' := hz2 hd2
  all_goals try have ho2' := ho2 hd2
  all_goals try have hf2' := hf2 hd2
  all_goals try have ha2' := ha2 (by omega)
  all_goals omega


universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma weaken_deficiency {d eps m b c v : ℤ}
    (h : MixedBounds d eps m b c v) (hm : 1 ≤ m) :
    MixedBounds d eps 1 b c v := by
  rcases h with ⟨he,he',hv,hc,hcap,hs,hz,ho,hf,ha⟩
  exact ⟨he,he',hv,hc,hcap,by omega,hz,ho,hf,ha⟩

lemma deficient_low_rank {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hb₁ : df G U (W₁.erase z₁) ≤ 4) (hb₂ : df G U (W₂.erase z₂) ≤ 4)
    (hY₁ : Y₁ ⊆ W₁.erase z₁) (hY₂ : Y₂ ⊆ W₂.erase z₂)
    (hR : R ⊆ S) (hr : #R ≤ 1) :
    4*(#R : ℤ) ≤ rankTerm G U₁ Y₁ R+rankTerm G U₂ Y₂ R := by
  have hdY₁ := (df_le_of_subset (G := G) hY₁
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))).trans hb₁
  have hdY₂ := (df_le_of_subset (G := G) hY₂
    (fun y hy => hi.capW y (h.subsets.2.2.2 (mem_erase.mp hy).2))).trans hb₂
  have hfirst := h.capped_rank_lower hi (hY₁.trans (erase_subset z₁ W₁)) hR
  have hsecond := h.swap.capped_rank_lower hi (hY₂.trans (erase_subset z₂ W₂)) hR
  have hm₁ : max 0 (df G U Y₁+2*#R-6) = 0 := max_eq_left (by omega)
  have hm₂ : max 0 (df G U Y₂+2*#R-6) = 0 := max_eq_left (by omega)
  rw [hm₁] at hfirst
  rw [hm₂] at hsecond
  have he := ec_union_left (G := G) h.leftDisjoint R
  rw [h.leftCover] at he
  have hmin : 4*#R ≤ ec G U R := by
    rw [ec_comm]
    unfold ec
    calc 4*#R = ∑ _s ∈ R, 4 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun s hs => hi.minW s (h.separator (hR hs))
  omega

lemma deficient_two_rank {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6)
    (hY₁ : Y₁ ⊆ W₁.erase z₁) (hY₂ : Y₂ ⊆ W₂.erase z₂)
    (hR : R ⊆ S) (hr : #R = 2)
    (hs : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (hsc : #{s ∈ S | dg G U s = 5} = 3) :
    8 ≤ rankTerm G U₁ Y₁ R+rankTerm G U₂ Y₂ R := by
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
    dsimp [Q]
    omega
  have hzB₁ : z₁ ∈ B₁ := mem_sdiff.mpr ⟨hz₁,fun hh => (mem_erase.mp (hY₁ hh)).1 rfl⟩
  have hzB₂ : z₂ ∈ B₂ := mem_sdiff.mpr ⟨hz₂,fun hh => (mem_erase.mp (hY₂ hh)).1 rfl⟩
  have hb₁ := original_mixed_bounds h hi hX₁ hB₁ hzB₁ hQ hq
  have hb₂ := original_mixed_bounds h.swap hi hX₂ hB₂ hzB₂ hQ hq
  have hb₁ := weaken_deficiency hb₁ (by omega)
  have hb₂ := weaken_deficiency hb₂ (by omega)
  have heps : df G W X₁+df G W X₂ ≤ 1 := by
    have hd : Disjoint X₁ X₂ := h.leftDisjoint.mono hX₁ hX₂
    have hsub : X₁ ∪ X₂ ⊆ U := union_subset (hX₁.trans h.subsets.1) (hX₂.trans h.subsets.2.1)
    have he := df_le_of_subset (G := G) hsub hi.capU
    unfold df at he
    rw [sum_union hd] at he
    change df G W X₁+df G W X₂ ≤ df G W U at he
    rwa [hi.defU] at he
  have hv : (ec G X₁ Q : ℤ)+ec G X₂ Q ≤ 11 := by
    have he := ec_union_left (G := G) h.leftDisjoint Q
    rw [h.leftCover] at he
    have hm₁ := ec_mono_left (G := G) hX₁ Q
    have hm₂ := ec_mono_left (G := G) hX₂ Q
    have hc := separator_pair_cap h.cardS hs hsc hQ hq
    omega
  have hpos := five_scalar hb₁ hb₂ heps hv
  have hc₁ := local_cost_of_partition h hi (hY₁.trans (erase_subset z₁ W₁)) hR hX₁ he₁
  have hc₂ := local_cost_of_partition h.swap hi (hY₂.trans (erase_subset z₂ W₂)) hR hX₂ he₂
  dsimp [B₁,B₂,Q] at hpos
  omega

lemma original_lobe_port_cap
    {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ = 5) {s : V} (hs : s ∈ S) : dg G U₁ s ≤ 3 := by
  have hsk : s ∉ W₁ := fun hk => disjoint_left.mp h.rightSep₁ hk hs
  have hsub : insert s W₁ ⊆ W₁ ∪ S := by
    intro x hx
    rcases mem_insert.mp hx with rfl|hx
    · exact mem_union_right _ hs
    · exact mem_union_left _ hx
  have hp := h.left_large hi
  have hf := h.local_floor hi (Subset.refl U₁) hsub (by omega)
  have hb := h.local_balance hi
  have hd : df G U₁ W₁ = 5 := by
    have he : df G U₁ W₁ = df G U W₁ := by
      unfold df
      exact sum_congr rfl fun y hy => by rw [h.degree_right hy]
    omega
  have he := df_eq (G := G) U₁ W₁
  have hc := ec_comm (G := G) W₁ U₁
  unfold gv at hf
  rw [card_insert_of_notMem hsk,ec_insert_right hsk] at hf
  omega

/-- Balance, original interior deficiencies and actual two/three separator
incidences are consequences of the literal input; none is an endpoint premise. -/
lemma original_separator_structure
    {U W S U₁ U₂ W₁ W₂ : Finset V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hs : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (hsc : #{s ∈ S | dg G U s = 5} = 3) :
    #U₁ = #W₁+1 ∧ #U₂ = #W₂+1 ∧
    df G U W₁ = 5 ∧ df G U W₂ = 5 ∧
    ∀ s ∈ S, (2 ≤ dg G U₁ s ∧ dg G U₁ s ≤ 3) ∧
      (2 ≤ dg G U₂ s ∧ dg G U₂ s ≤ 3) := by
  have hi' := U2Input.of_original hi
  have hfilter : S.filter (fun s => dg G U s < 6) =
      S.filter (fun s => dg G U s = 5) := by
    apply filter_congr
    intro s hsS
    rcases hs s hsS with hh|hh <;> simp [hh]
  have hthree : 3 ≤ #(S.filter fun s => dg G U s < 6) := by rw [hfilter,hsc]
  have ha := h.three_deficient_accounting hi' hthree
  refine ⟨h.local_balance hi',h.swap.local_balance hi',ha.2.1,ha.2.2.1,?_⟩
  intro s hsS
  have hcap₁ := original_lobe_port_cap h hi' ha.2.1 hsS
  have hcap₂ := original_lobe_port_cap h.swap hi' ha.2.2.1 hsS
  have he := dg_union_of_disjoint (G := G) h.leftDisjoint s
  rw [h.leftCover] at he
  rcases hs s hsS with hh|hh <;> omega

/-- Every originally deficient cross-lobe pair leaves an actual original
unit-edge quartic on every retained vertex, for separator degrees 5,5,5,6. -/
theorem original_separator0111_fixed_omissions
    {U W S U₁ U₂ W₁ W₂ : Finset V} {z₁ z₂ : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hs : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (hsc : #{s ∈ S | dg G U s = 5} = 3)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6) :
    FixedOmissionFactor G U W z₁ z₂ := by
  classical
  have hi' := U2Input.of_original hi
  have hfilter : S.filter (fun s => dg G U s < 6) =
      S.filter (fun s => dg G U s = 5) := by
    apply filter_congr
    intro s hsS
    rcases hs s hsS with hh|hh <;> simp [hh]
  have hthree : 3 ≤ #(S.filter fun s => dg G U s < 6) := by
    rw [hfilter,hsc]
  have hacc := h.three_deficient_accounting hi' hthree
  have he₁ : df G U (W₁.erase z₁)+(6-(dg G U z₁ : ℤ)) = df G U W₁ :=
    sum_erase_add W₁ (fun y => 6-(dg G U y : ℤ)) hz₁
  have he₂ : df G U (W₂.erase z₂)+(6-(dg G U z₂ : ℤ)) = df G U W₂ :=
    sum_erase_add W₂ (fun y => 6-(dg G U y : ℤ)) hz₂
  have hb₁ : df G U (W₁.erase z₁) ≤ 4 := by omega
  have hb₂ : df G U (W₂.erase z₂) ≤ 4 := by omega
  by_contra hfail
  obtain ⟨Y₁,Y₂,R,hY₁,hY₂,hR,hneg⟩ := failed_pair_rank_cut h hi' hz₁ hz₂ hfail
  have hrmax : #R ≤ 4 := by have := card_le_card hR; rw [h.cardS] at this; exact this
  by_cases hrlo : #R ≤ 1
  · have := deficient_low_rank h hi' hb₁ hb₂ hY₁ hY₂ hR hrlo
    omega
  by_cases hr2 : #R = 2
  · have := deficient_two_rank h hi' hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR hr2 hs hsc
    omega
  by_cases hr3 : #R = 3
  · have hd := card_sdiff_add_card_eq_card hR
    have hdiffone : #(S \ R) = 1 := by rw [h.cardS] at hd; omega
    obtain ⟨s,hsing⟩ := card_eq_one.mp hdiffone
    have hss : s ∈ S := (mem_sdiff.mp (show s ∈ S \ R by rw [hsing]; simp)).1
    have hReq : R = S.erase s := by
      have he := Finset.sdiff_sdiff_eq_self hR
      rw [hsing] at he
      simpa only [sdiff_singleton_eq_erase] using he.symm
    have hfirst := h.rank_erase_port_six hi' hz₁ hss hb₁ hY₁
    have hsecond := h.swap.rank_erase_port_six hi' hz₂ hss hb₂ hY₂
    rw [← hReq] at hfirst hsecond
    omega
  · have hr4 : #R = 4 := by omega
    have hReq : R = S := eq_of_subset_of_card_le hR (by rw [h.cardS]; omega)
    have hfirst := h.rank_full hi' hz₁ (by omega) hY₁
    have hsecond := h.swap.rank_full hi' hz₂ (by omega) hY₂
    rw [← hReq] at hfirst hsecond
    omega

#print axioms original_separator0111_fixed_omissions
#print axioms original_separator_structure
#print axioms five_scalar
end Erdos585.QB7Separator0111R721
