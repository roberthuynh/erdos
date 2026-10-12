/-
R827 formalization of the R803 residual2332/4332 selector.
Attribution: imports R806 physical ThreeTail union, marker bound and ten-trace
original-cut helpers; R751/R700 original mixed-cut support bounds are transitive.
New content: cap-five/cap-seven residual classification from original aug floor.
No R806 allocation3331/3333 endpoint is used as a premise. All factors use
original unit edges, with no temporary completion or scar-edge units.
-/
import R806
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.QB7ResidualThreePortR827
open QB4 QB7SmallLobeR643 QB7TwoDegreeFourR676 QB7MixedOmissionR700 QB7Separator0111R721 QB7Selector0012R751 QB7ThreePortR806
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Cap-five/cap-seven classification uses the ORIGINAL augmented support floor,
already paid by MixedBounds.aug. This is the R803 residual allocation step. -/
lemma residual_nonnegative {d e m b c v : ℤ}
    (h : MixedBounds d e m b c v) (hv : v ≤ 5) (hm : m = 1) : 0 ≤ c := by
  subst m
  rcases h with ⟨he,he',hvn,hc,hcap,hs,hz,ho,hf,ha⟩
  have hd : d ≤ -1 ∨ d = 0 ∨ d = 1 ∨ d = 2 ∨ 3 ≤ d := by omega
  rcases hd with hd|hd|hd|hd|hd
  all_goals try have hf' := hf (by omega)
  all_goals try have ha' := ha (by omega)
  all_goals omega

lemma residual_clean_nonnegative {d b c v : ℤ}
    (h : MixedBounds d 0 2 b c v) (hv : v ≤ 7) : 0 ≤ c := by
  rcases h with ⟨he,he',hvn,hc,hcap,hs,hz,ho,hf,ha⟩
  have hd : d ≤ -1 ∨ d = 0 ∨ d = 1 ∨ d = 2 ∨ 3 ≤ d := by omega
  rcases hd with hd|hd|hd|hd|hd
  all_goals try have ha' := ha (by omega)
  all_goals omega

lemma residual_failure_scalar {d₁ e₁ b₁ c₁ v₁ d₂ b₂ c₂ v₂ : ℤ}
    (h₁ : MixedBounds d₁ e₁ 1 b₁ c₁ v₁)
    (h₂ : MixedBounds d₂ 0 2 b₂ c₂ v₂)
    (hv₁ : v₁ ≤ 6) (hv₂ : v₂ ≤ 7) (hv : v₁+v₂ ≤ 12)
    (hn : c₁+c₂ < 0) :
    d₁ = 2 ∧ e₁ = 1 ∧ b₁ = 5 ∧ v₁ = 6 ∧ d₂ = 2 ∧ b₂ = 6 ∧ v₂ = 6 := by
  have hc₂ := residual_clean_nonnegative h₂ hv₂
  have hv₁' : v₁ = 6 := by
    by_contra hne
    have hc₁ := residual_nonnegative h₁ (by omega) rfl
    omega
  exact QB7ThreePortR806.mixed_failure_scalar h₁ h₂ hv₁ (by omega) hn

lemma original_two_trace_tail {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hdf₁ : df G U W₁ = 5)
    (hcap₂ : ∀ Q ⊆ S, #Q = 2 → ec G U₂ Q ≤ 7)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 5) (hd₂ : dg G U z₂ = 4)
    (hY₁ : Y₁ ⊆ W₁.erase z₁) (hY₂ : Y₂ ⊆ W₂.erase z₂)
    (hR : R ⊆ S) (hr : #R = 2)
    (hn : rankTerm G U₁ Y₁ R+rankTerm G U₂ Y₂ R < 8) :
    ∃ t : QB7ThreePortR806.PortTail G U U₁ W₁ (S \ R) u0, z₁ ∈ t.B ∧ ec G U (S \ R) = 12 := by
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
  rw [hd₁] at hb₁
  rw [hd₂,df_opposite_zero h hi hu hdu hX₂] at hb₂
  norm_num only at hb₁ hb₂
  have hv₁ := (ec_mono_left (G := G) hX₁ Q).trans (lobe_pair_cap h hi hdf₁ hQ hq)
  have hv₂ := (ec_mono_left (G := G) hX₂ Q).trans (hcap₂ Q hQ hq)
  have hc₁ := local_cost_of_partition h hi (hY₁.trans (erase_subset z₁ W₁)) hR hX₁ he₁
  have hc₂ := local_cost_of_partition h.swap hi (hY₂.trans (erase_subset z₂ W₂)) hR hX₂ he₂
  have hn' : cutCost G W X₁ B₁ Q+cutCost G W X₂ B₂ Q < 0 := by dsimp [B₁,B₂,Q]; omega
  have htotal : ec G X₁ Q+ec G X₂ Q ≤ 12 := by
    have hem := ec_union_left (G := G) h.leftDisjoint Q
    rw [h.leftCover] at hem
    have hwhole : ec G U Q ≤ 12 := by
      rw [ec_comm]; unfold ec
      calc (∑ q ∈ Q, dg G U q) ≤ ∑ _q ∈ Q, 6 :=
          sum_le_sum fun q hq' => hi.capW q (h.separator (hQ hq'))
        _ = 12 := by simp [hq]
    have hm₁ := ec_mono_left (G := G) hX₁ Q
    have hm₂ := ec_mono_left (G := G) hX₂ Q
    omega
  have hh := residual_failure_scalar hb₁ hb₂ (by exact_mod_cast hv₁)
    (by exact_mod_cast hv₂) (by exact_mod_cast htotal) hn'
  rcases hh with ⟨hdx₁,heps₁,hbval₁,hport₁,hdx₂,hbval₂,hport₂⟩
  have hscar := (original_scarred_vertex hi (hX₁.trans h.subsets.1) (h.subsets.1 hu) hdu).2 heps₁
  have hpot : gv G X₁ B₁ = 16 := by unfold gv; omega
  have hqcap₁ := lobe_pair_cap h hi hdf₁ hQ hq
  have hqcap₂ := hcap₂ Q hQ hq
  have hp₁ : ec G U₁ Q = 6 := by have := ec_mono_left (G := G) hX₁ Q; omega
  have hp₂ : ec G U₂ Q = 6 := by
    have hm := ec_mono_left (G := G) hX₂ Q
    have hewhole := ec_union_left (G := G) h.leftDisjoint Q
    rw [h.leftCover,hp₁] at hewhole
    have hwhole : ec G U Q ≤ 12 := by
      rw [ec_comm]; unfold ec
      calc (∑ q ∈ Q, dg G U q) ≤ ∑ _q ∈ Q, 6 :=
          sum_le_sum fun q hq' => hi.capW q (h.separator (hQ hq'))
        _ = 12 := by simp [hq]
    omega
  have he := ec_union_left (G := G) h.leftDisjoint Q
  rw [h.leftCover,hp₁,hp₂] at he
  exact ⟨⟨X₁,B₁,hX₁,hB₁,hscar,hdx₁,hpot,by simpa [Q] using (show ec G X₁ Q = 6 by omega)⟩,hzB₁,he⟩

lemma failed_pair_port_tail {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hdf₁ : df G U W₁ = 5) (hdf₂ : df G U W₂ = 6)
    (hcap₂ : ∀ Q ⊆ S, #Q = 2 → ec G U₂ Q ≤ 7)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 5) (hd₂ : dg G U z₂ = 4)
    (hfail : ¬ FixedOmissionFactor G U W z₁ z₂) :
    ∃ t : ThreeTail G U U₁ W₁ S u0, z₁ ∈ t.tail.B := by
  have he₁ : df G U (W₁.erase z₁)+(6-(dg G U z₁ : ℤ)) = df G U W₁ :=
    sum_erase_add W₁ (fun y => 6-(dg G U y : ℤ)) hz₁
  have he₂ : df G U (W₂.erase z₂)+(6-(dg G U z₂ : ℤ)) = df G U W₂ :=
    sum_erase_add W₂ (fun y => 6-(dg G U y : ℤ)) hz₂
  have hb₁ : df G U (W₁.erase z₁) ≤ 4 := by rw [hd₁,hdf₁] at he₁; omega
  have hb₂ : df G U (W₂.erase z₂) ≤ 4 := by rw [hd₂,hdf₂] at he₂; omega
  obtain ⟨Y₁,Y₂,R,hY₁,hY₂,hR,hneg⟩ := failed_pair_rank_cut h hi hz₁ hz₂ hfail
  have hrmax : #R ≤ 4 := by have := card_le_card hR; rw [h.cardS] at this; exact this
  by_cases hrlo : #R ≤ 1
  · have := retained_four_low_rank h hi hb₁ hb₂ hY₁ hY₂ hR hrlo
    omega
  by_cases hr2 : #R = 2
  · obtain ⟨t,ht,he⟩ := original_two_trace_tail h hi hu hdu hdf₁ hcap₂
      hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR hr2 (by omega)
    have hq : #(S \ R) = 2 := by
      have hc := card_sdiff_add_card_eq_card hR
      rw [h.cardS,hr2] at hc
      omega
    have hid := df_eq (G := G) U (S \ R)
    rw [ec_comm (S \ R) U,he,hq] at hid
    have hz : df G U (S \ R) = 0 := by omega
    have hQsat : S \ R ⊆ S.filter (fun s => dg G U s = 6) := by
      intro s hs
      exact mem_filter.mpr ⟨(mem_sdiff.mp hs).1,
        dg_eq_six_of_df_eq_zero
          (fun x hx => hi.capW x (h.separator (mem_sdiff.mp hx).1)) hz hs⟩
    exact ⟨⟨S \ R,hQsat,hq,t⟩,ht⟩
  by_cases hr3 : #R = 3
  · have hd := card_sdiff_add_card_eq_card hR
    have hdiffone : #(S \ R) = 1 := by rw [h.cardS] at hd; omega
    obtain ⟨s,hsing⟩ := card_eq_one.mp hdiffone
    have hss : s ∈ S := (mem_sdiff.mp (show s ∈ S \ R by rw [hsing]; simp)).1
    have hReq : R = S.erase s := by
      have he := Finset.sdiff_sdiff_eq_self hR
      rw [hsing] at he
      simpa only [sdiff_singleton_eq_erase] using he.symm
    have hfirst := h.rank_erase_port_six hi hz₁ hss hb₁ hY₁
    have hsecond := h.swap.rank_erase_port_six hi hz₂ hss (by omega) hY₂
    rw [← hReq] at hfirst hsecond
    omega
  · have hr4 : #R = 4 := by omega
    have hReq : R = S := eq_of_subset_of_card_le hR (by rw [h.cardS]; omega)
    have hfirst := h.rank_full hi hz₁ (by omega) hY₁
    have hsecond := h.swap.rank_full hi hz₂ (by omega) hY₂
    rw [← hReq] at hfirst hsecond
    omega

attribute [local instance] Classical.propDecidable

/-- At most two original degree-five choices in the scarred lobe fail against
one fixed original degree-four vertex in the opposite lobe. The conclusion
uses actual unit-edge factors on every retained original vertex. -/
theorem original_selector_three_port_at_most_two
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₂ : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs6 : #{s ∈ S | dg G U s = 6} = 3)
    (hcap₂ : ∀ Q ⊆ S, #Q = 2 → ec G U₂ Q ≤ 7)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c : #{y ∈ W₁ | dg G U y = 5} = 5)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c₄ : #{y ∈ W₂ | dg G U y = 4} = 1)
    (hw₂c₅ : #{y ∈ W₂ | dg G U y = 5} = 4)
    (hz₂ : z₂ ∈ W₂) (hd₂ : dg G U z₂ = 4) :
    #{z ∈ W₁ | dg G U z = 5 ∧ ¬ FixedOmissionFactor G U W z z₂} ≤ 2 := by
  classical
  have hi' := U2Input.of_original hi
  have hdf₁ : df G U W₁ = 5 := by rw [df_five_six hw₁,hw₁c]; norm_num
  have hdf₂ : df G U W₂ = 6 := by rw [df_four_five_six hw₂,hw₂c₄,hw₂c₅]; norm_num
  by_contra hn
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := two_lt_card_iff.mp (by omega :
    2 < #{z ∈ W₁ | dg G U z = 5 ∧ ¬ FixedOmissionFactor G U W z z₂})
  rcases mem_filter.mp ha with ⟨haW,haD,haF⟩
  rcases mem_filter.mp hb with ⟨hbW,hbD,hbF⟩
  rcases mem_filter.mp hc with ⟨hcW,hcD,hcF⟩
  obtain ⟨ta,hta⟩ := failed_pair_port_tail h hi' hu hdu hdf₁ hdf₂ hcap₂ haW hz₂ haD hd₂ haF
  obtain ⟨tb,htb⟩ := failed_pair_port_tail h hi' hu hdu hdf₁ hdf₂ hcap₂ hbW hz₂ hbD hd₂ hbF
  obtain ⟨tc,htc⟩ := failed_pair_port_tail h hi' hu hdu hdf₁ hdf₂ hcap₂ hcW hz₂ hcD hd₂ hcF
  obtain ⟨tab,_,htab⟩ := ta.union h hi' hdf₁ hs6 tb
  obtain ⟨tabc,_,htabc⟩ := tab.union h hi' hdf₁ hs6 tc
  have hbound := tabc.tail.marker_bound h hi' hw₁
  have hsub : {a,b,c} ⊆ tabc.tail.B.filter (fun z => dg G U z = 5) := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl|rfl
    · exact mem_filter.mpr ⟨by rw [htabc,htab]; exact mem_union_left _ (mem_union_left _ hta),haD⟩
    · exact mem_filter.mpr ⟨by rw [htabc,htab]; exact mem_union_left _ (mem_union_right _ htb),hbD⟩
    · exact mem_filter.mpr ⟨by rw [htabc]; exact mem_union_right _ htc,hcD⟩
  have hthree : #({a,b,c} : Finset V) = 3 := by simp [hab,hac,hbc]
  have hh := card_le_card hsub
  omega

/-- At least three original degree-five choices have actual original quartics,
each retaining every vertex other than its own fixed omission pair. -/
theorem original_selector_three_port_at_least_three
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₂ : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs6 : #{s ∈ S | dg G U s = 6} = 3)
    (hcap₂ : ∀ Q ⊆ S, #Q = 2 → ec G U₂ Q ≤ 7)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c : #{y ∈ W₁ | dg G U y = 5} = 5)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c₄ : #{y ∈ W₂ | dg G U y = 4} = 1)
    (hw₂c₅ : #{y ∈ W₂ | dg G U y = 5} = 4)
    (hz₂ : z₂ ∈ W₂) (hd₂ : dg G U z₂ = 4) :
    3 ≤ #{z ∈ W₁ | dg G U z = 5 ∧ FixedOmissionFactor G U W z z₂} := by
  classical
  have hb := original_selector_three_port_at_most_two hi h hu hdu hs6 hcap₂ hw₁ hw₁c hw₂ hw₂c₄ hw₂c₅ hz₂ hd₂
  have he := card_filter_add_card_filter_not
    (s := W₁.filter fun z => dg G U z = 5) (fun z => FixedOmissionFactor G U W z z₂)
  simp only [filter_filter] at he
  omega



/-- The literal 4332 side has cap seven on every physical two-port set. -/
lemma residual_pair_cap {P S Q : Finset V} {a : V}
    (ha : dg G P a = 4) (ho : ∀ s ∈ S, s ≠ a → dg G P s ≤ 3)
    (hQ : Q ⊆ S) (hq : #Q = 2) : ec G P Q ≤ 7 := by
  rw [ec_comm]; unfold ec
  by_cases haQ : a ∈ Q
  · have he := sum_erase_add Q (dg G P) haQ
    have hb : ∑ s ∈ Q.erase a, dg G P s ≤ 3 := by
      calc _ ≤ ∑ _s ∈ Q.erase a, 3 := sum_le_sum fun s hs =>
          ho s (hQ (mem_erase.mp hs).2) (mem_erase.mp hs).1
        _ = 3 := by have hc := card_erase_add_one haQ; rw [hq] at hc; simp; omega
    omega
  · calc _ ≤ ∑ _s ∈ Q, 3 := sum_le_sum fun s hs =>
          ho s (hQ hs) (fun hsa => haQ (hsa ▸ hs))
      _ ≤ 7 := by simp [hq]

/-- Exact R803 allocation2332/4332. Every hypothesis concerns the
original graph; sizes and all incidences are retained in this literal interface. -/
theorem original_selector_residual_three_port_target
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₂ a b c t : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (_hn₁ : 6 ≤ #U₁) (_hn₂ : 6 ≤ #U₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hS : S = {a,b,c,t})
    (hs : dg G U a = 6 ∧ dg G U b = 6 ∧ dg G U c = 6 ∧ dg G U t = 4)
    (_halloc₁ : dg G U₁ a = 2 ∧ dg G U₁ b = 3 ∧ dg G U₁ c = 3 ∧ dg G U₁ t = 2)
    (halloc₂ : dg G U₂ a = 4 ∧ dg G U₂ b = 3 ∧ dg G U₂ c = 3 ∧ dg G U₂ t = 2)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c : #{y ∈ W₁ | dg G U y = 5} = 5)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c₄ : #{y ∈ W₂ | dg G U y = 4} = 1)
    (hw₂c₅ : #{y ∈ W₂ | dg G U y = 5} = 4)
    (hz₂ : z₂ ∈ W₂) (hd₂ : dg G U z₂ = 4) :
    #{z ∈ W₁ | dg G U z = 5 ∧ ¬ FixedOmissionFactor G U W z z₂} ≤ 2 ∧
    3 ≤ #{z ∈ W₁ | dg G U z = 5 ∧ FixedOmissionFactor G U W z z₂} := by
  have hfilter : S.filter (fun s => dg G U s = 6) = S.erase t := by
    ext s
    simp only [mem_filter,mem_erase]
    constructor
    · rintro ⟨hsS,hs6⟩
      refine ⟨?_,hsS⟩
      intro hst
      subst s
      omega
    · rintro ⟨hst,hsS⟩
      refine ⟨hsS,?_⟩
      rw [hS] at hsS
      simp only [mem_insert,mem_singleton] at hsS
      rcases hsS with rfl|rfl|rfl|rfl
      · exact hs.1
      · exact hs.2.1
      · exact hs.2.2.1
      · exact False.elim (hst rfl)
  have ht : t ∈ S := by rw [hS]; simp
  have hs6 : #{s ∈ S | dg G U s = 6} = 3 := by
    rw [hfilter]
    have hc := card_erase_add_one ht
    rw [h.cardS] at hc
    omega
  have hother : ∀ s ∈ S, s ≠ a → dg G U₂ s ≤ 3 := by
    intro s hsS hsa
    rw [hS] at hsS
    simp only [mem_insert,mem_singleton] at hsS
    rcases hsS with rfl|rfl|rfl|rfl
    · exact False.elim (hsa rfl)
    · omega
    · omega
    · omega
  have hcap₂ : ∀ Q ⊆ S, #Q = 2 → ec G U₂ Q ≤ 7 := by
    intro Q hQ hq
    exact residual_pair_cap halloc₂.1 hother hQ hq
  exact ⟨original_selector_three_port_at_most_two hi h hu hdu hs6 hcap₂
      hw₁ hw₁c hw₂ hw₂c₄ hw₂c₅ hz₂ hd₂,
    original_selector_three_port_at_least_three hi h hu hdu hs6 hcap₂
      hw₁ hw₁c hw₂ hw₂c₄ hw₂c₅ hz₂ hd₂⟩

/-- Literal raw caller: three fixed omissions have one physical original edge set
each. All original U and all unomitted W have degree four; both omissions have
zero factor degree, explicitly derived from the support condition. -/
theorem original_selector_residual_three_port_raw
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₂ a b c t : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hn₁ : 6 ≤ #U₁) (hn₂ : 6 ≤ #U₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hS : S = {a,b,c,t})
    (hs : dg G U a = 6 ∧ dg G U b = 6 ∧ dg G U c = 6 ∧ dg G U t = 4)
    (halloc₁ : dg G U₁ a = 2 ∧ dg G U₁ b = 3 ∧ dg G U₁ c = 3 ∧ dg G U₁ t = 2)
    (halloc₂ : dg G U₂ a = 4 ∧ dg G U₂ b = 3 ∧ dg G U₂ c = 3 ∧ dg G U₂ t = 2)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c : #{y ∈ W₁ | dg G U y = 5} = 5)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c₄ : #{y ∈ W₂ | dg G U y = 4} = 1)
    (hw₂c₅ : #{y ∈ W₂ | dg G U y = 5} = 4)
    (hz₂ : z₂ ∈ W₂) (hd₂ : dg G U z₂ = 4) :
    ∃ Z : Finset V, 3 ≤ #Z ∧ Z ⊆ W₁.filter (fun z => dg G U z = 5) ∧
      ∀ z₁ ∈ Z, ∃ F : Finset (V × V), F ⊆ U ×ˢ (W.erase z₁ |>.erase z₂) ∧
        (∀ e ∈ F, G.Adj e.1 e.2) ∧
        (∀ x ∈ U, #{e ∈ F | e.1 = x} = 4) ∧
        (∀ y ∈ (W.erase z₁ |>.erase z₂), #{e ∈ F | e.2 = y} = 4) ∧
        #{e ∈ F | e.2 = z₁} = 0 ∧ #{e ∈ F | e.2 = z₂} = 0 := by
  have hh := original_selector_residual_three_port_target hi h hn₁ hn₂ hu hdu
    hS hs halloc₁ halloc₂ hw₁ hw₁c hw₂ hw₂c₄ hw₂c₅ hz₂ hd₂
  let Z := W₁.filter (fun z => dg G U z = 5 ∧ FixedOmissionFactor G U W z z₂)
  refine ⟨Z,hh.2,?_,?_⟩
  · intro z hz
    rcases mem_filter.mp hz with ⟨hzW,hzD,hzF⟩
    exact mem_filter.mpr ⟨hzW,hzD⟩
  · intro z₁ hz₁
    obtain ⟨F,hF,hAdj,hLeft,hRight⟩ := (mem_filter.mp hz₁).2.2
    refine ⟨F,hF,hAdj,hLeft,hRight,?_,?_⟩
    · apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      intro e he heq
      have hy := (mem_product.mp (hF he)).2
      have hy' := (mem_erase.mp hy).2
      exact (mem_erase.mp hy').1 heq
    · apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      intro e he heq
      have hy := (mem_product.mp (hF he)).2
      exact (mem_erase.mp hy).1 heq

#print axioms residual_clean_nonnegative
#print axioms residual_failure_scalar
#print axioms original_two_trace_tail
#print axioms failed_pair_port_tail
#print axioms original_selector_residual_three_port_target
#print axioms original_selector_residual_three_port_raw
end Erdos585.QB7ResidualThreePortR827
