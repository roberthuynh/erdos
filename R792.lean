import R763
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.QB7AllFive0012R792
open QB4 QB7SmallLobeR643 QB7TwoDegreeFourR676 QB7MixedOmissionR700 QB7Separator0111R721 QB7Selector0012R751
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma allfive_failure_scalar {d₁ e₁ b₁ c₁ v₁ d₂ b₂ c₂ v₂ : ℤ}
    (h₁ : MixedBounds d₁ e₁ 1 b₁ c₁ v₁)
    (h₂ : MixedBounds d₂ 0 1 b₂ c₂ v₂)
    (hv₁ : v₁ ≤ 6) (hv₂ : v₂ ≤ 6) (hn : c₁+c₂ < 0) :
    d₁ = 2 ∧ e₁ = 1 ∧ b₁ = 5 ∧ v₁ = 6 ∧ d₂ = 2 ∧ b₂ = 6 ∧ v₂ = 6 := by
  rcases h₁ with ⟨he1,he1',hv1,hc1,hcap1,hs1,hz1,ho1,hf1,ha1⟩
  rcases h₂ with ⟨_,_,hv2,hc2,hcap2,hs2,hz2,ho2,hf2,ha2⟩
  have hd1 : d₁ ≤ -1 ∨ d₁ = 0 ∨ d₁ = 1 ∨ 2 ≤ d₁ := by omega
  have hd2 : d₂ ≤ -1 ∨ d₂ = 0 ∨ d₂ = 1 ∨ 2 ≤ d₂ := by omega
  rcases hd1 with hd1|hd1|hd1|hd1 <;> rcases hd2 with hd2|hd2|hd2|hd2
  all_goals try have hz1' := hz1 hd1
  all_goals try have ho1' := ho1 hd1
  all_goals try have hf1' := hf1 hd1
  all_goals try have ha1' := ha1 (by omega)
  all_goals try have hz2' := hz2 hd2
  all_goals try have ho2' := ho2 hd2
  all_goals try have hf2' := hf2 hd2
  all_goals try have ha2' := ha2 (by omega)
  all_goals omega

lemma allfive_two_trace_tails {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hdf₁ : df G U W₁ = 5) (hdf₂ : df G U W₂ = 5)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 5) (hd₂ : dg G U z₂ = 5)
    (hY₁ : Y₁ ⊆ W₁.erase z₁) (hY₂ : Y₂ ⊆ W₂.erase z₂)
    (hR : R ⊆ S) (hr : #R = 2)
    (hn : rankTerm G U₁ Y₁ R+rankTerm G U₂ Y₂ R < 8) :
    ∃ t : PortTail G U U₁ W₁ (S \ R) u0, ∃ t' : QB7Reversed0012R763.PortTail G U U₂ W₂ (S \ R),
      z₁ ∈ t.B ∧ z₂ ∈ t'.B ∧ ec G U (S \ R) = 12 := by
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
  have hv₂ := (ec_mono_left (G := G) hX₂ Q).trans (lobe_pair_cap h.swap hi hdf₂ hQ hq)
  have hc₁ := local_cost_of_partition h hi (hY₁.trans (erase_subset z₁ W₁)) hR hX₁ he₁
  have hc₂ := local_cost_of_partition h.swap hi (hY₂.trans (erase_subset z₂ W₂)) hR hX₂ he₂
  have hn' : cutCost G W X₁ B₁ Q+cutCost G W X₂ B₂ Q < 0 := by dsimp [B₁,B₂,Q]; omega
  have hh := allfive_failure_scalar hb₁ hb₂ (by exact_mod_cast hv₁) (by exact_mod_cast hv₂) hn'
  rcases hh with ⟨hdx₁,heps₁,hbval₁,hport₁,hdx₂,hbval₂,hport₂⟩
  have hscar := (original_scarred_vertex hi (hX₁.trans h.subsets.1) (h.subsets.1 hu) hdu).2 heps₁
  have hpot : gv G X₁ B₁ = 16 := by unfold gv; omega
  have hqcap₁ := lobe_pair_cap h hi hdf₁ hQ hq
  have hqcap₂ := lobe_pair_cap h.swap hi hdf₂ hQ hq
  have hp₁ : ec G U₁ Q = 6 := by have := ec_mono_left (G := G) hX₁ Q; omega
  have hp₂ : ec G U₂ Q = 6 := by have := ec_mono_left (G := G) hX₂ Q; omega
  have he := ec_union_left (G := G) h.leftDisjoint Q
  rw [h.leftCover,hp₁,hp₂] at he
  have heps₂ := df_opposite_zero h hi hu hdu hX₂
  have hpot₂ : gv G X₂ B₂ = 16 := by unfold gv; omega
  exact ⟨⟨X₁,B₁,hX₁,hB₁,hscar,hdx₁,hpot,by simpa [Q] using (show ec G X₁ Q = 6 by omega)⟩,⟨X₂,B₂,hX₂,hB₂,hdx₂,hpot₂,by simpa [Q] using (show ec G X₂ Q = 6 by omega)⟩,hzB₁,hzB₂,he⟩

lemma allfive_failed_pair_tails {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hdf₁ : df G U W₁ = 5) (hdf₂ : df G U W₂ = 5)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 5) (hd₂ : dg G U z₂ = 5)
    (hfail : ¬ FixedOmissionFactor G U W z₁ z₂) :
    ∃ t : PortTail G U U₁ W₁ (S.filter fun s => dg G U s = 6) u0,
    ∃ t' : QB7Reversed0012R763.PortTail G U U₂ W₂ (S.filter fun s => dg G U s = 6),
      z₁ ∈ t.B ∧ z₂ ∈ t'.B := by
  have he₁ : df G U (W₁.erase z₁)+(6-(dg G U z₁ : ℤ)) = df G U W₁ :=
    sum_erase_add W₁ (fun y => 6-(dg G U y : ℤ)) hz₁
  have he₂ : df G U (W₂.erase z₂)+(6-(dg G U z₂ : ℤ)) = df G U W₂ :=
    sum_erase_add W₂ (fun y => 6-(dg G U y : ℤ)) hz₂
  have hb₁ : df G U (W₁.erase z₁) ≤ 4 := by rw [hd₁,hdf₁] at he₁; omega
  have hb₂ : df G U (W₂.erase z₂) ≤ 4 := by rw [hd₂,hdf₂] at he₂; omega
  obtain ⟨Y₁,Y₂,R,hY₁,hY₂,hR,hneg⟩ := failed_pair_rank_cut h hi hz₁ hz₂ hfail
  have hrmax : #R ≤ 4 := by have := card_le_card hR; rw [h.cardS] at this; exact this
  by_cases hrlo : #R ≤ 1
  · have := deficient_low_rank h hi hb₁ hb₂ hY₁ hY₂ hR hrlo
    omega
  by_cases hr2 : #R = 2
  · obtain ⟨t,t',ht,ht',he⟩ := allfive_two_trace_tails h hi hu hdu hdf₁ hdf₂
      hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR hr2 (by omega)
    have hq : #(S \ R) = 2 := by
      have hc := card_sdiff_add_card_eq_card hR
      rw [h.cardS,hr2] at hc
      omega
    have hQeq := saturated_pair_unique hi h.separator hs6 sdiff_subset hq he
    rw [← hQeq]
    exact ⟨t,t',ht,ht'⟩
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

/-- A bound on the union of all physical certificates, not just one certificate. -/
lemma marker_family_bound {T : Type*} (K : Finset V) (B : T → Finset V)
    (pred : V → Prop)
    (hunion : ∀ t t', ∃ j, B j = B t ∪ B t')
    (hbound : ∀ t, #{z ∈ B t | pred z} ≤ 2) :
    #{z ∈ K | pred z ∧ ∃ t, z ∈ B t} ≤ 2 := by
  classical
  by_contra hn
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := two_lt_card_iff.mp (by omega :
    2 < #{z ∈ K | pred z ∧ ∃ t, z ∈ B t})
  rcases mem_filter.mp ha with ⟨_,haP,ta,hta⟩
  rcases mem_filter.mp hb with ⟨_,hbP,tb,htb⟩
  rcases mem_filter.mp hc with ⟨_,hcP,tc,htc⟩
  obtain ⟨tab,htab⟩ := hunion ta tb
  obtain ⟨tabc,htabc⟩ := hunion tab tc
  have hsub : {a,b,c} ⊆ (B tabc).filter pred := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl|rfl
    · exact mem_filter.mpr ⟨by rw [htabc,htab]; exact mem_union_left _ (mem_union_left _ hta),haP⟩
    · exact mem_filter.mpr ⟨by rw [htabc,htab]; exact mem_union_left _ (mem_union_right _ htb),hbP⟩
    · exact mem_filter.mpr ⟨by rw [htabc]; exact mem_union_right _ htc,hcP⟩
  have hthree : #({a,b,c} : Finset V) = 3 := by simp [hab,hac,hbc]
  have hh := card_le_card hsub
  have hh' := hbound tabc
  have heq : ((B tabc).filter pred) = (B tabc).filter (fun z => pred z) := by ext z; simp
  rw [heq] at hh
  omega

/-- All bad original pairs lie in one physical rectangle of size at most four.
The two shore sets depend on G and the original split, not on the marker pair. -/
theorem original_allfive0012_rectangle_enclosure
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c : #{y ∈ W₁ | dg G U y = 5} = 5)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c : #{y ∈ W₂ | dg G U y = 5} = 5) :
    ∃ A₁ A₂ : Finset V,
      A₁ ⊆ W₁.filter (fun z => dg G U z = 5) ∧
      A₂ ⊆ W₂.filter (fun z => dg G U z = 5) ∧ #A₁ ≤ 2 ∧ #A₂ ≤ 2 ∧
      ∀ z₁ ∈ W₁, ∀ z₂ ∈ W₂, dg G U z₁ = 5 → dg G U z₂ = 5 →
        ¬ FixedOmissionFactor G U W z₁ z₂ → z₁ ∈ A₁ ∧ z₂ ∈ A₂ := by
  classical
  have hi' := U2Input.of_original hi
  have hdf₁ : df G U W₁ = 5 := by rw [df_five_six hw₁,hw₁c]; norm_num
  have hdf₂ : df G U W₂ = 5 := by rw [df_five_six hw₂,hw₂c]; norm_num
  let Q := S.filter (fun s => dg G U s = 6)
  let T₁ := PortTail G U U₁ W₁ Q u0
  let T₂ := QB7Reversed0012R763.PortTail G U U₂ W₂ Q
  let A₁ := W₁.filter (fun z => dg G U z = 5 ∧ ∃ t : T₁, z ∈ t.B)
  let A₂ := W₂.filter (fun z => dg G U z = 5 ∧ ∃ t : T₂, z ∈ t.B)
  have hb₁ : #A₁ ≤ 2 := by
    dsimp only [A₁]
    convert marker_family_bound W₁ (fun t : T₁ => t.B) (fun z => dg G U z = 5) ?_ ?_ using 1
    all_goals try { congr 1; ext z; simp }
    · intro t t'
      obtain ⟨j,_,hj⟩ := t.union h hi' hdf₁ (filter_subset _ _) hs6 t'
      exact ⟨j,hj⟩
    · intro t
      convert t.marker_bound h hi' hw₁ using 1
      congr 1
      ext z
      simp
  have hb₂ : #A₂ ≤ 2 := by
    dsimp only [A₂]
    convert marker_family_bound W₂ (fun t : T₂ => t.B) (fun z => dg G U z = 5) ?_ ?_ using 1
    all_goals try { congr 1; ext z; simp }
    · intro t t'
      obtain ⟨j,_,hj⟩ := t.union h.swap hi' hdf₂ (filter_subset _ _) hs6 t'
      exact ⟨j,hj⟩
    · intro t
      convert t.marker_bound h.swap hi' hw₂ using 1
      congr 1
      ext z
      simp
  refine ⟨A₁,A₂,?_,?_,hb₁,hb₂,?_⟩
  · exact fun z hz => mem_filter.mpr ⟨(mem_filter.mp hz).1,(mem_filter.mp hz).2.1⟩
  · exact fun z hz => mem_filter.mpr ⟨(mem_filter.mp hz).1,(mem_filter.mp hz).2.1⟩
  · intro z₁ hz₁ z₂ hz₂ hd₁ hd₂ hfail
    obtain ⟨t,t',ht,ht'⟩ := allfive_failed_pair_tails h hi' hu hdu hdf₁ hdf₂ hs6 hz₁ hz₂ hd₁ hd₂ hfail
    exact ⟨mem_filter.mpr ⟨hz₁,hd₁,t,ht⟩,mem_filter.mpr ⟨hz₂,hd₂,t',ht'⟩⟩

/-- A fixed original pair is selected before all cuts. At least 21 pairs work,
and each shore has at least three markers working against every opposite marker. -/
theorem original_allfive0012_count
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c : #{y ∈ W₁ | dg G U y = 5} = 5)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c : #{y ∈ W₂ | dg G U y = 5} = 5) :
    21 ≤ #{p ∈ (W₁.filter (fun z => dg G U z = 5)) ×ˢ
      (W₂.filter (fun z => dg G U z = 5)) | FixedOmissionFactor G U W p.1 p.2} ∧
    3 ≤ #{z ∈ W₁ | dg G U z = 5 ∧
      ∀ z' ∈ W₂, dg G U z' = 5 → FixedOmissionFactor G U W z z'} ∧
    3 ≤ #{z ∈ W₂ | dg G U z = 5 ∧
      ∀ z' ∈ W₁, dg G U z' = 5 → FixedOmissionFactor G U W z' z} := by
  classical
  obtain ⟨A₁,A₂,hA₁,hA₂,hb₁,hb₂,hbad⟩ :=
    original_allfive0012_rectangle_enclosure hi h hu hdu hs6 hw₁ hw₁c hw₂ hw₂c
  let M₁ := W₁.filter (fun z => dg G U z = 5)
  let M₂ := W₂.filter (fun z => dg G U z = 5)
  have hbadsub : (M₁ ×ˢ M₂).filter (fun p => ¬ FixedOmissionFactor G U W p.1 p.2) ⊆ A₁ ×ˢ A₂ := by
    intro p hp
    obtain ⟨hpM,hpf⟩ := mem_filter.mp hp
    obtain ⟨hp1,hp2⟩ := mem_product.mp hpM
    have hh := hbad p.1 (mem_filter.mp hp1).1 p.2 (mem_filter.mp hp2).1
      (mem_filter.mp hp1).2 (mem_filter.mp hp2).2 hpf
    exact mem_product.mpr hh
  have hb : #((M₁ ×ˢ M₂).filter (fun p => ¬ FixedOmissionFactor G U W p.1 p.2)) ≤ 4 := by
    have hh := card_le_card hbadsub
    rw [card_product] at hh
    have hm := Nat.mul_le_mul hb₁ hb₂
    omega
  have hc := card_filter_add_card_filter_not (s := M₁ ×ˢ M₂)
    (fun p => FixedOmissionFactor G U W p.1 p.2)
  have htotal : #(M₁ ×ˢ M₂) = 25 := by rw [card_product]; dsimp [M₁,M₂]; rw [hw₁c,hw₂c]
  have hgood₁ : M₁ \ A₁ ⊆ W₁.filter (fun z => dg G U z = 5 ∧
      ∀ z' ∈ W₂, dg G U z' = 5 → FixedOmissionFactor G U W z z') := by
    intro z hz
    obtain ⟨hzM,hzA⟩ := mem_sdiff.mp hz
    obtain ⟨hzW,hzD⟩ := mem_filter.mp hzM
    refine mem_filter.mpr ⟨hzW,hzD,?_⟩
    intro z' hz' hd'
    by_contra hf
    exact hzA (hbad z hzW z' hz' hzD hd' hf).1
  have hgood₂ : M₂ \ A₂ ⊆ W₂.filter (fun z => dg G U z = 5 ∧
      ∀ z' ∈ W₁, dg G U z' = 5 → FixedOmissionFactor G U W z' z) := by
    intro z hz
    obtain ⟨hzM,hzA⟩ := mem_sdiff.mp hz
    obtain ⟨hzW,hzD⟩ := mem_filter.mp hzM
    refine mem_filter.mpr ⟨hzW,hzD,?_⟩
    intro z' hz' hd'
    by_contra hf
    exact hzA (hbad z' hz' z hzW hd' hzD hf).2
  have hc₁ := card_sdiff_add_card_eq_card hA₁
  have hc₂ := card_sdiff_add_card_eq_card hA₂
  have hg₁ := card_le_card hgood₁
  have hg₂ := card_le_card hgood₂
  change #(M₁ \ A₁)+#A₁ = #M₁ at hc₁
  change #(M₂ \ A₂)+#A₂ = #M₂ at hc₂
  have hm₁ : #M₁ = 5 := hw₁c
  have hm₂ : #M₂ = 5 := hw₂c
  refine ⟨?_,by omega,by omega⟩
  have hh : 21 ≤ #((M₁ ×ˢ M₂).filter (fun p => FixedOmissionFactor G U W p.1 p.2)) := by omega
  convert hh using 1

/-- Literal original 0012 all-five caller. The original sparsity floor, every
retained vertex, and original degrees are carried by U2Input/Split. -/
theorem original_allfive0012_target
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (_hn₁ : 6 ≤ #U₁) (_hn₂ : 6 ≤ #U₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (_hs : ∀ s ∈ S, dg G U s = 4 ∨ dg G U s = 5 ∨ dg G U s = 6)
    (_hs4 : #{s ∈ S | dg G U s = 4} = 1)
    (_hs5 : #{s ∈ S | dg G U s = 5} = 1)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c : #{y ∈ W₁ | dg G U y = 5} = 5)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c : #{y ∈ W₂ | dg G U y = 5} = 5) :
    21 ≤ #{p ∈ (W₁.filter (fun z => dg G U z = 5)) ×ˢ
      (W₂.filter (fun z => dg G U z = 5)) | FixedOmissionFactor G U W p.1 p.2} ∧
    3 ≤ #{z ∈ W₁ | dg G U z = 5 ∧
      ∀ z' ∈ W₂, dg G U z' = 5 → FixedOmissionFactor G U W z z'} ∧
    3 ≤ #{z ∈ W₂ | dg G U z = 5 ∧
      ∀ z' ∈ W₁, dg G U z' = 5 → FixedOmissionFactor G U W z' z} :=
  original_allfive0012_count hi h hu hdu hs6 hw₁ hw₁c hw₂ hw₂c

#print axioms allfive_failed_pair_tails
#print axioms marker_family_bound
#print axioms original_allfive0012_rectangle_enclosure
#print axioms original_allfive0012_count
#print axioms original_allfive0012_target
end Erdos585.QB7AllFive0012R792
