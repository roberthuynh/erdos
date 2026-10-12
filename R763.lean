import R751
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.QB7Reversed0012R763
open QB4 QB7SmallLobeR643 QB7TwoDegreeFourR676 QB7MixedOmissionR700 QB7Separator0111R721 QB7Selector0012R751
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma mixed_failure_scalar {d₁ e₁ b₁ c₁ v₁ d₂ b₂ c₂ v₂ : ℤ}
    (h₁ : MixedBounds d₁ e₁ 2 b₁ c₁ v₁)
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

/-- Original tight imbalance-two support containing all original incidences of Q. -/
structure PortTail (G : SimpleGraph V) [DecidableRel G.Adj]
    (U P K Q : Finset V) where
  X : Finset V
  B : Finset V
  left : X ⊆ P
  right : B ⊆ K
  balance : (#X : ℤ)-#B = 2
  potential : gv G X B = 16
  ports : ec G X Q = 6

lemma original_two_trace_tail {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hdf₁ : df G U W₁ = 5) (hdf₂ : df G U W₂ = 5)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 4) (hd₂ : dg G U z₂ = 5)
    (hY₁ : Y₁ ⊆ W₁.erase z₁) (hY₂ : Y₂ ⊆ W₂.erase z₂)
    (hR : R ⊆ S) (hr : #R = 2)
    (hn : rankTerm G U₁ Y₁ R+rankTerm G U₂ Y₂ R < 8) :
    ∃ t : PortTail G U U₂ W₂ (S \ R), z₂ ∈ t.B ∧ ec G U (S \ R) = 12 := by
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
  have hh := mixed_failure_scalar hb₁ hb₂ (by exact_mod_cast hv₁) (by exact_mod_cast hv₂) hn'
  rcases hh with ⟨hdx₁,heps₁,hbval₁,hport₁,hdx₂,hbval₂,hport₂⟩
  have heps₂ := df_opposite_zero h hi hu hdu hX₂
  have hpot : gv G X₂ B₂ = 16 := by unfold gv; omega
  have hqcap₁ := lobe_pair_cap h hi hdf₁ hQ hq
  have hqcap₂ := lobe_pair_cap h.swap hi hdf₂ hQ hq
  have hp₁ : ec G U₁ Q = 6 := by have := ec_mono_left (G := G) hX₁ Q; omega
  have hp₂ : ec G U₂ Q = 6 := by have := ec_mono_left (G := G) hX₂ Q; omega
  have he := ec_union_left (G := G) h.leftDisjoint Q
  rw [h.leftCover,hp₁,hp₂] at he
  exact ⟨⟨X₂,B₂,hX₂,hB₂,hdx₂,hpot,by simpa [Q] using (show ec G X₂ Q = 6 by omega)⟩,hzB₂,he⟩

lemma PortTail.union {U W S U₁ U₂ W₁ W₂ Q : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ = 5) (hQ : Q ⊆ S) (hq : #Q = 2)
    (t t' : PortTail G U U₁ W₁ Q) :
    ∃ j : PortTail G U U₁ W₁ Q, j.X = t.X ∪ t'.X ∧ j.B = t.B ∪ t'.B := by
  have hcap := lobe_pair_cap h hi hdf hQ hq
  have hju : t.X ∪ t'.X ⊆ U₁ := union_subset t.left t'.left
  have hji : t.B ∪ t'.B ⊆ W₁ := union_subset t.right t'.right
  have hiu : t.X ∩ t'.X ⊆ U₁ := inter_subset_left.trans t.left
  have hii : t.B ∩ t'.B ⊆ W₁ := inter_subset_left.trans t.right
  have hem := ec_left_union_inter (G := G) t.X t'.X Q
  have heu := (ec_mono_left (G := G) hju Q).trans hcap
  have hei := (ec_mono_left (G := G) hiu Q).trans hcap
  rw [t.ports,t'.ports] at hem
  have hpi : ec G (t.X ∩ t'.X) Q = 6 := by omega
  have hpj : ec G (t.X ∪ t'.X) Q = 6 := by omega
  have heprod := ec_product_bound (G := G) (t.X ∩ t'.X) Q
  rw [hpi,hq] at heprod
  have hxi : 3 ≤ #(t.X ∩ t'.X) := by omega
  have hxt := card_le_card (inter_subset_left : t.X ∩ t'.X ⊆ t.X)
  have hxj := card_le_card (subset_union_left : t.X ⊆ t.X ∪ t'.X)
  have hbj := card_le_card (subset_union_left : t.B ⊆ t.B ∪ t'.B)
  have hbal := t.balance
  have hfj := h.local_floor hi hju (hji.trans subset_union_left) (by omega)
  have hsub := gv_union_add_gv_inter_le (G := G) t.X t'.X t.B t'.B
  rw [t.potential,t'.potential] at hsub
  have hni : 4 ≤ #(t.X ∩ t'.X)+#(t.B ∩ t'.B) := by
    by_contra hn
    have hz : #(t.B ∩ t'.B) = 0 := by omega
    have hx : #(t.X ∩ t'.X) = 3 := by omega
    have hempty := card_eq_zero.mp hz
    have h18 : gv G (t.X ∩ t'.X) (t.B ∩ t'.B) = 18 := by
      simp [gv,hempty,ec,dg,hx]
    omega
  have hfi := h.local_floor hi hiu (hii.trans subset_union_left) hni
  have htj : gv G (t.X ∪ t'.X) (t.B ∪ t'.B) = 16 := by omega
  have hti : gv G (t.X ∩ t'.X) (t.B ∩ t'.B) = 16 := by omega
  have hbj2 := tight_balance_le_two hi (hju.trans h.subsets.1) (hji.trans h.subsets.2.2.1) htj
  have hbi2 := tight_balance_le_two hi (hiu.trans h.subsets.1) (hii.trans h.subsets.2.2.1) hti
  have hxcard := card_union_add_card_inter t.X t'.X
  have hbcard := card_union_add_card_inter t.B t'.B
  have hbal' := t'.balance
  have hbalance : (#(t.X ∪ t'.X) : ℤ)-#(t.B ∪ t'.B) = 2 := by omega
  exact ⟨⟨t.X ∪ t'.X,t.B ∪ t'.B,hju,hji,hbalance,htj,hpj⟩,rfl,rfl⟩

lemma PortTail.marker_bound {U W S U₁ U₂ W₁ W₂ Q : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (_hi : U2Input G U W)
    (hw : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6)
    (t : PortTail G U U₁ W₁ Q) : #{y ∈ t.B | dg G U y = 5} ≤ 2 := by
  have hd := df_five_six (fun y hy => hw y (t.right hy))
  have hm := ec_mono_left (G := G) (t.left.trans h.subsets.1) t.B
  have he := df_eq (G := G) U t.B
  rw [ec_comm t.B U] at he
  have hp := t.potential
  have hb := t.balance
  unfold gv at hp
  omega

lemma failed_pair_port_tail {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hdf₁ : df G U W₁ = 5) (hdf₂ : df G U W₂ = 5)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 4) (hd₂ : dg G U z₂ = 5)
    (hfail : ¬ FixedOmissionFactor G U W z₁ z₂) :
    ∃ t : PortTail G U U₂ W₂ (S.filter fun s => dg G U s = 6), z₂ ∈ t.B := by
  have he₁ : df G U (W₁.erase z₁)+(6-(dg G U z₁ : ℤ)) = df G U W₁ :=
    sum_erase_add W₁ (fun y => 6-(dg G U y : ℤ)) hz₁
  have he₂ : df G U (W₂.erase z₂)+(6-(dg G U z₂ : ℤ)) = df G U W₂ :=
    sum_erase_add W₂ (fun y => 6-(dg G U y : ℤ)) hz₂
  have hb₁ : df G U (W₁.erase z₁) ≤ 3 := by rw [hd₁,hdf₁] at he₁; omega
  have hb₂ : df G U (W₂.erase z₂) ≤ 4 := by rw [hd₂,hdf₂] at he₂; omega
  obtain ⟨Y₁,Y₂,R,hY₁,hY₂,hR,hneg⟩ := failed_pair_rank_cut h hi hz₁ hz₂ hfail
  have hrmax : #R ≤ 4 := by have := card_le_card hR; rw [h.cardS] at this; exact this
  by_cases hrlo : #R ≤ 1
  · have := mixed_low_rank h.swap hi hb₂ hb₁ hY₂ hY₁ hR hrlo
    omega
  by_cases hr2 : #R = 2
  · obtain ⟨t,ht,he⟩ := original_two_trace_tail h hi hu hdu hdf₁ hdf₂
      hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR hr2 (by omega)
    have hq : #(S \ R) = 2 := by
      have hc := card_sdiff_add_card_eq_card hR
      rw [h.cardS,hr2] at hc
      omega
    have hQeq := saturated_pair_unique hi h.separator hs6 sdiff_subset hq he
    rw [← hQeq]
    exact ⟨t,ht⟩
  by_cases hr3 : #R = 3
  · have hd := card_sdiff_add_card_eq_card hR
    have hdiffone : #(S \ R) = 1 := by rw [h.cardS] at hd; omega
    obtain ⟨s,hsing⟩ := card_eq_one.mp hdiffone
    have hss : s ∈ S := (mem_sdiff.mp (show s ∈ S \ R by rw [hsing]; simp)).1
    have hReq : R = S.erase s := by
      have he := Finset.sdiff_sdiff_eq_self hR
      rw [hsing] at he
      simpa only [sdiff_singleton_eq_erase] using he.symm
    have hfirst := h.rank_erase_port_six hi hz₁ hss (by omega) hY₁
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

/-- At most two original degree-five choices in the unscarred lobe fail against
one fixed original degree-four vertex in the scarred lobe. The conclusion
uses actual unit-edge factors on every retained original vertex. -/
theorem original_selector0012_at_most_two
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c : #{y ∈ W₂ | dg G U y = 5} = 5)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c₄ : #{y ∈ W₁ | dg G U y = 4} = 1)
    (hw₁c₅ : #{y ∈ W₁ | dg G U y = 5} = 3)
    (hz₁ : z₁ ∈ W₁) (hd₁ : dg G U z₁ = 4) :
    #{z ∈ W₂ | dg G U z = 5 ∧ ¬ FixedOmissionFactor G U W z₁ z} ≤ 2 := by
  classical
  have hi' := U2Input.of_original hi
  have hdf₂ : df G U W₂ = 5 := by rw [df_five_six hw₂,hw₂c]; norm_num
  have hdf₁ : df G U W₁ = 5 := by rw [df_four_five_six hw₁,hw₁c₄,hw₁c₅]; norm_num
  by_contra hn
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := two_lt_card_iff.mp (by omega :
    2 < #{z ∈ W₂ | dg G U z = 5 ∧ ¬ FixedOmissionFactor G U W z₁ z})
  rcases mem_filter.mp ha with ⟨haW,haD,haF⟩
  rcases mem_filter.mp hb with ⟨hbW,hbD,hbF⟩
  rcases mem_filter.mp hc with ⟨hcW,hcD,hcF⟩
  obtain ⟨ta,hta⟩ := failed_pair_port_tail h hi' hu hdu hdf₁ hdf₂ hs6 hz₁ haW hd₁ haD haF
  obtain ⟨tb,htb⟩ := failed_pair_port_tail h hi' hu hdu hdf₁ hdf₂ hs6 hz₁ hbW hd₁ hbD hbF
  obtain ⟨tc,htc⟩ := failed_pair_port_tail h hi' hu hdu hdf₁ hdf₂ hs6 hz₁ hcW hd₁ hcD hcF
  obtain ⟨tab,_,htab⟩ := ta.union h.swap hi' hdf₂ (filter_subset _ _) hs6 tb
  obtain ⟨tabc,_,htabc⟩ := tab.union h.swap hi' hdf₂ (filter_subset _ _) hs6 tc
  have hbound := tabc.marker_bound h.swap hi' hw₂
  have hsub : {a,b,c} ⊆ tabc.B.filter (fun z => dg G U z = 5) := by
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
theorem original_selector0012_at_least_three
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c : #{y ∈ W₂ | dg G U y = 5} = 5)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c₄ : #{y ∈ W₁ | dg G U y = 4} = 1)
    (hw₁c₅ : #{y ∈ W₁ | dg G U y = 5} = 3)
    (hz₁ : z₁ ∈ W₁) (hd₁ : dg G U z₁ = 4) :
    3 ≤ #{z ∈ W₂ | dg G U z = 5 ∧ FixedOmissionFactor G U W z₁ z} := by
  classical
  have hb := original_selector0012_at_most_two hi h hu hdu hs6 hw₂ hw₂c hw₁ hw₁c₄ hw₁c₅ hz₁ hd₁
  have he := card_filter_add_card_filter_not
    (s := W₂.filter fun z => dg G U z = 5) (fun z => FixedOmissionFactor G U W z₁ z)
  simp only [filter_filter] at he
  omega

/-- The literal original 0012 target B interface. Size and separator profile
premises are retained here exactly; the stronger theorem above needs only the
saturated pair count and derives all cuts without a successful choice premise. -/
theorem original_selector0012_targetB
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (_hn₁ : 5 ≤ #U₁) (_hn₂ : 6 ≤ #U₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (_hs : ∀ s ∈ S, dg G U s = 4 ∨ dg G U s = 5 ∨ dg G U s = 6)
    (_hs4 : #{s ∈ S | dg G U s = 4} = 1)
    (_hs5 : #{s ∈ S | dg G U s = 5} = 1)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c : #{y ∈ W₂ | dg G U y = 5} = 5)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c₄ : #{y ∈ W₁ | dg G U y = 4} = 1)
    (hw₁c₅ : #{y ∈ W₁ | dg G U y = 5} = 3)
    (hz₁ : z₁ ∈ W₁) (hd₁ : dg G U z₁ = 4) :
    #{z ∈ W₂ | dg G U z = 5 ∧ ¬ FixedOmissionFactor G U W z₁ z} ≤ 2 ∧
    3 ≤ #{z ∈ W₂ | dg G U z = 5 ∧ FixedOmissionFactor G U W z₁ z} :=
  ⟨original_selector0012_at_most_two hi h hu hdu hs6 hw₂ hw₂c hw₁ hw₁c₄ hw₁c₅ hz₁ hd₁,
   original_selector0012_at_least_three hi h hu hdu hs6 hw₂ hw₂c hw₁ hw₁c₄ hw₁c₅ hz₁ hd₁⟩


#print axioms mixed_failure_scalar
#print axioms original_two_trace_tail
#print axioms PortTail.union
#print axioms failed_pair_port_tail
#print axioms original_selector0012_at_most_two
#print axioms original_selector0012_at_least_three
#print axioms original_selector0012_targetB
end Erdos585.QB7Reversed0012R763
