import R751
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.QB7ThreePortR806
open QB4 QB7SmallLobeR643 QB7TwoDegreeFourR676 QB7MixedOmissionR700 QB7Separator0111R721 QB7Selector0012R751
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma mixed_failure_scalar {d₁ e₁ b₁ c₁ v₁ d₂ b₂ c₂ v₂ : ℤ}
    (h₁ : MixedBounds d₁ e₁ 1 b₁ c₁ v₁)
    (h₂ : MixedBounds d₂ 0 2 b₂ c₂ v₂)
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
    (U P K Q : Finset V) (u0 : V) where
  X : Finset V
  B : Finset V
  left : X ⊆ P
  right : B ⊆ K
  scar : u0 ∈ X
  balance : (#X : ℤ)-#B = 2
  potential : gv G X B = 16
  ports : ec G X Q = 6

omit [DecidableEq V] in
lemma pair_cap {P S Q : Finset V}
    (hc : ∀ s ∈ S, dg G P s ≤ 3) (hQ : Q ⊆ S) (hq : #Q = 2) : ec G P Q ≤ 6 := by
  rw [ec_comm]
  unfold ec
  calc (∑ s ∈ Q, dg G P s) ≤ ∑ _s ∈ Q, 3 :=
      sum_le_sum fun s hs => hc s (hQ hs)
    _ = 6 := by simp [hq]

lemma original_two_trace_tail {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hdf₁ : df G U W₁ = 5)
    (hcap₂ : ∀ s ∈ S, dg G U₂ s ≤ 3)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 5) (hd₂ : dg G U z₂ = 4)
    (hY₁ : Y₁ ⊆ W₁.erase z₁) (hY₂ : Y₂ ⊆ W₂.erase z₂)
    (hR : R ⊆ S) (hr : #R = 2)
    (hn : rankTerm G U₁ Y₁ R+rankTerm G U₂ Y₂ R < 8) :
    ∃ t : PortTail G U U₁ W₁ (S \ R) u0, z₁ ∈ t.B ∧ ec G U (S \ R) = 12 := by
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
  have hv₂ := (ec_mono_left (G := G) hX₂ Q).trans (pair_cap hcap₂ hQ hq)
  have hc₁ := local_cost_of_partition h hi (hY₁.trans (erase_subset z₁ W₁)) hR hX₁ he₁
  have hc₂ := local_cost_of_partition h.swap hi (hY₂.trans (erase_subset z₂ W₂)) hR hX₂ he₂
  have hn' : cutCost G W X₁ B₁ Q+cutCost G W X₂ B₂ Q < 0 := by dsimp [B₁,B₂,Q]; omega
  have hh := mixed_failure_scalar hb₁ hb₂ (by exact_mod_cast hv₁) (by exact_mod_cast hv₂) hn'
  rcases hh with ⟨hdx₁,heps₁,hbval₁,hport₁,hdx₂,hbval₂,hport₂⟩
  have hscar := (original_scarred_vertex hi (hX₁.trans h.subsets.1) (h.subsets.1 hu) hdu).2 heps₁
  have hpot : gv G X₁ B₁ = 16 := by unfold gv; omega
  have hqcap₁ := lobe_pair_cap h hi hdf₁ hQ hq
  have hqcap₂ := pair_cap hcap₂ hQ hq
  have hp₁ : ec G U₁ Q = 6 := by have := ec_mono_left (G := G) hX₁ Q; omega
  have hp₂ : ec G U₂ Q = 6 := by have := ec_mono_left (G := G) hX₂ Q; omega
  have he := ec_union_left (G := G) h.leftDisjoint Q
  rw [h.leftCover,hp₁,hp₂] at he
  exact ⟨⟨X₁,B₁,hX₁,hB₁,hscar,hdx₁,hpot,by simpa [Q] using (show ec G X₁ Q = 6 by omega)⟩,hzB₁,he⟩

/-- A tight tail with one of the three physical saturated-pair labels. -/
structure ThreeTail (G : SimpleGraph V) [DecidableRel G.Adj]
    (U P K S : Finset V) (u0 : V) where
  Q : Finset V
  subset : Q ⊆ S.filter (fun s => dg G U s = 6)
  card : #Q = 2
  tail : PortTail G U P K Q u0

lemma ThreeTail.union {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ = 5) (hs6 : #{s ∈ S | dg G U s = 6} = 3)
    (t t' : ThreeTail G U U₁ W₁ S u0) :
    ∃ j : ThreeTail G U U₁ W₁ S u0,
      j.tail.X = t.tail.X ∪ t'.tail.X ∧ j.tail.B = t.tail.B ∪ t'.tail.B := by
  have hQ : t.Q ⊆ S := t.subset.trans (filter_subset _ _)
  have hQ' : t'.Q ⊆ S := t'.subset.trans (filter_subset _ _)
  have hcap : ∀ s ∈ S, dg G U₁ s ≤ 3 := fun s hs => original_lobe_port_cap h hi hdf hs
  have hju : t.tail.X ∪ t'.tail.X ⊆ U₁ := union_subset t.tail.left t'.tail.left
  have hji : t.tail.B ∪ t'.tail.B ⊆ W₁ := union_subset t.tail.right t'.tail.right
  have hiu : t.tail.X ∩ t'.tail.X ⊆ U₁ := inter_subset_left.trans t.tail.left
  have hii : t.tail.B ∩ t'.tail.B ⊆ W₁ := inter_subset_left.trans t.tail.right
  have hinter : (t.Q ∩ t'.Q).Nonempty := by
    by_contra hn
    have hzero : t.Q ∩ t'.Q = ∅ := not_nonempty_iff_eq_empty.mp hn
    have hc := card_union_add_card_inter t.Q t'.Q
    have hb := card_le_card (union_subset t.subset t'.subset)
    rw [hzero,card_empty,t.card,t'.card,hs6] at *
    omega
  obtain ⟨s,hs⟩ := hinter
  have hs₁ := (mem_inter.mp hs).1
  have hs₂ := (mem_inter.mp hs).2
  have hdeg : ∀ (a : ThreeTail G U U₁ W₁ S u0), ∀ s ∈ a.Q, dg G a.tail.X s = 3 := by
    intro a s hsa
    have hQa : a.Q ⊆ S := a.subset.trans (filter_subset _ _)
    have hm : ∀ q ∈ a.Q, dg G a.tail.X q ≤ 3 :=
      fun q hq => (dg_mono (G := G) a.tail.left q).trans (hcap q (hQa hq))
    have he : ∑ q ∈ a.Q, dg G a.tail.X q = 6 := by
      rw [← ec,ec_comm]; exact a.tail.ports
    have herase := sum_erase_add a.Q (fun q => dg G a.tail.X q) hsa
    have hbound : ∑ q ∈ a.Q.erase s, dg G a.tail.X q ≤ 3 := by
      calc _ ≤ ∑ _q ∈ a.Q.erase s, 3 := sum_le_sum fun q hq => hm q (mem_erase.mp hq).2
        _ = 3 := by have hc := card_erase_add_one hsa; rw [a.card] at hc; simp; omega
    have := hm s hsa
    omega
  have hds := hdeg t s hs₁
  have hds' := hdeg t' s hs₂
  have hsum := dg_union_add_dg_inter (G := G) t.tail.X t'.tail.X s
  have hjcap := (dg_mono (G := G) hju s).trans (hcap s (hQ hs₁))
  have hicard := dg_le_card (G := G) (t.tail.X ∩ t'.tail.X) s
  have hxi : 3 ≤ #(t.tail.X ∩ t'.tail.X) := by omega
  have hxt := card_le_card (inter_subset_left : t.tail.X ∩ t'.tail.X ⊆ t.tail.X)
  have hxj := card_le_card (subset_union_left : t.tail.X ⊆ t.tail.X ∪ t'.tail.X)
  have hbj := card_le_card (subset_union_left : t.tail.B ⊆ t.tail.B ∪ t'.tail.B)
  have hbal := t.tail.balance
  have hfj := h.local_floor hi hju (hji.trans subset_union_left) (by omega)
  have hsub := gv_union_add_gv_inter_le (G := G) t.tail.X t'.tail.X t.tail.B t'.tail.B
  rw [t.tail.potential,t'.tail.potential] at hsub
  have hni : 4 ≤ #(t.tail.X ∩ t'.tail.X)+#(t.tail.B ∩ t'.tail.B) := by
    by_contra hn
    have hz : #(t.tail.B ∩ t'.tail.B) = 0 := by omega
    have hx : #(t.tail.X ∩ t'.tail.X) = 3 := by omega
    have hempty := card_eq_zero.mp hz
    have h18 : gv G (t.tail.X ∩ t'.tail.X) (t.tail.B ∩ t'.tail.B) = 18 := by
      simp [gv,hempty,ec,dg,hx]
    omega
  have hfi := h.local_floor hi hiu (hii.trans subset_union_left) hni
  have htj : gv G (t.tail.X ∪ t'.tail.X) (t.tail.B ∪ t'.tail.B) = 16 := by omega
  have hti : gv G (t.tail.X ∩ t'.tail.X) (t.tail.B ∩ t'.tail.B) = 16 := by omega
  have hbj2 := tight_balance_le_two hi (hju.trans h.subsets.1) (hji.trans h.subsets.2.2.1) htj
  have hbi2 := tight_balance_le_two hi (hiu.trans h.subsets.1) (hii.trans h.subsets.2.2.1) hti
  have hxcard := card_union_add_card_inter t.tail.X t'.tail.X
  have hbcard := card_union_add_card_inter t.tail.B t'.tail.B
  have hbal' := t'.tail.balance
  have hbalance : (#(t.tail.X ∪ t'.tail.X) : ℤ)-#(t.tail.B ∪ t'.tail.B) = 2 := by omega
  have hpj : ec G (t.tail.X ∪ t'.tail.X) t.Q = 6 := by
    have hl := ec_mono_left (G := G) (subset_union_left : t.tail.X ⊆ t.tail.X ∪ t'.tail.X) t.Q
    have hu := (ec_mono_left (G := G) hju t.Q).trans (lobe_pair_cap h hi hdf hQ t.card)
    rw [t.tail.ports] at hl
    omega
  exact ⟨⟨t.Q,t.subset,t.card,⟨t.tail.X ∪ t'.tail.X,t.tail.B ∪ t'.tail.B,
    hju,hji,mem_union_left _ t.tail.scar,hbalance,htj,hpj⟩⟩,rfl,rfl⟩

lemma PortTail.marker_bound {U W S U₁ U₂ W₁ W₂ Q : Finset V} {u0 : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (_hi : U2Input G U W)
    (hw : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6)
    (t : PortTail G U U₁ W₁ Q u0) : #{y ∈ t.B | dg G U y = 5} ≤ 2 := by
  have hd := df_five_six (fun y hy => hw y (t.right hy))
  have hm := ec_mono_left (G := G) (t.left.trans h.subsets.1) t.B
  have he := df_eq (G := G) U t.B
  rw [ec_comm t.B U] at he
  have hp := t.potential
  have hb := t.balance
  unfold gv at hp
  omega

lemma retained_four_low_rank {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {z₁ z₂ : V}
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

lemma failed_pair_port_tail {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hdf₁ : df G U W₁ = 5) (hdf₂ : df G U W₂ = 6)
    (hcap₂ : ∀ s ∈ S, dg G U₂ s ≤ 3)
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
    (hcap₂ : ∀ s ∈ S, dg G U₂ s ≤ 3)
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
    (hcap₂ : ∀ s ∈ S, dg G U₂ s ≤ 3)
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

/-- Literal original R787 allocation3331/3333, with the unique degree-four
opposite omission fixed before every cut. Sizes and full allocation are kept
in this endpoint even where the stronger theorem derives or weakens them. -/
theorem original_selector_three_port_target
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₂ : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (_hn₁ : 6 ≤ #U₁) (_hn₂ : 6 ≤ #U₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (_hs : ∀ s ∈ S, dg G U s = 4 ∨ dg G U s = 6)
    (_hs4 : #{s ∈ S | dg G U s = 4} = 1)
    (hs6 : #{s ∈ S | dg G U s = 6} = 3)
    (_halloc₁ : ∀ s ∈ S, dg G U₁ s = if dg G U s = 6 then 3 else 1)
    (halloc₂ : ∀ s ∈ S, dg G U₂ s = 3)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c : #{y ∈ W₁ | dg G U y = 5} = 5)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c₄ : #{y ∈ W₂ | dg G U y = 4} = 1)
    (hw₂c₅ : #{y ∈ W₂ | dg G U y = 5} = 4)
    (hz₂ : z₂ ∈ W₂) (hd₂ : dg G U z₂ = 4) :
    #{z ∈ W₁ | dg G U z = 5 ∧ ¬ FixedOmissionFactor G U W z z₂} ≤ 2 ∧
    3 ≤ #{z ∈ W₁ | dg G U z = 5 ∧ FixedOmissionFactor G U W z z₂} := by
  have hcap₂ : ∀ s ∈ S, dg G U₂ s ≤ 3 := fun s hs => (halloc₂ s hs).le
  exact ⟨original_selector_three_port_at_most_two hi h hu hdu hs6 hcap₂
      hw₁ hw₁c hw₂ hw₂c₄ hw₂c₅ hz₂ hd₂,
    original_selector_three_port_at_least_three hi h hu hdu hs6 hcap₂
      hw₁ hw₁c hw₂ hw₂c₄ hw₂c₅ hz₂ hd₂⟩

#print axioms mixed_failure_scalar
#print axioms original_two_trace_tail
#print axioms ThreeTail.union
#print axioms retained_four_low_rank
#print axioms failed_pair_port_tail
#print axioms original_selector_three_port_at_most_two
#print axioms original_selector_three_port_at_least_three
#print axioms original_selector_three_port_target
end Erdos585.QB7ThreePortR806
