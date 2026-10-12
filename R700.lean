import R676
import R668
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.QB7MixedOmissionR700
open QB4 QB7SmallLobeR643 QB7TwoDegreeFourR676
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Original scalar inequalities for a two-port complementary cut. -/
structure MixedBounds (d eps m b c v : ℤ) : Prop where
  eps_nonneg : 0 ≤ eps
  eps_le : eps ≤ 1
  v_nonneg : 0 ≤ v
  value : c = b-v
  cap : -4*d ≤ c
  scar : 2*d+m-eps ≤ b
  zero : d = 0 → 5-eps ≤ b
  one : d = 1 → 6-eps ≤ b
  floor : 2 ≤ d → 8-d-eps ≤ b
  aug : 0 ≤ d → 2-d-eps ≤ c

lemma original_mixed_bounds {U W S U₁ U₂ W₁ W₂ X Y Q : Finset V} {z : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hX : X ⊆ U₁) (hY : Y ⊆ W₁) (hz : z ∈ Y)
    (hQ : Q ⊆ S) (hq : #Q = 2) :
    MixedBounds ((#X : ℤ)-#Y) (df G W X) (6-dg G U z)
      (2*#X+4*#Y-df G W X-ec G X Y)
      (cutCost G W X Y Q) (ec G X Q) := by
  let eps := df G W X
  let d : ℤ := (#X : ℤ)-#Y
  let b : ℤ := 2*#X+4*#Y-eps-ec G X Y
  let c := cutCost G W X Y Q
  have hXu := hX.trans h.subsets.1
  have hYw := hY.trans h.subsets.2.2.1
  have hQw := hQ.trans h.separator
  have heps : 0 ≤ eps ∧ eps ≤ 1 := by
    have hn := df_nonneg (G := G) (fun x hx => hi.capU x (hXu hx))
    have hb := df_le_of_subset (G := G) hXu hi.capU
    rw [hi.defU] at hb
    exact ⟨hn,hb⟩
  have hepsid := df_eq (G := G) W X
  have hYQ : Disjoint Y Q := h.rightSep₁.mono hY hQ
  have hec := ec_union_right (G := G) hYQ X
  have hmono := ec_mono_right (G := G) X (union_subset hYw hQw)
  have hscar : 6-(dg G U z : ℤ) ≤ 6*(#Y : ℤ)-(ec G X Y : ℤ) := by
    have hs := df_le_of_subset (G := G) (singleton_subset_iff.mpr hz)
      (fun y hy => hi.capW y (hYw hy))
    simp only [df,sum_singleton] at hs
    change 6-(dg G U z : ℤ) ≤ df G U Y at hs
    rw [df_eq,ec_comm Y U] at hs
    have hem := ec_mono_left (G := G) hXu Y
    omega
  have hypos : 1 ≤ #Y := card_pos.mpr ⟨z,hz⟩
  have hcap : -4*d ≤ c := by dsimp [c,cutCost,d,b,eps] at *; omega
  have hfloor : 4 ≤ #X+#Y → 8-d-eps ≤ b := by
    intro hn
    have hf := h.local_floor hi hX (hY.trans subset_union_left) hn
    unfold gv at hf
    dsimp [d,b]
    omega
  have hzero : d = 0 → 5-eps ≤ b := by
    intro hd
    by_cases hn : 4 ≤ #X+#Y
    · have := hfloor hn; omega
    · have hx1 : #X = 1 := by dsimp [d] at hd; omega
      have hy1 : #Y = 1 := by dsimp [d] at hd; omega
      have hp := ec_product_bound (G := G) X Y
      rw [hx1,hy1] at hp
      dsimp [b]
      rw [hx1,hy1]
      omega
  have hone : d = 1 → 6-eps ≤ b := by
    intro hd
    by_cases hn : 4 ≤ #X+#Y
    · have := hfloor hn; omega
    · have hx2 : #X = 2 := by dsimp [d] at hd; omega
      have hy1 : #Y = 1 := by dsimp [d] at hd; omega
      have hp := ec_product_bound (G := G) X Y
      rw [hx2,hy1] at hp
      dsimp [b]
      rw [hx2,hy1]
      omega
  have hlarge : 2 ≤ d → 8-d-eps ≤ b := by
    intro hd
    exact hfloor (by dsimp [d] at hd; omega)
  have haug : 0 ≤ d → 2-d-eps ≤ c := by
    intro hd
    have hn : 4 ≤ #X+#(Y ∪ Q) := by
      rw [card_union_of_disjoint hYQ,hq]
      dsimp [d] at hd
      omega
    have hf := h.local_floor hi hX
      (union_subset (hY.trans subset_union_left) (hQ.trans subset_union_right)) hn
    unfold gv at hf
    rw [card_union_of_disjoint hYQ,hq,hec] at hf
    dsimp [d,c,cutCost]
    omega
  refine ⟨heps.1,heps.2,by positivity,rfl,hcap,?_,hzero,hone,hlarge,haug⟩
  omega

lemma mixed_scalar {d₁ e₁ b₁ c₁ v₁ d₂ e₂ b₂ c₂ v₂ : ℤ}
    (h₁ : MixedBounds d₁ e₁ 1 b₁ c₁ v₁)
    (h₂ : MixedBounds d₂ e₂ 2 b₂ c₂ v₂)
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

lemma df_five_six {U K : Finset V}
    (hd : ∀ y ∈ K, dg G U y = 5 ∨ dg G U y = 6) :
    df G U K = (#{y ∈ K | dg G U y = 5} : ℤ) := by
  unfold df
  calc (∑ y ∈ K, (6-(dg G U y : ℤ))) =
      ∑ y ∈ K, if dg G U y = 5 then (1 : ℤ) else 0 := by
        apply sum_congr rfl
        intro y hy
        rcases hd y hy with hh|hh <;> simp [hh]
    _ = _ := by simp

lemma df_four_five_six {U K : Finset V}
    (hd : ∀ y ∈ K, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6) :
    df G U K = 2*(#{y ∈ K | dg G U y = 4} : ℤ)+
      (#{y ∈ K | dg G U y = 5} : ℤ) := by
  unfold df
  calc (∑ y ∈ K, (6-(dg G U y : ℤ))) =
      ∑ y ∈ K, ((if dg G U y = 4 then (2 : ℤ) else 0)+
        (if dg G U y = 5 then (1 : ℤ) else 0)) := by
        apply sum_congr rfl
        intro y hy
        rcases hd y hy with hh|hh|hh <;> simp [hh]
    _ = _ := by
      rw [sum_add_distrib]
      simp only [← sum_filter]
      simp [mul_comm]

lemma separator_pair_cap {U S Q : Finset V}
    (hS : #S = 4) (hd : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (hc : #{s ∈ S | dg G U s = 5} = 3)
    (hQ : Q ⊆ S) (hq : #Q = 2) : ec G U Q ≤ 11 := by
  have hds : df G U S = 3 := by rw [df_five_six hd,hc]; norm_num
  have hcard := card_sdiff_add_card_eq_card hQ
  have hcomp : df G U (S \ Q) ≤ (#(S \ Q) : ℤ) := by
    unfold df
    calc _ ≤ ∑ _s ∈ S \ Q, (1 : ℤ) := by
            apply sum_le_sum
            intro s hs
            rcases hd s (mem_sdiff.mp hs).1 with hh|hh <;> simp [hh]
      _ = _ := by simp
  have he := sum_sdiff hQ (f := fun s => 6-(dg G U s : ℤ))
  change df G U (S \ Q)+df G U Q = df G U S at he
  have hid := df_eq (G := G) U Q
  have hcomm := ec_comm (G := G) Q U
  omega

lemma mixed_low_rank {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hb₁ : df G U (W₁.erase z₁) ≤ 4) (hb₂ : df G U (W₂.erase z₂) ≤ 3)
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

lemma mixed_two_rank {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 5) (hd₂ : dg G U z₂ = 4)
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
  rw [hd₁] at hb₁
  rw [hd₂] at hb₂
  norm_num only at hb₁ hb₂
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
  have hpos := mixed_scalar hb₁ hb₂ heps hv
  have hc₁ := local_cost_of_partition h hi (hY₁.trans (erase_subset z₁ W₁)) hR hX₁ he₁
  have hc₂ := local_cost_of_partition h.swap hi (hY₂.trans (erase_subset z₂ W₂)) hR hX₂ he₂
  dsimp [B₁,B₂,Q] at hpos
  omega

/-- Every fixed original mixed omission in the residual branch leaves
an original unit-edge quartic on all retained vertices. No cut or rank premise
is supplied by the caller. -/
theorem original_mixed_fixed_omission
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ z₂ : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hn₁ : 6 ≤ #U₁) (hn₂ : 6 ≤ #U₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (hsc : #{s ∈ S | dg G U s = 5} = 3)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c : #{y ∈ W₁ | dg G U y = 5} = 5)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c₄ : #{y ∈ W₂ | dg G U y = 4} = 1)
    (hw₂c₅ : #{y ∈ W₂ | dg G U y = 5} = 3)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 5) (hd₂ : dg G U z₂ = 4) :
    FixedOmissionFactor G U W z₁ z₂
 := by
  classical
  have hi' := U2Input.of_original hi
  have hdf₁ : df G U W₁ = 5 := by rw [df_five_six hw₁,hw₁c]; norm_num
  have hdf₂ : df G U W₂ = 5 := by
    rw [df_four_five_six hw₂,hw₂c₄,hw₂c₅]
    norm_num
  have he₁ : df G U (W₁.erase z₁)+(6-(dg G U z₁ : ℤ)) = df G U W₁ :=
    sum_erase_add W₁ (fun y => 6-(dg G U y : ℤ)) hz₁
  have he₂ : df G U (W₂.erase z₂)+(6-(dg G U z₂ : ℤ)) = df G U W₂ :=
    sum_erase_add W₂ (fun y => 6-(dg G U y : ℤ)) hz₂
  have hb₁ : df G U (W₁.erase z₁) ≤ 4 := by rw [hd₁,hdf₁] at he₁; omega
  have hb₂ : df G U (W₂.erase z₂) ≤ 3 := by rw [hd₂,hdf₂] at he₂; omega
  by_contra hfail
  obtain ⟨Y₁,Y₂,R,hY₁,hY₂,hR,hneg⟩ := failed_pair_rank_cut h hi' hz₁ hz₂ hfail
  have hrmax : #R ≤ 4 := by have := card_le_card hR; rw [h.cardS] at this; exact this
  by_cases hrlo : #R ≤ 1
  · have := mixed_low_rank h hi' hb₁ hb₂ hY₁ hY₂ hR hrlo
    omega
  by_cases hr2 : #R = 2
  · have := mixed_two_rank h hi' hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR hr2 hs hsc
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
    have hsecond := h.swap.rank_erase_port_six hi' hz₂ hss (by omega) hY₂
    rw [← hReq] at hfirst hsecond
    omega
  · have hr4 : #R = 4 := by omega
    have hReq : R = S := eq_of_subset_of_card_le hR (by rw [h.cardS]; omega)
    have hfirst := h.rank_full hi' hz₁ (by omega) hY₁
    have hsecond := h.swap.rank_full hi' hz₂ (by omega) hY₂
    rw [← hReq] at hfirst hsecond
    omega

#print axioms original_mixed_fixed_omission
#print original_mixed_fixed_omission
#print axioms original_mixed_bounds
#print axioms mixed_scalar
end Erdos585.QB7MixedOmissionR700
