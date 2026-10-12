/- R854 profile-free S0011 formalization, following the R844 argument.
-/
import R799
import R827
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Finset
namespace Erdos585.QB7ProfileFreeR854
open QB4 QB7SmallLobeR643 QB7TwoDegreeFourR676 QB7MixedOmissionR700
  QB7Separator0111R721 QB7Selector0012R751
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

/-- Allowance seven on BOTH lobes, with arbitrary positive marker weight. -/
lemma allowance_seven_lower {d e m b c v : ℤ}
    (h : MixedBounds d e m b c v) (hm : 1 ≤ m) (hv : v ≤ 7) :
    -e ≤ c ∧ (c = -e → 2 ≤ d ∧ 6 ≤ v ∧ (3 ≤ d → 7 ≤ v)) := by
  have hd : d ≤ -1 ∨ d = 0 ∨ d = 1 ∨ d = 2 ∨ 3 ≤ d := by omega
  rcases h with ⟨he,he',hvn,hc,hcap,hs,hz,ho,hf,ha⟩
  rcases hd with hd|hd|hd|hd|hd
  all_goals try have hf' := hf (by omega)
  all_goals try have ha' := ha (by omega)
  all_goals constructor <;> intros <;> omega

lemma allowance_seven_failure {d₁ e₁ m₁ b₁ c₁ v₁ d₂ m₂ b₂ c₂ v₂ : ℤ}
    (h₁ : MixedBounds d₁ e₁ m₁ b₁ c₁ v₁)
    (h₂ : MixedBounds d₂ 0 m₂ b₂ c₂ v₂)
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (hv₁ : v₁ ≤ 7) (hv₂ : v₂ ≤ 7) (hv : v₁+v₂ ≤ 12)
    (hn : c₁+c₂ < 0) :
    d₁ = 2 ∧ e₁ = 1 ∧ b₁ = 5 ∧ v₁ = 6 ∧ d₂ = 2 ∧ b₂ = 6 ∧ v₂ = 6 := by
  have hl₁ := allowance_seven_lower h₁ hm₁ hv₁
  have hl₂ := allowance_seven_lower h₂ hm₂ hv₂
  have he : e₁ = 1 := by have := h₁.eps_le; omega
  have hc₁ : c₁ = -e₁ := by omega
  have hc₂ : c₂ = 0 := by omega
  have hx₁ := hl₁.2 hc₁
  have hx₂ := hl₂.2 (by omega)
  have hvv₁ : v₁ = 6 := by omega
  have hvv₂ : v₂ = 6 := by omega
  have hd₁ : d₁ = 2 := by by_contra hh; have := hx₁.2.2 (by omega); omega
  have hd₂ : d₂ = 2 := by by_contra hh; have := hx₂.2.2 (by omega); omega
  have hb₁ := h₁.value
  have hb₂ := h₂.value
  exact ⟨hd₁,he,by omega,hvv₁,hd₂,by omega,hvv₂⟩

/-- S0011 alone supplies both possible D orientations. -/
lemma original_deficiencies {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hs : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (hs5 : #{s ∈ S | dg G U s = 5} = 2) :
    5 ≤ df G U W₁ ∧ 5 ≤ df G U W₂ ∧
    df G U W₁ + df G U W₂ = 11 ∧
    df G U W₁ ≤ 6 ∧ df G U W₂ ≤ 6 := by
  have hds : df G U S = 2 := by rw [df_five_six hs,hs5]; norm_num
  have hd := hi.defW
  unfold df at hd
  rw [← h.rightCover,sum_union (show Disjoint (W₁ ∪ W₂) S from disjoint_union_left.mpr ⟨h.rightSep₁,h.rightSep₂⟩),
    sum_union h.rightDisjoint] at hd
  change df G U W₁+df G U W₂+df G U S = 13 at hd
  have h₁ := h.interior_scar hi
  have h₂ := h.swap.interior_scar hi
  exact ⟨h₁,h₂,by omega,by omega,by omega⟩

lemma lobe_pair_cap_seven {U W S U₁ U₂ W₁ W₂ Q : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ ≤ 6) (hQ : Q ⊆ S) (hq : #Q = 2) : ec G U₁ Q ≤ 7 := by
  have hsub : W₁ ∪ Q ⊆ W₁ ∪ S := union_subset subset_union_left (hQ.trans subset_union_right)
  have hp := h.left_large hi
  have hf := h.local_floor hi (Subset.refl U₁) hsub (by omega)
  have hb := h.local_balance hi
  have hedf : df G U₁ W₁ = df G U W₁ := by
    unfold df
    exact sum_congr rfl fun y hy => by rw [h.degree_right hy]
  have he := df_eq (G := G) U₁ W₁
  have hc := ec_comm (G := G) W₁ U₁
  unfold gv at hf
  rw [card_union_of_disjoint (h.rightSep₁.mono_right hQ),
    ec_union_right (h.rightSep₁.mono_right hQ),hq] at hf
  omega

/-- Both retained masses may be five, but their combined mass is at most nine. -/
lemma low_rank {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hb₁ : df G U (W₁.erase z₁) ≤ 5) (hb₂ : df G U (W₂.erase z₂) ≤ 5)
    (hbs : df G U (W₁.erase z₁)+df G U (W₂.erase z₂) ≤ 9)
    (hs : ∀ s ∈ S, 5 ≤ dg G U s)
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
      _ ≤ _ := sum_le_sum fun s hsR => hs s (hR hsR)
  omega

/-- One-port complementary cuts for EVERY positive original marker weight.
The equality incidence is essential when the two local scars sum to one. -/
lemma single_complement_bounds {U W S U₁ U₂ W₁ W₂ X Y Q : Finset V} {z : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hX : X ⊆ U₁) (hY : Y ⊆ W₁) (hz : z ∈ Y) (hdz : dg G U z < 6)
    (hQ : Q ⊆ S) (hq : #Q = 1) :
    2-df G W X ≤ cutCost G W X Y Q ∧
    (cutCost G W X Y Q = 2-df G W X →
      (#X : ℤ)-#Y = 3 ∧ 5 ≤ ec G X Q) := by
  obtain ⟨Q',hQ',hq'⟩ := exists_subset_card_eq (show 2 ≤ #S by rw [h.cardS]; omega)
  have hb := original_mixed_bounds h hi hX hY hz hQ' hq'
  let d : ℤ := (#X : ℤ)-#Y
  let eps := df G W X
  let b : ℤ := 2*#X+4*#Y-eps-ec G X Y
  let c := cutCost G W X Y Q
  have he : 0 ≤ eps ∧ eps ≤ 1 := ⟨hb.eps_nonneg,hb.eps_le⟩
  have hv : (ec G X Q : ℤ) ≤ 6 := by
    have hm := ec_mono_left (G := G) (hX.trans h.subsets.1) Q
    have hc := ec_le_six_mul (G := G) (fun q hqq => hi.capW q (h.separator (hQ hqq)))
    rw [hq] at hc
    have hcomm := ec_comm (G := G) Q U
    omega
  have hc : c = b-ec G X Q := rfl
  have hYQ := h.rightSep₁.mono hY hQ
  have hec := ec_union_right (G := G) hYQ X
  have hm := ec_mono_right (G := G) X
    (union_subset (hY.trans h.subsets.2.2.1) (hQ.trans h.separator))
  have hde := df_eq (G := G) W X
  have hcap : -4*d ≤ c := by dsimp [c,cutCost,d,b,eps] at *; omega
  have hypos : 1 ≤ #Y := card_pos.mpr ⟨z,hz⟩
  have hfloor : 4 ≤ #X+#Y+#Q → 5-d-eps ≤ c := by
    intro hn
    have hf := h.local_floor hi hX
      (union_subset (hY.trans subset_union_left) (hQ.trans subset_union_right))
      (by rw [card_union_of_disjoint hYQ]; omega)
    unfold gv at hf
    rw [card_union_of_disjoint hYQ,hq,hec] at hf
    dsimp [c,cutCost,d,eps]
    omega
  have hzero : d = 0 → 4-eps ≤ c := by
    intro hdzero
    by_cases hn : 4 ≤ #X+#Y+#Q
    · have hf := hfloor hn; omega
    · have hx1 : #X = 1 := by dsimp [d] at hdzero; omega
      have hy1 : #Y = 1 := by dsimp [d] at hdzero; omega
      have hp := ec_product_bound (G := G) X (Y ∪ Q)
      rw [card_union_of_disjoint hYQ,hq,hx1,hy1,hec] at hp
      dsimp [c,cutCost,eps]
      rw [hx1,hy1]
      omega
  have hposfloor : 1 ≤ d → 5-d-eps ≤ c := by
    intro hdp
    exact hfloor (by dsimp [d] at hdp; omega)
  have hbscar : 2*d+1-eps ≤ b := by have := hb.scar; dsimp [d,b,eps]; omega
  have hfinal : 2-eps ≤ c ∧ (c = 2-eps → d = 3 ∧ 5 ≤ ec G X Q) := by
    by_cases hneg : d ≤ -1
    · constructor <;> intros <;> omega
    by_cases hdzero : d = 0
    · have := hzero hdzero; constructor <;> intros <;> omega
    have hf := hposfloor (by omega)
    constructor
    · omega
    · intro heq
      exact ⟨by omega,by omega⟩
  exact hfinal

/-- All four triple traces, using the actual original singleton incidence cap. -/
lemma three_rank {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6)
    (hY₁ : Y₁ ⊆ W₁.erase z₁) (hY₂ : Y₂ ⊆ W₂.erase z₂)
    (hR : R ⊆ S) (hr : #R = 3) :
    12 ≤ rankTerm G U₁ Y₁ R+rankTerm G U₂ Y₂ R := by
  obtain ⟨X₁,hX₁,he₁⟩ := capped_partition (G := G) U₁ (Y₁ ∪ R)
  obtain ⟨X₂,hX₂,he₂⟩ := capped_partition (G := G) U₂ (Y₂ ∪ R)
  have hzB₁ : z₁ ∈ W₁ \ Y₁ := mem_sdiff.mpr ⟨hz₁,fun hh => (mem_erase.mp (hY₁ hh)).1 rfl⟩
  have hzB₂ : z₂ ∈ W₂ \ Y₂ := mem_sdiff.mpr ⟨hz₂,fun hh => (mem_erase.mp (hY₂ hh)).1 rfl⟩
  have hq : #(S \ R) = 1 := by have := card_sdiff_add_card_eq_card hR; rw [h.cardS,hr] at this; omega
  have hl₁ := single_complement_bounds h hi hX₁ sdiff_subset hzB₁ hd₁ sdiff_subset hq
  have hl₂ := single_complement_bounds h.swap hi hX₂ sdiff_subset hzB₂ hd₂ sdiff_subset hq
  have hc₁ := local_cost_of_partition h hi (hY₁.trans (erase_subset z₁ W₁)) hR hX₁ he₁
  have hc₂ := local_cost_of_partition h.swap hi (hY₂.trans (erase_subset z₂ W₂)) hR hX₂ he₂
  have heps : df G W X₁+df G W X₂ ≤ 1 := by
    have hd : Disjoint X₁ X₂ := h.leftDisjoint.mono hX₁ hX₂
    have hs : X₁ ∪ X₂ ⊆ U := union_subset (hX₁.trans h.subsets.1) (hX₂.trans h.subsets.2.1)
    have he := df_le_of_subset (G := G) hs hi.capU
    unfold df at he
    rw [sum_union hd] at he
    change df G W X₁+df G W X₂ ≤ df G W U at he
    rwa [hi.defU] at he
  by_contra hn
  have hf₁ : cutCost G W X₁ (W₁ \ Y₁) (S \ R) = 2-df G W X₁ := by omega
  have hf₂ : cutCost G W X₂ (W₂ \ Y₂) (S \ R) = 2-df G W X₂ := by omega
  have hv₁ := (hl₁.2 hf₁).2
  have hv₂ := (hl₂.2 hf₂).2
  have hcap : ec G U (S \ R) ≤ 6 := by
    have hc := ec_le_six_mul (G := G) (A := S \ R) (fun q hqq => hi.capW q (h.separator (mem_sdiff.mp hqq).1))
    rw [hq] at hc
    rwa [ec_comm] at hc
  have he := ec_union_left (G := G) h.leftDisjoint (S \ R)
  rw [h.leftCover] at he
  have hm₁ := ec_mono_left (G := G) hX₁ (S \ R)
  have hm₂ := ec_mono_left (G := G) hX₂ (S \ R)
  omega


/-- A physical support in original vertices; its port incidence uses original edges. -/
structure PortTail (G : SimpleGraph V) [DecidableRel G.Adj]
    (U P K Q : Finset V) where
  X : Finset V
  B : Finset V
  left : X ⊆ P
  right : B ⊆ K
  balance : (#X : ℤ)-#B = 2
  potential : gv G X B = 16
  ports : ec G X Q = 6

lemma original_two_trace_tails {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hdf₁ : df G U W₁ ≤ 6) (hdf₂ : df G U W₂ ≤ 6)
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
  have hv₁ := (ec_mono_left (G := G) hX₁ Q).trans (lobe_pair_cap_seven h hi hdf₁ hQ hq)
  have hv₂ := (ec_mono_left (G := G) hX₂ Q).trans (lobe_pair_cap_seven h.swap hi hdf₂ hQ hq)
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
  have hh := allowance_seven_failure hb₁ hb₂ (by omega) (by omega)
    (by exact_mod_cast hv₁) (by exact_mod_cast hv₂) hv hn'
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

/-- Any failure supplies physical tails for the SAME original fixed pair. -/
lemma failed_pair_port_tails {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (hs5 : #{s ∈ S | dg G U s = 5} = 2)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6)
    (hfail : ¬ FixedOmissionFactor G U W z₁ z₂) :
    let Q := S.filter fun s => dg G U s = 6
    ∃ t₁ : PortTail G U U₁ W₁ Q, ∃ t₂ : PortTail G U U₂ W₂ Q,
      u0 ∈ t₁.X ∧ z₁ ∈ t₁.B ∧ z₂ ∈ t₂.B ∧ ec G U₁ Q = 6 ∧ ec G U₂ Q = 6 := by
  have hd := original_deficiencies h hi hs hs5
  have he₁ : df G U (W₁.erase z₁)+(6-(dg G U z₁ : ℤ)) = df G U W₁ :=
    sum_erase_add W₁ (fun y => 6-(dg G U y : ℤ)) hz₁
  have he₂ : df G U (W₂.erase z₂)+(6-(dg G U z₂ : ℤ)) = df G U W₂ :=
    sum_erase_add W₂ (fun y => 6-(dg G U y : ℤ)) hz₂
  have hb₁ : df G U (W₁.erase z₁) ≤ 5 := by omega
  have hb₂ : df G U (W₂.erase z₂) ≤ 5 := by omega
  have hbs : df G U (W₁.erase z₁)+df G U (W₂.erase z₂) ≤ 9 := by omega
  have hsmin : ∀ s ∈ S, 5 ≤ dg G U s := by intro s hss; rcases hs s hss with hh|hh <;> omega
  obtain ⟨Y₁,Y₂,R,hY₁,hY₂,hR,hneg⟩ := failed_pair_rank_cut h hi hz₁ hz₂ hfail
  have hrmax : #R ≤ 4 := by have := card_le_card hR; rw [h.cardS] at this; exact this
  by_cases hrlo : #R ≤ 1
  · have := low_rank h hi hb₁ hb₂ hbs hsmin hY₁ hY₂ hR hrlo
    omega
  by_cases hr2 : #R = 2
  · obtain ⟨t₁,t₂,htu,ht₁,ht₂,he,hp₁,hp₂⟩ := original_two_trace_tails h hi hu hdu hd.2.2.2.1 hd.2.2.2.2
      hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR hr2 (by omega)
    have hq : #(S \ R) = 2 := by
      have hc := card_sdiff_add_card_eq_card hR
      rw [h.cardS,hr2] at hc
      omega
    have hQeq := saturated_pair_unique hi h.separator hs6 sdiff_subset hq he
    dsimp only
    rw [← hQeq]
    exact ⟨t₁,t₂,htu,ht₁,ht₂,hp₁,hp₂⟩
  by_cases hr3 : #R = 3
  · have := three_rank h hi hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR hr3
    omega
  · have hr4 : #R = 4 := by omega
    have hReq : R = S := eq_of_subset_of_card_le hR (by rw [h.cardS]; omega)
    have hfirst := h.rank_full hi hz₁ (by omega) hY₁
    have hsecond := h.swap.rank_full hi hz₂ (by omega) hY₂
    rw [← hReq] at hfirst hsecond
    omega

/-- Physical union closure needs only the derived legal allowance seven. -/
lemma PortTail.union {U W S U₁ U₂ W₁ W₂ Q : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ ≤ 6) (hQ : Q ⊆ S) (hq : #Q = 2)
    (t t' : PortTail G U U₁ W₁ Q) :
    ∃ j : PortTail G U U₁ W₁ Q, j.X = t.X ∪ t'.X ∧ j.B = t.B ∪ t'.B := by
  have hcap := lobe_pair_cap_seven h hi hdf hQ hq
  have hju : t.X ∪ t'.X ⊆ U₁ := union_subset t.left t'.left
  have hji : t.B ∪ t'.B ⊆ W₁ := union_subset t.right t'.right
  have hiu : t.X ∩ t'.X ⊆ U₁ := inter_subset_left.trans t.left
  have hii : t.B ∩ t'.B ⊆ W₁ := inter_subset_left.trans t.right
  have hem := ec_left_union_inter (G := G) t.X t'.X Q
  have heu := (ec_mono_left (G := G) hju Q).trans hcap
  have hei := (ec_mono_left (G := G) hiu Q).trans hcap
  rw [t.ports,t'.ports] at hem
  have hpi : 5 ≤ ec G (t.X ∩ t'.X) Q := by omega
  have heprod := ec_product_bound (G := G) (t.X ∩ t'.X) Q
  rw [hq] at heprod
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
  have hBQ : Disjoint (t.B ∪ t'.B) Q := h.rightSep₁.mono hji hQ
  have hfaug := h.local_floor hi hju
    (union_subset (hji.trans subset_union_left) (hQ.trans subset_union_right))
    (by rw [card_union_of_disjoint hBQ,hq]; omega)
  have hpj : ec G (t.X ∪ t'.X) Q = 6 := by
    have hm := ec_mono_left (G := G) (subset_union_left : t.X ⊆ t.X ∪ t'.X) Q
    rw [t.ports] at hm
    unfold gv at hfaug htj
    rw [card_union_of_disjoint hBQ,hq,ec_union_right hBQ] at hfaug
    omega
  exact ⟨⟨t.X ∪ t'.X,t.B ∪ t'.B,hju,hji,hbalance,htj,hpj⟩,rfl,rfl⟩

lemma PortTail.deficiency_bound {U W S U₁ U₂ W₁ W₂ Q : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (t : PortTail G U U₁ W₁ Q) : df G U t.B ≤ 2 := by
  have hm := ec_mono_left (G := G) (t.left.trans h.subsets.1) t.B
  have he := df_eq (G := G) U t.B
  rw [ec_comm t.B U] at he
  have hp := t.potential
  have hb := t.balance
  unfold gv at hp
  omega


/-- Original degree-four markers have weight two; degree-five markers have weight one. -/
def deficientMarkers (G : SimpleGraph V) [DecidableRel G.Adj] (U K : Finset V) : Finset V :=
  K.filter fun z => dg G U z < 6

/-- The sets depend only on the original graph and split, before any pair or cut. -/
noncomputable def physicalA (G : SimpleGraph V) [DecidableRel G.Adj]
    (U P K Q required : Finset V) : Finset V :=
  (deficientMarkers G U K).filter fun z => ec G P Q = 6 ∧
    ∃ t : PortTail G U P K Q, required ⊆ t.X ∧ z ∈ t.B

omit [DecidableEq V] in
lemma physicalA_subset (U P K Q required : Finset V) :
    physicalA G U P K Q required ⊆ deficientMarkers G U K := filter_subset _ _

lemma finite_physical_cover {U W S U₁ U₂ W₁ W₂ Q required A : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ ≤ 6) (hQ : Q ⊆ S) (hq : #Q = 2)
    (ha : ∀ z ∈ A, ∃ t : PortTail G U U₁ W₁ Q, required ⊆ t.X ∧ z ∈ t.B)
    (hne : A.Nonempty) :
    ∃ t : PortTail G U U₁ W₁ Q, required ⊆ t.X ∧ A ⊆ t.B := by
  induction A using Finset.induction_on with
  | empty => simp at hne
  | @insert a A haA ih =>
    obtain ⟨ta,hta,hza⟩ := ha a (mem_insert_self a A)
    rcases A.eq_empty_or_nonempty with rfl|hA
    · exact ⟨ta,hta,by simpa using (singleton_subset_iff.mpr hza)⟩
    · obtain ⟨tb,htb,hzb⟩ := ih (fun z hz => ha z (mem_insert_of_mem hz)) hA
      obtain ⟨t,htX,htB⟩ := ta.union h hi hdf hQ hq tb
      refine ⟨t,?_,?_⟩
      · rw [htX]; exact hta.trans subset_union_left
      · rw [htB]
        exact insert_subset (mem_union_left _ hza) (hzb.trans subset_union_right)

/-- A single physical union pays ALL markers, with degree-four weight counted twice. -/
lemma physicalA_deficiency_bound {U W S U₁ U₂ W₁ W₂ Q required : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ ≤ 6) (hQ : Q ⊆ S) (hq : #Q = 2) :
    df G U (physicalA G U U₁ W₁ Q required) ≤ 2 := by
  rcases (physicalA G U U₁ W₁ Q required).eq_empty_or_nonempty with hempty|hne
  · simp [hempty,df]
  · obtain ⟨t,_,hsub⟩ := finite_physical_cover h hi hdf hQ hq
      (fun z hz => (mem_filter.mp hz).2.2) hne
    exact (df_le_of_subset (G := G) hsub
      (fun y hy => hi.capW y (h.subsets.2.2.1 (t.right hy)))).trans (t.deficiency_bound h)

lemma failure_in_rectangle {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (hs5 : #{s ∈ S | dg G U s = 5} = 2)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hz₁ : z₁ ∈ deficientMarkers G U W₁) (hz₂ : z₂ ∈ deficientMarkers G U W₂)
    (hf : ¬ FixedOmissionFactor G U W z₁ z₂) :
    z₁ ∈ physicalA G U U₁ W₁ (S.filter fun s => dg G U s = 6) {u0} ∧
    z₂ ∈ physicalA G U U₂ W₂ (S.filter fun s => dg G U s = 6) ∅ := by
  obtain ⟨t₁,t₂,htu,ht₁,ht₂,hp₁,hp₂⟩ := failed_pair_port_tails h hi hu hdu hs hs5 hs6
    (mem_filter.mp hz₁).1 (mem_filter.mp hz₂).1 (mem_filter.mp hz₁).2 (mem_filter.mp hz₂).2 hf
  exact ⟨mem_filter.mpr ⟨hz₁,hp₁,t₁,singleton_subset_iff.mpr htu,ht₁⟩,
    mem_filter.mpr ⟨hz₂,hp₂,t₂,empty_subset _,ht₂⟩⟩

lemma rectangle_is_failure {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hz₁ : z₁ ∈ physicalA G U U₁ W₁ (S.filter fun s => dg G U s = 6) {u0})
    (hz₂ : z₂ ∈ physicalA G U U₂ W₂ (S.filter fun s => dg G U s = 6) ∅) :
    ¬ FixedOmissionFactor G U W z₁ z₂ := by
  obtain ⟨hz₁M,_,t₁,htu,ht₁⟩ := mem_filter.mp hz₁
  obtain ⟨hz₂M,_,t₂,_,ht₂⟩ := mem_filter.mp hz₂
  let Q := S.filter fun s => dg G U s = 6
  have hQ : Q ⊆ S := filter_subset _ _
  have hq : #Q = 2 := hs6
  have hR : S \ Q ⊆ S := sdiff_subset
  have hr : #(S \ Q) = 2 := by
    have hh := card_sdiff_add_card_eq_card hQ
    rw [h.cardS,hq] at hh
    omega
  have hY₁ : W₁ \ t₁.B ⊆ W₁.erase z₁ := by
    intro y hy
    obtain ⟨hyW,hn⟩ := mem_sdiff.mp hy
    exact mem_erase.mpr ⟨fun he => hn (he ▸ ht₁),hyW⟩
  have hY₂ : W₂ \ t₂.B ⊆ W₂.erase z₂ := by
    intro y hy
    obtain ⟨hyW,hn⟩ := mem_sdiff.mp hy
    exact mem_erase.mpr ⟨fun he => hn (he ▸ ht₂),hyW⟩
  have he₁ : df G W t₁.X = 1 := by
    have hh := df_le_of_subset (G := G) htu
      (fun x hx => hi.capU x (h.subsets.1 (t₁.left hx)))
    have hsdf : df G W {u0} = 1 := by simp [df,hdu]
    rw [hsdf] at hh
    have hb := df_le_of_subset (G := G) (t₁.left.trans h.subsets.1) hi.capU
    rw [hi.defU] at hb
    omega
  have he₂ := df_opposite_zero h hi hu hdu t₂.left
  have hfirst := QB7Selector0011R799.tail_rank_upper h hi t₁.left t₁.right hQ t₁.balance t₁.potential t₁.ports
  have hsecond := QB7Selector0011R799.tail_rank_upper h.swap hi t₂.left t₂.right hQ t₂.balance t₂.potential t₂.ports
  intro hf
  have hh := QB7Selector0011R799.original_rank_necessary h (mem_filter.mp hz₁M).1 (mem_filter.mp hz₂M).1 hY₁ hY₂ hR hf
  rw [he₁] at hfirst
  rw [he₂] at hsecond
  dsimp [Q] at hfirst hsecond hr hh
  omega

def pairWeight (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (p : V × V) : ℤ :=
  (6-(dg G U p.1 : ℤ))*(6-(dg G U p.2 : ℤ))

omit [DecidableEq V] in
lemma product_weight (U A B : Finset V) :
    ∑ p ∈ A ×ˢ B, pairWeight G U p = df G U A * df G U B := by
  simp only [sum_product,pairWeight,df,mul_sum,sum_mul]
  exact sum_comm

omit [DecidableEq V] in
lemma markers_deficiency {U K : Finset V} (hcap : ∀ z ∈ K, dg G U z ≤ 6) :
    df G U (deficientMarkers G U K) = df G U K := by
  unfold df deficientMarkers
  rw [sum_filter]
  apply sum_congr rfl
  intro z hz
  by_cases hh : dg G U z < 6
  · simp [hh]
  · have he : dg G U z = 6 := by have := hcap z hz; omega
    simp [he]

/-- Literal profile-free S0011 endpoint, all allocations and both D orientations.
No local-factor, selector, tail, or lobe-size premise is supplied by the caller. -/
theorem original_profile_free_target
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (hs5 : #{s ∈ S | dg G U s = 5} = 2)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2) :
    let Q := S.filter fun s => dg G U s = 6
    let A₁ := physicalA G U U₁ W₁ Q {u0}
    let A₂ := physicalA G U U₂ W₂ Q ∅
    let M₁ := deficientMarkers G U W₁
    let M₂ := deficientMarkers G U W₂
    A₁ ⊆ M₁ ∧ A₂ ⊆ M₂ ∧ df G U A₁ ≤ 2 ∧ df G U A₂ ≤ 2 ∧
    (∀ z₁ ∈ M₁, ∀ z₂ ∈ M₂,
      (¬ FixedOmissionFactor G U W z₁ z₂ ↔ z₁ ∈ A₁ ∧ z₂ ∈ A₂)) ∧
    (∑ p ∈ (M₁ ×ˢ M₂).filter (fun p => ¬ FixedOmissionFactor G U W p.1 p.2), pairWeight G U p) = df G U A₁ * df G U A₂ ∧
    (∑ p ∈ (M₁ ×ˢ M₂).filter (fun p => ¬ FixedOmissionFactor G U W p.1 p.2), pairWeight G U p) ≤ 4 ∧
    26 ≤ ∑ p ∈ (M₁ ×ˢ M₂).filter (fun p => FixedOmissionFactor G U W p.1 p.2), pairWeight G U p := by
  have hi' := U2Input.of_original hi
  have hd := original_deficiencies h hi' hs hs5
  let Q := S.filter fun s => dg G U s = 6
  let A₁ := physicalA G U U₁ W₁ Q {u0}
  let A₂ := physicalA G U U₂ W₂ Q ∅
  let M₁ := deficientMarkers G U W₁
  let M₂ := deficientMarkers G U W₂
  have hA₁ : df G U A₁ ≤ 2 := physicalA_deficiency_bound h hi' hd.2.2.2.1 (filter_subset _ _) hs6
  have hA₂ : df G U A₂ ≤ 2 := physicalA_deficiency_bound h.swap hi' hd.2.2.2.2 (filter_subset _ _) hs6
  have hsub₁ : A₁ ⊆ M₁ := physicalA_subset _ _ _ _ _
  have hsub₂ : A₂ ⊆ M₂ := physicalA_subset _ _ _ _ _
  have hiff : ∀ z₁ ∈ M₁, ∀ z₂ ∈ M₂,
      (¬ FixedOmissionFactor G U W z₁ z₂ ↔ z₁ ∈ A₁ ∧ z₂ ∈ A₂) := by
    intro z₁ hz₁ z₂ hz₂
    exact ⟨failure_in_rectangle h hi' hu hdu hs hs5 hs6 hz₁ hz₂,
      fun hh => rectangle_is_failure h hi' hu hdu hs6 hh.1 hh.2⟩
  have hbad_eq : (M₁ ×ˢ M₂).filter (fun p => ¬ FixedOmissionFactor G U W p.1 p.2) = A₁ ×ˢ A₂ := by
    ext p
    simp only [mem_filter,mem_product]
    constructor
    · rintro ⟨⟨hp₁,hp₂⟩,hf⟩
      exact (hiff p.1 hp₁ p.2 hp₂).mp hf
    · rintro ⟨hp₁,hp₂⟩
      exact ⟨⟨hsub₁ hp₁,hsub₂ hp₂⟩,(hiff p.1 (hsub₁ hp₁) p.2 (hsub₂ hp₂)).mpr ⟨hp₁,hp₂⟩⟩
  have hn₁ : 0 ≤ df G U A₁ := df_nonneg fun z hz => hi'.capW z (h.subsets.2.2.1 (mem_filter.mp (hsub₁ hz)).1)
  have hn₂ : 0 ≤ df G U A₂ := df_nonneg fun z hz => hi'.capW z (h.subsets.2.2.2 (mem_filter.mp (hsub₂ hz)).1)
  have hweight : (∑ p ∈ (M₁ ×ˢ M₂).filter (fun p => ¬ FixedOmissionFactor G U W p.1 p.2), pairWeight G U p) = df G U A₁ * df G U A₂ := by
    rw [hbad_eq,product_weight]
  have hbad : (∑ p ∈ (M₁ ×ˢ M₂).filter (fun p => ¬ FixedOmissionFactor G U W p.1 p.2), pairWeight G U p) ≤ 4 := by
    rw [hbad_eq,product_weight]
    nlinarith
  have hM₁ : df G U M₁ = df G U W₁ := markers_deficiency fun z hz => hi'.capW z (h.subsets.2.2.1 hz)
  have hM₂ : df G U M₂ = df G U W₂ := markers_deficiency fun z hz => hi'.capW z (h.subsets.2.2.2 hz)
  have htotal : (∑ p ∈ M₁ ×ˢ M₂, pairWeight G U p) = 30 := by
    rw [product_weight,hM₁,hM₂]
    rcases (show df G U W₁ = 5 ∨ df G U W₁ = 6 by omega) with hh|hh <;> rw [hh] <;> nlinarith [hd.2.2.1]
  have hsum := sum_filter_add_sum_filter_not (s := M₁ ×ˢ M₂)
    (p := fun p => FixedOmissionFactor G U W p.1 p.2) (f := pairWeight G U)
  have hgood : 26 ≤ ∑ p ∈ (M₁ ×ˢ M₂).filter (fun p => FixedOmissionFactor G U W p.1 p.2), pairWeight G U p := by omega
  exact ⟨hsub₁,hsub₂,hA₁,hA₂,hiff,hweight,hbad,hgood⟩


/-- Actual original unit-edge quartics, with total successful omission weight at least26. -/
theorem original_profile_free_raw
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (hs5 : #{s ∈ S | dg G U s = 5} = 2)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2) :
    ∃ P : Finset (V × V),
      26 ≤ ∑ p ∈ P, pairWeight G U p ∧
      P ⊆ deficientMarkers G U W₁ ×ˢ deficientMarkers G U W₂ ∧
      ∀ p ∈ P, ∃ F : Finset (V × V), F ⊆ U ×ˢ (W.erase p.1 |>.erase p.2) ∧
        (∀ e ∈ F, G.Adj e.1 e.2) ∧
        (∀ x ∈ U, #{e ∈ F | e.1 = x} = 4) ∧
        (∀ y ∈ (W.erase p.1 |>.erase p.2), #{e ∈ F | e.2 = y} = 4) := by
  have hh := original_profile_free_target hi h hu hdu hs hs5 hs6
  rcases hh with ⟨_,_,_,_,_,_,_,hgood⟩
  let P := ((deficientMarkers G U W₁) ×ˢ (deficientMarkers G U W₂)).filter
    (fun p => FixedOmissionFactor G U W p.1 p.2)
  exact ⟨P,hgood,filter_subset _ _,fun p hp => (mem_filter.mp hp).2⟩

/-- One originally fixed deficient pair pays every cut simultaneously. -/
theorem original_profile_free_exists
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (hs5 : #{s ∈ S | dg G U s = 5} = 2)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2) :
    ∃ z₁ ∈ W₁, ∃ z₂ ∈ W₂, dg G U z₁ < 6 ∧ dg G U z₂ < 6 ∧
      FixedOmissionFactor G U W z₁ z₂ := by
  obtain ⟨P,hgood,hsub,hf⟩ := original_profile_free_raw hi h hu hdu hs hs5 hs6
  have hne : P.Nonempty := by
    by_contra hn
    have he : P = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [he] at hgood
    simp at hgood
  obtain ⟨p,hp⟩ := hne
  obtain ⟨hp₁,hp₂⟩ := mem_product.mp (hsub hp)
  obtain ⟨hw₁,hd₁⟩ := mem_filter.mp hp₁
  obtain ⟨hw₂,hd₂⟩ := mem_filter.mp hp₂
  exact ⟨p.1,hw₁,p.2,hw₂,hd₁,hd₂,hf p hp⟩

#print axioms allowance_seven_lower
#print axioms allowance_seven_failure
#print axioms original_deficiencies
#print axioms single_complement_bounds
#print axioms three_rank
#print axioms original_two_trace_tails
#print axioms failed_pair_port_tails
#print axioms PortTail.union
#print axioms physicalA_deficiency_bound
#print axioms original_profile_free_target
#print axioms original_profile_free_raw
#print axioms original_profile_free_exists
end Erdos585.QB7ProfileFreeR854
