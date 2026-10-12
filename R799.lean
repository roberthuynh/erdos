/- -/
import R763
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.QB7Selector0011R799
open QB4 QB7SmallLobeR643 QB7TwoDegreeFourR676 QB7MixedOmissionR700 QB7Separator0111R721 QB7Selector0012R751
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma mixed_failure_scalar {d₁ e₁ b₁ c₁ v₁ d₂ b₂ c₂ v₂ : ℤ}
    (h₁ : MixedBounds d₁ e₁ 1 b₁ c₁ v₁)
    (h₂ : MixedBounds d₂ 0 1 b₂ c₂ v₂)
    (hv₁ : v₁ ≤ 6) (hv₂ : v₂ ≤ 7) (hv : v₁+v₂ ≤ 12)
    (hn : c₁+c₂ < 0) :
    d₁ = 2 ∧ e₁ = 1 ∧ b₁ = 5 ∧ v₁ = 6 ∧ d₂ = 2 ∧ b₂ = 6 ∧ v₂ = 6 := by
  rcases h₁ with ⟨he1,he1',hv1,hc1,hcap1,hs1,hz1,ho1,hf1,ha1⟩
  rcases h₂ with ⟨_,_,hv2,hc2,hcap2,hs2,hz2,ho2,hf2,ha2⟩
  have hd1 : d₁ ≤ -1 ∨ d₁ = 0 ∨ d₁ = 1 ∨ d₁ = 2 ∨ 3 ≤ d₁ := by omega
  have hd2 : d₂ ≤ -1 ∨ d₂ = 0 ∨ d₂ = 1 ∨ d₂ = 2 ∨ 3 ≤ d₂ := by omega
  rcases hd1 with hd1|hd1|hd1|hd1|hd1 <;> rcases hd2 with hd2|hd2|hd2|hd2|hd2
  all_goals try have hz1' := hz1 hd1
  all_goals try have ho1' := ho1 hd1
  all_goals try have hf1' := hf1 (by omega)
  all_goals try have ha1' := ha1 (by omega)
  all_goals try have hz2' := hz2 hd2
  all_goals try have ho2' := ho2 hd2
  all_goals try have hf2' := hf2 (by omega)
  all_goals try have ha2' := ha2 (by omega)
  all_goals omega

lemma lobe_pair_cap_seven {U W S U₁ U₂ W₁ W₂ Q : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ = 6) (hQ : Q ⊆ S) (hq : #Q = 2) : ec G U₁ Q ≤ 7 := by
  have hsub : W₁ ∪ Q ⊆ W₁ ∪ S := union_subset subset_union_left (hQ.trans subset_union_right)
  have hp := h.left_large hi
  have hf := h.local_floor hi (Subset.refl U₁) hsub (by omega)
  have hb := h.local_balance hi
  have hd : df G U₁ W₁ = 6 := by
    have he : df G U₁ W₁ = df G U W₁ := by
      unfold df
      exact sum_congr rfl fun y hy => by rw [h.degree_right hy]
    omega
  have he := df_eq (G := G) U₁ W₁
  have hc := ec_comm (G := G) W₁ U₁
  unfold gv at hf
  rw [card_union_of_disjoint (h.rightSep₁.mono_right hQ),ec_union_right (h.rightSep₁.mono_right hQ),hq] at hf
  omega

lemma low_rank {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hb₁ : df G U (W₁.erase z₁) ≤ 4) (hb₂ : df G U (W₂.erase z₂) ≤ 5)
    (hs : ∀ s ∈ S, 5 ≤ dg G U s)
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
  have hm₂ : max 0 (df G U Y₂+2*#R-6) ≤ (#R : ℤ) := by
    apply max_le <;> omega
  rw [hm₁] at hfirst
  have he := ec_union_left (G := G) h.leftDisjoint R
  rw [h.leftCover] at he
  have hmin : 5*#R ≤ ec G U R := by
    rw [ec_comm]
    unfold ec
    calc 5*#R = ∑ _s ∈ R, 5 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun s hsR => hs s (hR hsR)
  omega

lemma unscarred_single_port_deficit_le_two {P K S X Y : Finset V} {z s : V}
    (hKS : Disjoint K S) (hz : z ∈ K) (hs : s ∈ S)
    (hX : X ⊆ P) (hY : Y ⊆ K.erase z)
    (hbalance : #P = #K + 1)
    (hcap : ∀ x ∈ P, dg G (K ∪ S) x ≤ 6)
    (hkcap : ∀ y ∈ K, dg G P y ≤ 6)
    (hscar : df G (K ∪ S) P ≤ 0)
    (hret : df G P (K.erase z) ≤ 5)
    (hfloor : ∀ A ⊆ P, ∀ T ⊆ K ∪ S, 4 ≤ #A + #T → 16 ≤ gv G A T)
    (hboundary : 8 - df G (K ∪ S) P ≤ (ec G P (S.erase s) : ℤ)) :
    4 * ((#X : ℤ) - #Y) - ec G X (K.erase z \ Y) - ec G X (S.erase s) ≤ 2 := by
  let C := P \ X
  let Z := K.erase z \ Y
  let q : ℤ := (#X : ℤ) - #Y - 2
  have hCY := ec_sdiff_add_left (G := G) hX Y
  have hCZ := ec_sdiff_add_left (G := G) hX Z
  have hCR := ec_sdiff_add_left (G := G) hX (S.erase s)
  have hCQ := ec_union_right (G := G) hKS C
  have hXQ := ec_union_right (G := G) hKS X
  have hCXK := ec_erase_right (G := G) (P := C) hz
  have hXXK := ec_erase_right (G := G) (P := X) hz
  have hCXret := ec_sdiff_add_right (G := G) hY C
  have hXXret := ec_sdiff_add_right (G := G) hY X
  have hCXs := ec_erase_right (G := G) (P := C) hs
  have hXXs := ec_erase_right (G := G) (P := X) hs
  have hcardC := card_sdiff_add_card_eq_card hX
  have hcardZ := card_sdiff_add_card_eq_card hY
  have hcardK := card_erase_add_one hz
  have hdeltaZ : df G P Z ≤ 5 := (df_le_of_subset (G := G) (S := P)
    (sdiff_subset : Z ⊆ K.erase z) (fun y hy => hkcap y (mem_erase.mp hy).2)).trans hret
  have hepsX : df G (K ∪ S) X ≤ 0 :=
    (df_le_of_subset (G := G) (S := K ∪ S) hX hcap).trans hscar
  have hepsC : 0 ≤ df G (K ∪ S) C := df_nonneg fun x hx => hcap x (sdiff_subset hx)
  have hdZ := df_eq (G := G) P Z
  have hdX := df_eq (G := G) (K ∪ S) X
  have hdC := df_eq (G := G) (K ∪ S) C
  have hcZ := ec_comm (G := G) Z P
  have hu : 4 * ((#X : ℤ) - #Y) - ec G X Z - ec G X (S.erase s) ≤ 5 - 2 * q := by
    dsimp [C,Z] at *
    dsimp [q]
    omega
  by_cases hq : q ≤ 1
  · have hzy : z ∉ Y := fun hzY => (mem_erase.mp (hY hzY)).1 rfl
    have hsK : s ∉ K := fun hsK => disjoint_left.mp hKS hsK hs
    have hsy : s ∉ Y := fun hsY => hsK ((mem_erase.mp (hY hsY)).2)
    have hsz : s ≠ z := fun he => hsK (he ▸ hz)
    have hsmallcard : #(insert s (insert z Y)) = #Y + 2 := by
      rw [card_insert_of_notMem (by simp only [mem_insert]; exact not_or.mpr ⟨hsz,hsy⟩),
        card_insert_of_notMem hzy]
    have hsmallsubset : insert s (insert z Y) ⊆ K ∪ S := by
      intro x hx
      rcases mem_insert.mp hx with rfl|hx
      · exact mem_union_right _ hs
      rcases mem_insert.mp hx with rfl|hx
      · exact mem_union_left _ hz
      · exact mem_union_left _ ((mem_erase.mp (hY hx)).2)
    have hsmallE : ec G X (insert s (insert z Y)) =
        dg G X s + dg G X z + ec G X Y := by
      rw [ec_insert_right (by simp only [mem_insert]; exact not_or.mpr ⟨hsz,hsy⟩),
        ec_insert_right hzy]
      omega
    by_cases hn : 4 ≤ #X + #(insert s (insert z Y))
    · have hf := hfloor X hX (insert s (insert z Y)) hsmallsubset hn
      unfold gv at hf
      dsimp [q] at hq
      dsimp [Z] at *
      omega
    · have hp := ec_product_bound (G := G) X (insert s (insert z Y))
      by_cases hx0 : #X = 0
      · have hXe : X = ∅ := card_eq_zero.mp hx0
        simp [hXe,ec] at *
        omega
      · have hx1 : #X = 1 := by omega
        have hy0 : #Y = 0 := by omega
        rw [hx1,hsmallcard,hy0] at hp
        norm_num at hp
        dsimp [Z] at *
        omega
  · dsimp [Z] at hu
    omega

#print axioms unscarred_single_port_deficit_le_two

lemma unscarred_rank_erase_port_six_lower {P K S Y : Finset V} {z s : V}
    (hKS : Disjoint K S) (hz : z ∈ K) (hs : s ∈ S) (hY : Y ⊆ K.erase z)
    (hbalance : #P = #K + 1)
    (hcap : ∀ x ∈ P, dg G (K ∪ S) x ≤ 6)
    (hkcap : ∀ y ∈ K, dg G P y ≤ 6)
    (hscar : df G (K ∪ S) P ≤ 0) (hret : df G P (K.erase z) ≤ 5)
    (hfloor : ∀ A ⊆ P, ∀ T ⊆ K ∪ S, 4 ≤ #A + #T → 16 ≤ gv G A T)
    (hboundary : 8 - df G (K ∪ S) P ≤ (ec G P (S.erase s) : ℤ)) :
    6 ≤ rankTerm G P Y (S.erase s) := by
  obtain ⟨A,hA,he⟩ := capped_partition (G := G) P (Y ∪ S.erase s)
  have hc := unscarred_single_port_deficit_le_two hKS hz hs hA
    (sdiff_subset : K.erase z \ Y ⊆ K.erase z)
    hbalance hcap hkcap hscar hret hfloor hboundary
  rw [Finset.sdiff_sdiff_eq_self hY] at hc
  have hYS : Disjoint Y (S.erase s) := hKS.mono (hY.trans (erase_subset z K)) (erase_subset s S)
  have hsplit := ec_union_right (G := G) hYS A
  have hPA := card_sdiff_add_card_eq_card hA
  have hKY := card_sdiff_add_card_eq_card hY
  have hKz := card_erase_add_one hz
  unfold rankTerm
  omega



lemma unscarred_rank_six {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z s : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hz : z ∈ W₂) (hs : s ∈ S) (hret : df G U (W₂.erase z) ≤ 5)
    {Y : Finset V} (hY : Y ⊆ W₂.erase z) : 6 ≤ rankTerm G U₂ Y (S.erase s) := by
  have hdef : df G U₂ (W₂.erase z) = df G U (W₂.erase z) := by
    unfold df
    exact sum_congr rfl fun y hy => by rw [h.swap.degree_right (mem_erase.mp hy).2]
  have hscar : df G (W₂ ∪ S) U₂ = 0 := by
    have he : df G (W₂ ∪ S) U₂ = df G W U₂ := by
      unfold df
      exact sum_congr rfl fun x hx => by rw [h.swap.degree_left hx]
    rw [he,df_opposite_zero h hi hu hdu (Subset.refl U₂)]
  apply unscarred_rank_erase_port_six_lower h.rightSep₂ hz hs hY (h.swap.local_balance hi)
  · intro x hx
    rw [h.swap.degree_left hx]
    exact hi.capU x (h.subsets.2.1 hx)
  · intro y hy
    rw [h.swap.degree_right hy]
    exact hi.capW y (h.subsets.2.2.2 hy)
  · omega
  · rwa [hdef]
  · exact fun A hA T hT hn => h.swap.local_floor hi hA hT hn
  · exact h.swap.boundary_complement_lower hi hs

lemma original_two_trace_tails {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hdf₁ : df G U W₁ = 5) (hdf₂ : df G U W₂ = 6)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 5) (hd₂ : dg G U z₂ = 5)
    (hY₁ : Y₁ ⊆ W₁.erase z₁) (hY₂ : Y₂ ⊆ W₂.erase z₂)
    (hR : R ⊆ S) (hr : #R = 2)
    (hn : rankTerm G U₁ Y₁ R+rankTerm G U₂ Y₂ R < 8) :
    ∃ t₁ : QB7Selector0012R751.PortTail G U U₁ W₁ (S \ R) u0,
    ∃ t₂ : QB7Reversed0012R763.PortTail G U U₂ W₂ (S \ R),
      z₁ ∈ t₁.B ∧ z₂ ∈ t₂.B ∧ ec G U (S \ R) = 12 := by
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
  have hv₂ := (ec_mono_left (G := G) hX₂ Q).trans (lobe_pair_cap_seven h.swap hi hdf₂ hQ hq)
  have hcap : ec G U Q ≤ 12 := by
    rw [ec_comm]
    unfold ec
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
  have hh := mixed_failure_scalar hb₁ hb₂ (by exact_mod_cast hv₁) (by exact_mod_cast hv₂) hv hn'
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
  exact ⟨⟨X₁,B₁,hX₁,hB₁,hscar,hdx₁,hpot₁,by simpa [Q] using (show ec G X₁ Q = 6 by omega)⟩,
    ⟨X₂,B₂,hX₂,hB₂,hdx₂,hpot₂,by simpa [Q] using (show ec G X₂ Q = 6 by omega)⟩,hzB₁,hzB₂,he⟩

lemma unscarred_tail_union {U W S U₁ U₂ W₁ W₂ Q : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ = 6) (hQ : Q ⊆ S) (hq : #Q = 2)
    (t t' : QB7Reversed0012R763.PortTail G U U₁ W₁ Q) :
    ∃ j : QB7Reversed0012R763.PortTail G U U₁ W₁ Q, j.X = t.X ∪ t'.X ∧ j.B = t.B ∪ t'.B := by
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

lemma unscarred_marker_bound {U W S U₁ U₂ W₁ W₂ Q : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (_hi : U2Input G U W)
    (hw : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6)
    (t : QB7Reversed0012R763.PortTail G U U₁ W₁ Q) : #{y ∈ t.B | dg G U y = 5} ≤ 2 := by
  have hd := df_five_six (fun y hy => hw y (t.right hy))
  have hm := ec_mono_left (G := G) (t.left.trans h.subsets.1) t.B
  have he := df_eq (G := G) U t.B
  rw [ec_comm t.B U] at he
  have hp := t.potential
  have hb := t.balance
  unfold gv at hp
  omega



lemma failed_pair_port_tails {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hdf₁ : df G U W₁ = 5) (hdf₂ : df G U W₂ = 6)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hs : ∀ s ∈ S, 5 ≤ dg G U s)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 5) (hd₂ : dg G U z₂ = 5)
    (hfail : ¬ FixedOmissionFactor G U W z₁ z₂) :
    ∃ t₁ : QB7Selector0012R751.PortTail G U U₁ W₁ (S.filter fun s => dg G U s = 6) u0,
    ∃ t₂ : QB7Reversed0012R763.PortTail G U U₂ W₂ (S.filter fun s => dg G U s = 6),
      z₁ ∈ t₁.B ∧ z₂ ∈ t₂.B ∧ ec G U₂ (S.filter fun s => dg G U s = 6) = 6 := by
  have he₁ : df G U (W₁.erase z₁)+(6-(dg G U z₁ : ℤ)) = df G U W₁ :=
    sum_erase_add W₁ (fun y => 6-(dg G U y : ℤ)) hz₁
  have he₂ : df G U (W₂.erase z₂)+(6-(dg G U z₂ : ℤ)) = df G U W₂ :=
    sum_erase_add W₂ (fun y => 6-(dg G U y : ℤ)) hz₂
  have hb₁ : df G U (W₁.erase z₁) ≤ 4 := by rw [hd₁,hdf₁] at he₁; omega
  have hb₂ : df G U (W₂.erase z₂) ≤ 5 := by rw [hd₂,hdf₂] at he₂; omega
  obtain ⟨Y₁,Y₂,R,hY₁,hY₂,hR,hneg⟩ := failed_pair_rank_cut h hi hz₁ hz₂ hfail
  have hrmax : #R ≤ 4 := by have := card_le_card hR; rw [h.cardS] at this; exact this
  by_cases hrlo : #R ≤ 1
  · have := low_rank h hi hb₁ hb₂ hs hY₁ hY₂ hR hrlo
    omega
  by_cases hr2 : #R = 2
  · obtain ⟨t₁,t₂,ht₁,ht₂,he⟩ := original_two_trace_tails h hi hu hdu hdf₁ hdf₂
      hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR hr2 (by omega)
    have hq : #(S \ R) = 2 := by
      have hc := card_sdiff_add_card_eq_card hR
      rw [h.cardS,hr2] at hc
      omega
    have hQeq := saturated_pair_unique hi h.separator hs6 sdiff_subset hq he
    rw [← hQeq]
    have hp₂ : ec G U₂ (S \ R) = 6 := by
      have hm₁ := ec_mono_left (G := G) t₁.left (S \ R)
      have hm₂ := ec_mono_left (G := G) t₂.left (S \ R)
      rw [t₁.ports] at hm₁
      rw [t₂.ports] at hm₂
      have hec := ec_union_left (G := G) h.leftDisjoint (S \ R)
      rw [h.leftCover] at hec
      omega
    exact ⟨t₁,t₂,ht₁,ht₂,hp₂⟩
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
    have hsecond := unscarred_rank_six h hi hu hdu hz₂ hss hb₂ hY₂
    rw [← hReq] at hfirst hsecond
    omega
  · have hr4 : #R = 4 := by omega
    have hReq : R = S := eq_of_subset_of_card_le hR (by rw [h.cardS]; omega)
    have hfirst := h.rank_full hi hz₁ (by omega) hY₁
    have hsecond := h.swap.rank_full hi hz₂ (by omega) hY₂
    rw [← hReq] at hfirst hsecond
    omega


attribute [local instance] Classical.propDecidable

def markers (G : SimpleGraph V) [DecidableRel G.Adj] (U K : Finset V) : Finset V :=
  K.filter fun z => dg G U z = 5

noncomputable def physicalA₁ (G : SimpleGraph V) [DecidableRel G.Adj]
    (U U₁ W₁ Q : Finset V) (u0 : V) : Finset V :=
  (markers G U W₁).filter fun z =>
    ∃ t : QB7Selector0012R751.PortTail G U U₁ W₁ Q u0, z ∈ t.B

noncomputable def physicalA₂ (G : SimpleGraph V) [DecidableRel G.Adj]
    (U U₂ W₂ Q : Finset V) : Finset V :=
  (markers G U W₂).filter fun z => ec G U₂ Q = 6 ∧
    ∃ t : QB7Reversed0012R763.PortTail G U U₂ W₂ Q, z ∈ t.B

lemma physicalA₁_bound {U W S U₁ U₂ W₁ W₂ Q : Finset V} {u0 : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ = 5) (hQ : Q ⊆ S) (hq : #Q = 2)
    (hw : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6) :
    #(physicalA₁ G U U₁ W₁ Q u0) ≤ 2 := by
  by_contra hn
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := two_lt_card_iff.mp (by omega :
    2 < #(physicalA₁ G U U₁ W₁ Q u0))
  rcases mem_filter.mp ha with ⟨haM,ta,hta⟩
  rcases mem_filter.mp hb with ⟨hbM,tb,htb⟩
  rcases mem_filter.mp hc with ⟨hcM,tc,htc⟩
  have haD := (mem_filter.mp haM).2
  have hbD := (mem_filter.mp hbM).2
  have hcD := (mem_filter.mp hcM).2
  obtain ⟨tab,_,htab⟩ := ta.union h hi hdf hQ hq tb
  obtain ⟨tabc,_,htabc⟩ := tab.union h hi hdf hQ hq tc
  have hbound := tabc.marker_bound h hi hw
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

lemma physicalA₂_bound {U W S U₁ U₂ W₁ W₂ Q : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₂ = 6) (hQ : Q ⊆ S) (hq : #Q = 2)
    (hw : ∀ y ∈ W₂, dg G U y = 5 ∨ dg G U y = 6) :
    #(physicalA₂ G U U₂ W₂ Q) ≤ 2 := by
  by_contra hn
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := two_lt_card_iff.mp (by omega :
    2 < #(physicalA₂ G U U₂ W₂ Q))
  rcases mem_filter.mp ha with ⟨haM,_,ta,hta⟩
  rcases mem_filter.mp hb with ⟨hbM,_,tb,htb⟩
  rcases mem_filter.mp hc with ⟨hcM,_,tc,htc⟩
  have haD := (mem_filter.mp haM).2
  have hbD := (mem_filter.mp hbM).2
  have hcD := (mem_filter.mp hcM).2
  obtain ⟨tab,_,htab⟩ := unscarred_tail_union h.swap hi hdf hQ hq ta tb
  obtain ⟨tabc,_,htabc⟩ := unscarred_tail_union h.swap hi hdf hQ hq tab tc
  have hbound := unscarred_marker_bound h.swap hi hw tabc
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

lemma failure_in_rectangle {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hdf₁ : df G U W₁ = 5) (hdf₂ : df G U W₂ = 6)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2) (hs : ∀ s ∈ S, 5 ≤ dg G U s)
    (hz₁ : z₁ ∈ markers G U W₁) (hz₂ : z₂ ∈ markers G U W₂)
    (hf : ¬ FixedOmissionFactor G U W z₁ z₂) :
    z₁ ∈ physicalA₁ G U U₁ W₁ (S.filter fun s => dg G U s = 6) u0 ∧
    z₂ ∈ physicalA₂ G U U₂ W₂ (S.filter fun s => dg G U s = 6) := by
  obtain ⟨t₁,t₂,ht₁,ht₂,hp₂⟩ := failed_pair_port_tails h hi hu hdu hdf₁ hdf₂ hs6 hs
    (mem_filter.mp hz₁).1 (mem_filter.mp hz₂).1
    (mem_filter.mp hz₁).2 (mem_filter.mp hz₂).2 hf
  exact ⟨mem_filter.mpr ⟨hz₁,t₁,ht₁⟩,mem_filter.mpr ⟨hz₂,hp₂,t₂,ht₂⟩⟩

#print axioms failed_pair_port_tails
#print axioms physicalA₁_bound
#print axioms physicalA₂_bound

lemma factor_capped_lower {U W T : Finset V} {z₁ z₂ : V}
    (hf : FixedOmissionFactor G U W z₁ z₂) (hT : T ⊆ (W.erase z₁).erase z₂) :
    4*#T ≤ capped G U T := by
  obtain ⟨F,hF,hFG,hFU,hFW⟩ := hf
  let J := F.filter fun e => e.2 ∈ T
  have hJU : ∀ e ∈ J, e.1 ∈ U := fun e he =>
    (mem_product.mp (hF (mem_filter.mp he).1)).1
  have hJT : ∀ e ∈ J, e.2 ∈ T := fun _ he => (mem_filter.mp he).2
  have hcT := card_eq_sum_card_fiberwise (f := Prod.snd) hJT
  have hcU := card_eq_sum_card_fiberwise (f := Prod.fst) hJU
  have hright : ∀ y ∈ T, #{e ∈ J | e.2 = y} = 4 := by
    intro y hy
    have he : J.filter (fun e => e.2 = y) = F.filter (fun e => e.2 = y) := by
      ext e
      simp only [J,mem_filter]
      constructor
      · tauto
      · rintro ⟨he,rfl⟩; exact ⟨⟨he,hy⟩,rfl⟩
    rw [he,hFW y (hT hy)]
  have hleft : ∀ x ∈ U, #{e ∈ J | e.1 = x} ≤ min 4 (dg G T x) := by
    intro x hx
    apply le_min
    · have hsub : J.filter (fun e => e.1 = x) ⊆ F.filter (fun e => e.1 = x) := by
        intro e he
        exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp he).1).1,(mem_filter.mp he).2⟩
      simpa [hFU x hx] using card_le_card hsub
    · apply card_le_card_of_injOn Prod.snd
      · intro e he
        obtain ⟨heJ,hex⟩ := mem_filter.mp he
        obtain ⟨heF,heT⟩ := mem_filter.mp heJ
        exact mem_filter.mpr ⟨heT,hex ▸ hFG e heF⟩
      · intro a ha b hb he
        exact Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm) he
  have hsum := sum_le_sum hleft
  have hct : #J = 4*#T := by
    rw [hcT]
    calc _ = ∑ _y ∈ T, 4 := sum_congr rfl hright
      _ = _ := by simp [mul_comm]
  rw [← hcU] at hsum
  exact hct ▸ hsum

lemma original_rank_necessary {U W S U₁ U₂ W₁ W₂ Y₁ Y₂ R : Finset V} {z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hY₁ : Y₁ ⊆ W₁.erase z₁) (hY₂ : Y₂ ⊆ W₂.erase z₂) (hR : R ⊆ S)
    (hf : FixedOmissionFactor G U W z₁ z₂) :
    4*(#R : ℤ) ≤ rankTerm G U₁ Y₁ R+rankTerm G U₂ Y₂ R := by
  let T := Y₁ ∪ Y₂ ∪ R
  have hY₁K := hY₁.trans (erase_subset z₁ W₁)
  have hY₂K := hY₂.trans (erase_subset z₂ W₂)
  have hY₁₂ := h.rightDisjoint.mono hY₁K hY₂K
  have hY₁R := h.rightSep₁.mono hY₁K hR
  have hY₂R := h.rightSep₂.mono hY₂K hR
  have hT : T ⊆ (W.erase z₁).erase z₂ := by
    rw [h.retained_cover hz₁ hz₂]
    exact union_subset (union_subset (hY₁.trans (subset_union_left.trans subset_union_left))
      (hY₂.trans (subset_union_right.trans subset_union_left))) (hR.trans subset_union_right)
  have hcard : #T = #Y₁+#Y₂+#R := by
    dsimp [T]
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hY₁R,hY₂R⟩),card_union_of_disjoint hY₁₂]
  have hleft : ∀ x ∈ U₁, dg G T x = dg G (Y₁ ∪ R) x := by
    intro x hx
    have he : (Y₁ ∪ R) ∪ Y₂ = T := by dsimp [T]; ac_rfl
    have hd := dg_union_of_disjoint (G := G) (disjoint_union_left.mpr ⟨hY₁₂,hY₂R.symm⟩) x
    have hz : dg G Y₂ x = 0 := dg_zero fun y hy => h.cross₁ x hx y (hY₂K hy)
    rw [he,hz] at hd
    omega
  have hright : ∀ x ∈ U₂, dg G T x = dg G (Y₂ ∪ R) x := by
    intro x hx
    have he : (Y₂ ∪ R) ∪ Y₁ = T := by dsimp [T]; ac_rfl
    have hd := dg_union_of_disjoint (G := G) (disjoint_union_left.mpr ⟨hY₁₂.symm,hY₁R.symm⟩) x
    have hz : dg G Y₁ x = 0 := dg_zero fun y hy => h.cross₂ x hx y (hY₁K hy)
    rw [he,hz] at hd
    omega
  have hcap : capped G U T = capped G U₁ (Y₁ ∪ R)+capped G U₂ (Y₂ ∪ R) := by
    unfold capped
    rw [← h.leftCover,sum_union h.leftDisjoint]
    congr 1
    · exact sum_congr rfl fun x hx => by rw [hleft x hx]
    · exact sum_congr rfl fun x hx => by rw [hright x hx]
  have hh := factor_capped_lower hf hT
  unfold rankTerm
  omega

lemma tail_rank_upper {U W S U₁ U₂ W₁ W₂ X B Q : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hX : X ⊆ U₁) (hB : B ⊆ W₁) (hQ : Q ⊆ S)
    (hbalance : (#X : ℤ)-#B = 2) (hpot : gv G X B = 16)
    (hport : ec G X Q = 6) :
    rankTerm G U₁ (W₁ \ B) (S \ Q) ≤ 4-df G W X := by
  have hC : (W₁ \ B) ∪ (S \ Q) = (W₁ ∪ S) \ (B ∪ Q) := by
    ext y
    have hbs := h.rightSep₁.mono hB hQ
    simp only [mem_union,mem_sdiff]
    constructor
    · rintro (⟨hy,hn⟩|⟨hy,hn⟩)
      · refine ⟨Or.inl hy,?_⟩
        rintro (hh|hh)
        · exact hn hh
        · exact disjoint_left.mp h.rightSep₁ hy (hQ hh)
      · refine ⟨Or.inr hy,?_⟩
        rintro (hh|hh)
        · exact disjoint_left.mp h.rightSep₁ (hB hh) hy
        · exact hn hh
    · rintro ⟨hy,hn⟩
      rcases hy with hy|hy
      · exact Or.inl ⟨hy,fun hh => hn (Or.inl hh)⟩
      · exact Or.inr ⟨hy,fun hh => hn (Or.inr hh)⟩
  have hBQ : Disjoint B Q := h.rightSep₁.mono hB hQ
  have hsub : B ∪ Q ⊆ W₁ ∪ S := union_subset (hB.trans subset_union_left) (hQ.trans subset_union_right)
  have he := ec_sdiff_add_right (G := G) hsub X
  rw [ec_union_right hBQ] at he
  have hdf : df G (W₁ ∪ S) X = df G W X := by
    unfold df
    exact sum_congr rfl fun x hx => by rw [h.degree_left (hX hx)]
  have hd := df_eq (G := G) (W₁ ∪ S) X
  have hp := h.local_balance hi
  have hc := card_sdiff_add_card_eq_card hB
  have hx := card_sdiff_add_card_eq_card hX
  have hu := capped_upper_split (G := G) (T := (W₁ \ B) ∪ (S \ Q)) hX
  rw [hC] at hu
  unfold rankTerm
  rw [hC]
  unfold gv at hpot
  omega

lemma rectangle_is_failure {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hz₁ : z₁ ∈ physicalA₁ G U U₁ W₁ (S.filter fun s => dg G U s = 6) u0)
    (hz₂ : z₂ ∈ physicalA₂ G U U₂ W₂ (S.filter fun s => dg G U s = 6)) :
    ¬ FixedOmissionFactor G U W z₁ z₂ := by
  obtain ⟨hz₁M,t₁,ht₁⟩ := mem_filter.mp hz₁
  obtain ⟨hz₂M,_,t₂,ht₂⟩ := mem_filter.mp hz₂
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
    have hsub : {u0} ⊆ t₁.X := singleton_subset_iff.mpr t₁.scar
    have hh := df_le_of_subset (G := G) hsub (fun x hx => hi.capU x (h.subsets.1 (t₁.left hx)))
    have hsdf : df G W {u0} = 1 := by simp [df,hdu]
    rw [hsdf] at hh
    have hb := df_le_of_subset (G := G) (t₁.left.trans h.subsets.1) hi.capU
    rw [hi.defU] at hb
    omega
  have he₂ := df_opposite_zero h hi hu hdu t₂.left
  have hfirst := tail_rank_upper h hi t₁.left t₁.right hQ t₁.balance t₁.potential t₁.ports
  have hsecond := tail_rank_upper h.swap hi t₂.left t₂.right hQ t₂.balance t₂.potential t₂.ports
  intro hf
  have hh := original_rank_necessary h (mem_filter.mp hz₁M).1 (mem_filter.mp hz₂M).1 hY₁ hY₂ hR hf
  rw [he₁] at hfirst
  rw [he₂] at hsecond
  dsimp [Q] at hfirst hsecond hr hh
  omega

#print axioms factor_capped_lower
#print axioms rectangle_is_failure

/-- Exact physical obstruction rectangle and at least26 original unit-edge
quartics among the30 omission pairs. Every selected pair precedes all cuts. -/
theorem original_selector0011_target
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (_hs5 : #{s ∈ S | dg G U s = 5} = 2)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c : #{y ∈ W₁ | dg G U y = 5} = 5)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c : #{y ∈ W₂ | dg G U y = 5} = 6) :
    let Q := S.filter fun s => dg G U s = 6
    let A₁ := physicalA₁ G U U₁ W₁ Q u0
    let A₂ := physicalA₂ G U U₂ W₂ Q
    #A₁ ≤ 2 ∧ #A₂ ≤ 2 ∧
    (∀ z₁ ∈ markers G U W₁, ∀ z₂ ∈ markers G U W₂,
      (¬ FixedOmissionFactor G U W z₁ z₂ ↔ z₁ ∈ A₁ ∧ z₂ ∈ A₂)) ∧
    #{p ∈ (markers G U W₁) ×ˢ (markers G U W₂) |
      ¬ FixedOmissionFactor G U W p.1 p.2} ≤ 4 ∧
    26 ≤ #{p ∈ (markers G U W₁) ×ˢ (markers G U W₂) |
      FixedOmissionFactor G U W p.1 p.2} := by
  classical
  have hi' := U2Input.of_original hi
  have hdf₁ : df G U W₁ = 5 := by rw [df_five_six hw₁,hw₁c]; norm_num
  have hdf₂ : df G U W₂ = 6 := by rw [df_five_six hw₂,hw₂c]; norm_num
  have hsmin : ∀ s ∈ S, 5 ≤ dg G U s := by
    intro s hsS
    rcases hs s hsS with hh|hh <;> omega
  let Q := S.filter fun s => dg G U s = 6
  let A₁ := physicalA₁ G U U₁ W₁ Q u0
  let A₂ := physicalA₂ G U U₂ W₂ Q
  have hA₁ : #A₁ ≤ 2 := physicalA₁_bound h hi' hdf₁ (filter_subset _ _) hs6 hw₁
  have hA₂ : #A₂ ≤ 2 := physicalA₂_bound h hi' hdf₂ (filter_subset _ _) hs6 hw₂
  have hiff : ∀ z₁ ∈ markers G U W₁, ∀ z₂ ∈ markers G U W₂,
      (¬ FixedOmissionFactor G U W z₁ z₂ ↔ z₁ ∈ A₁ ∧ z₂ ∈ A₂) := by
    intro z₁ hz₁ z₂ hz₂
    exact ⟨failure_in_rectangle h hi' hu hdu hdf₁ hdf₂ hs6 hsmin hz₁ hz₂,
      fun hh => rectangle_is_failure h hi' hu hdu hs6 hh.1 hh.2⟩
  have hsub : ((markers G U W₁) ×ˢ (markers G U W₂)).filter
      (fun p => ¬ FixedOmissionFactor G U W p.1 p.2) ⊆ A₁ ×ˢ A₂ := by
    intro p hp
    obtain ⟨hpM,hpF⟩ := mem_filter.mp hp
    obtain ⟨hp₁,hp₂⟩ := mem_product.mp hpM
    exact mem_product.mpr ((hiff p.1 hp₁ p.2 hp₂).mp hpF)
  have hprod : #(A₁ ×ˢ A₂) ≤ 4 := by
    rw [card_product]
    have hh := Nat.mul_le_mul hA₁ hA₂
    norm_num at hh
    exact hh
  have hbad : #{p ∈ (markers G U W₁) ×ˢ (markers G U W₂) |
      ¬ FixedOmissionFactor G U W p.1 p.2} ≤ 4 := (card_le_card hsub).trans hprod
  have he := card_filter_add_card_filter_not
    (s := (markers G U W₁) ×ˢ (markers G U W₂))
    (fun p => FixedOmissionFactor G U W p.1 p.2)
  have hc₁ : #(markers G U W₁) = 5 := hw₁c
  have hc₂ : #(markers G U W₂) = 6 := hw₂c
  rw [card_product,hc₁,hc₂] at he
  exact ⟨hA₁,hA₂,hiff,hbad,by omega⟩

/-- Literal original caller with actual edge sets and exact retained degrees. -/
theorem original_selector0011_raw
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs : ∀ s ∈ S, dg G U s = 5 ∨ dg G U s = 6)
    (hs5 : #{s ∈ S | dg G U s = 5} = 2)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c : #{y ∈ W₁ | dg G U y = 5} = 5)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c : #{y ∈ W₂ | dg G U y = 5} = 6) :
    ∃ P : Finset (V × V), 26 ≤ #P ∧
      P ⊆ (W₁.filter fun z => dg G U z = 5) ×ˢ (W₂.filter fun z => dg G U z = 5) ∧
      ∀ p ∈ P, ∃ F : Finset (V × V), F ⊆ U ×ˢ (W.erase p.1 |>.erase p.2) ∧
        (∀ e ∈ F, G.Adj e.1 e.2) ∧
        (∀ x ∈ U, #{e ∈ F | e.1 = x} = 4) ∧
        (∀ y ∈ (W.erase p.1 |>.erase p.2), #{e ∈ F | e.2 = y} = 4) := by
  have hh := original_selector0011_target hi h hu hdu hs hs5 hs6 hw₁ hw₁c hw₂ hw₂c
  let P := ((markers G U W₁) ×ˢ (markers G U W₂)).filter
    (fun p => FixedOmissionFactor G U W p.1 p.2)
  refine ⟨P,hh.2.2.2.2,filter_subset _ _,?_⟩
  intro p hp
  exact (mem_filter.mp hp).2

#print axioms mixed_failure_scalar
#print axioms original_two_trace_tails
#print axioms unscarred_tail_union
#print axioms original_selector0011_target
#print axioms original_selector0011_raw
end Erdos585.QB7Selector0011R799
