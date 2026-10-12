import R643Bridge
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.QB7SmallLobeR643
open QB4
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma single_port_deficit_le_two {P K S X Y : Finset V} {z s : V}
    (hKS : Disjoint K S) (hz : z ∈ K) (hs : s ∈ S)
    (hX : X ⊆ P) (hY : Y ⊆ K.erase z)
    (hbalance : #P = #K + 1)
    (hcap : ∀ x ∈ P, dg G (K ∪ S) x ≤ 6)
    (hkcap : ∀ y ∈ K, dg G P y ≤ 6)
    (hscar : df G (K ∪ S) P ≤ 1)
    (hret : df G P (K.erase z) ≤ 4)
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
  have hdeltaZ : df G P Z ≤ 4 := (df_le_of_subset (G := G) (S := P)
    (sdiff_subset : Z ⊆ K.erase z) (fun y hy => hkcap y (mem_erase.mp hy).2)).trans hret
  have hepsX : df G (K ∪ S) X ≤ 1 :=
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

#print axioms single_port_deficit_le_two

lemma rank_erase_port_six_lower {P K S Y : Finset V} {z s : V}
    (hKS : Disjoint K S) (hz : z ∈ K) (hs : s ∈ S) (hY : Y ⊆ K.erase z)
    (hbalance : #P = #K + 1)
    (hcap : ∀ x ∈ P, dg G (K ∪ S) x ≤ 6)
    (hkcap : ∀ y ∈ K, dg G P y ≤ 6)
    (hscar : df G (K ∪ S) P ≤ 1) (hret : df G P (K.erase z) ≤ 4)
    (hfloor : ∀ A ⊆ P, ∀ T ⊆ K ∪ S, 4 ≤ #A + #T → 16 ≤ gv G A T)
    (hboundary : 8 - df G (K ∪ S) P ≤ (ec G P (S.erase s) : ℤ)) :
    6 ≤ rankTerm G P Y (S.erase s) := by
  obtain ⟨A,hA,he⟩ := capped_partition (G := G) P (Y ∪ S.erase s)
  have hc := single_port_deficit_le_two hKS hz hs hA
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

lemma Split.rank_erase_port_six {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    {z s : V} (hz : z ∈ W₁) (hs : s ∈ S) (hret : df G U (W₁.erase z) ≤ 4)
    {Y : Finset V} (hY : Y ⊆ W₁.erase z) : 6 ≤ rankTerm G U₁ Y (S.erase s) := by
  have hdef : df G U₁ (W₁.erase z) = df G U (W₁.erase z) := by
    unfold df
    exact sum_congr rfl fun y hy => by rw [h.degree_right (mem_erase.mp hy).2]
  apply rank_erase_port_six_lower h.rightSep₁ hz hs hY (h.local_balance hi)
  · intro x hx
    rw [h.degree_left hx]
    exact hi.capU x (h.subsets.1 hx)
  · intro y hy
    rw [h.degree_right hy]
    exact hi.capW y (h.subsets.2.2.1 hy)
  · exact (h.local_scar hi).2
  · rwa [hdef]
  · exact fun A hA T hT hn => h.local_floor hi hA hT hn
  · exact h.boundary_complement_lower hi hs


lemma deficient_count_le {P Q : Finset V}
    (hcap : ∀ y ∈ Q, dg G P y ≤ 6) :
    (#(Q.filter fun y => dg G P y < 6) : ℤ) ≤ df G P Q := by
  let D := Q.filter fun y => dg G P y < 6
  have hd : (#D : ℤ) ≤ df G P D := by
    unfold df
    calc (#D : ℤ) = ∑ _y ∈ D, (1 : ℤ) := by simp
      _ ≤ _ := sum_le_sum fun y hy => by
        have := (mem_filter.mp hy).2
        omega
  exact hd.trans (df_le_of_subset (filter_subset _ _) hcap)

lemma Split.three_deficient_accounting {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hthree : 3 ≤ #(S.filter fun s => dg G U s < 6)) :
    df G U S = 3 ∧ df G U W₁ = 5 ∧ df G U W₂ = 5 ∧
    (∀ s ∈ S, 5 ≤ dg G U s) := by
  have hpart : df G U W₁ + df G U W₂ + df G U S = 13 := by
    have he : df G U (W₁ ∪ W₂ ∪ S) = df G U W₁ + df G U W₂ + df G U S := by
      unfold df
      rw [sum_union (disjoint_union_left.mpr ⟨h.rightSep₁,h.rightSep₂⟩),
        sum_union h.rightDisjoint]
    rw [h.rightCover, hi.defW] at he
    omega
  have hfirst := h.interior_scar hi
  have hsecond := h.swap.interior_scar hi
  have hcount := deficient_count_le (G := G) (fun s hs => hi.capW s (h.separator hs))
  have hscar : df G U S = 3 := by omega
  refine ⟨hscar,by omega,by omega,?_⟩
  intro s hs
  have hcap : ∀ y ∈ S.erase s, dg G U y ≤ 6 :=
    fun y hy => hi.capW y (h.separator (mem_erase.mp hy).2)
  have hc := deficient_count_le (G := G) hcap
  have hfilter : (S.erase s).filter (fun y => dg G U y < 6) =
      (S.filter fun y => dg G U y < 6).erase s := by
    ext y
    simp only [mem_filter,mem_erase]
    tauto
  rw [hfilter] at hc
  have hcard : #(S.filter fun y => dg G U y < 6) ≤
      #((S.filter fun y => dg G U y < 6).erase s) + 1 := by
    by_cases hm : s ∈ S.filter fun y => dg G U y < 6
    · have := card_erase_add_one hm
      omega
    · rw [erase_eq_of_notMem hm]
      omega
  have he : df G U (S.erase s) + (6 - (dg G U s : ℤ)) = df G U S :=
    sum_erase_add S (fun y => 6 - (dg G U y : ℤ)) hs
  omega

lemma Split.three_deficient_retained {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hthree : 3 ≤ #(S.filter fun s => dg G U s < 6))
    {z : V} (hz : z ∈ W₁) (hd : dg G U z = 4) :
    df G U (W₁.erase z) = 3 := by
  have hh := h.three_deficient_accounting hi hthree
  have he : df G U (W₁.erase z) + (6 - (dg G U z : ℤ)) = df G U W₁ :=
    sum_erase_add W₁ (fun y => 6 - (dg G U y : ℤ)) hz
  omega

lemma Split.three_deficient_rank_cuts {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hthree : 3 ≤ #(S.filter fun s => dg G U s < 6))
    {z₁ z₂ : V} (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 4) (hd₂ : dg G U z₂ = 4)
    {Y₁ Y₂ R : Finset V} (hY₁ : Y₁ ⊆ W₁.erase z₁)
    (hY₂ : Y₂ ⊆ W₂.erase z₂) (hR : R ⊆ S) :
    4 * (#R : ℤ) ≤ rankTerm G U₁ Y₁ R + rankTerm G U₂ Y₂ R := by
  have hacc := h.three_deficient_accounting hi hthree
  have hret₁ := h.three_deficient_retained hi hthree hz₁ hd₁
  have hret₂ := h.swap.three_deficient_retained hi hthree hz₂ hd₂
  have hRmax : #R ≤ 4 := by have := card_le_card hR; rw [h.cardS] at this; exact this
  by_cases hrlo : #R ≤ 2
  · have hfirst := h.capped_rank_lower hi (hY₁.trans (erase_subset z₁ W₁)) hR
    have hsecond := h.swap.capped_rank_lower hi (hY₂.trans (erase_subset z₂ W₂)) hR
    have hdefY₁ : df G U Y₁ ≤ 3 := by
      have hh := df_le_of_subset (G := G) hY₁
        (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))
      omega
    have hdefY₂ : df G U Y₂ ≤ 3 := by
      have hh := df_le_of_subset (G := G) hY₂
        (fun y hy => hi.capW y (h.subsets.2.2.2 (mem_erase.mp hy).2))
      omega
    have hdefR : df G U R ≤ #R := by
      unfold df
      calc (∑ y ∈ R, (6 - (dg G U y : ℤ))) ≤ ∑ _y ∈ R, (1 : ℤ) :=
          sum_le_sum fun y hy => by have := hacc.2.2.2 y (hR hy); omega
        _ = _ := by simp
    have he := ec_union_left (G := G) h.leftDisjoint R
    rw [h.leftCover] at he
    have hdR := df_eq (G := G) U R
    have hec := ec_comm (G := G) R U
    by_cases hr : #R = 2
    · have hm₁ : max 0 (df G U Y₁ + 2 * #R - 6) ≤ 1 := max_le (by omega) (by omega)
      have hm₂ : max 0 (df G U Y₂ + 2 * #R - 6) ≤ 1 := max_le (by omega) (by omega)
      omega
    · have hr : #R ≤ 1 := by omega
      have hm₁ : max 0 (df G U Y₁ + 2 * #R - 6) = 0 := max_eq_left (by omega)
      have hm₂ : max 0 (df G U Y₂ + 2 * #R - 6) = 0 := max_eq_left (by omega)
      rw [hm₁] at hfirst
      rw [hm₂] at hsecond
      omega
  · by_cases hr3 : #R = 3
    · have hd := card_sdiff_add_card_eq_card hR
      have hdiffone : #(S \ R) = 1 := by rw [h.cardS] at hd; omega
      obtain ⟨s,hsing⟩ := card_eq_one.mp hdiffone
      have hs : s ∈ S := (mem_sdiff.mp (show s ∈ S \ R by rw [hsing]; simp)).1
      have hReq : R = S.erase s := by
        have he := Finset.sdiff_sdiff_eq_self hR
        rw [hsing] at he
        simpa only [sdiff_singleton_eq_erase] using he.symm
      have hfirst := h.rank_erase_port_six hi hz₁ hs (by omega) hY₁
      have hsecond := h.swap.rank_erase_port_six hi hz₂ hs (by omega) hY₂
      rw [← hReq] at hfirst hsecond
      omega
    · have hr4 : #R = 4 := by omega
      have hReq : R = S := eq_of_subset_of_card_le hR (by rw [h.cardS]; omega)
      rw [hReq]
      have hfirst := h.rank_full hi hz₁ (by omega) hY₁
      have hsecond := h.swap.rank_full hi hz₂ (by omega) hY₂
      have hc := h.cardS
      omega
lemma Split.three_deficient_capped_cuts {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W) (hthree : 3 ≤ #(S.filter fun s => dg G U s < 6))
    {z₁ z₂ : V} (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 4) (hd₂ : dg G U z₂ = 4)
    {T : Finset V} (hT : T ⊆ (W.erase z₁).erase z₂) :
    4 * #T ≤ capped G U T := by
  let Y₁ := T ∩ W₁.erase z₁
  let Y₂ := T ∩ W₂.erase z₂
  let R := T ∩ S
  have hY₁ : Y₁ ⊆ W₁.erase z₁ := inter_subset_right
  have hY₂ : Y₂ ⊆ W₂.erase z₂ := inter_subset_right
  have hR : R ⊆ S := inter_subset_right
  have hY₁K : Y₁ ⊆ W₁ := hY₁.trans (erase_subset z₁ W₁)
  have hY₂K : Y₂ ⊆ W₂ := hY₂.trans (erase_subset z₂ W₂)
  have hY₁₂ : Disjoint Y₁ Y₂ := h.rightDisjoint.mono hY₁K hY₂K
  have hY₁R : Disjoint Y₁ R := h.rightSep₁.mono hY₁K hR
  have hY₂R : Disjoint Y₂ R := h.rightSep₂.mono hY₂K hR
  have hcover : Y₁ ∪ Y₂ ∪ R = T := by
    ext x
    constructor
    · intro hx
      rcases mem_union.mp hx with hxy|hxr
      · rcases mem_union.mp hxy with hx1|hx2
        · exact (mem_inter.mp hx1).1
        · exact (mem_inter.mp hx2).1
      · exact (mem_inter.mp hxr).1
    · intro hx
      have hxQ := hT hx
      rw [h.retained_cover hz₁ hz₂] at hxQ
      rcases mem_union.mp hxQ with hx12|hxs
      · rcases mem_union.mp hx12 with hx1|hx2
        · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hx,hx1⟩))
        · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨hx,hx2⟩))
      · exact mem_union_right _ (mem_inter.mpr ⟨hx,hxs⟩)
  have hcard : #T = #Y₁ + #Y₂ + #R := by
    rw [← hcover,card_union_of_disjoint (disjoint_union_left.mpr ⟨hY₁R,hY₂R⟩),
      card_union_of_disjoint hY₁₂]
  have hleft : ∀ x ∈ U₁, dg G T x = dg G (Y₁ ∪ R) x := by
    intro x hx
    have he : (Y₁ ∪ R) ∪ Y₂ = T := by
      rw [union_assoc,union_comm R Y₂,← union_assoc,hcover]
    have hd := dg_union_of_disjoint (G := G)
      (disjoint_union_left.mpr ⟨hY₁₂,hY₂R.symm⟩) x
    have hz : dg G Y₂ x = 0 := dg_zero fun y hy => h.cross₁ x hx y (hY₂K hy)
    rw [he,hz] at hd
    omega
  have hright : ∀ x ∈ U₂, dg G T x = dg G (Y₂ ∪ R) x := by
    intro x hx
    have he : (Y₂ ∪ R) ∪ Y₁ = T := by
      rw [union_assoc,union_comm R Y₁,← union_assoc,union_comm Y₂ Y₁,hcover]
    have hd := dg_union_of_disjoint (G := G)
      (disjoint_union_left.mpr ⟨hY₁₂.symm,hY₁R.symm⟩) x
    have hz : dg G Y₁ x = 0 := dg_zero fun y hy => h.cross₂ x hx y (hY₁K hy)
    rw [he,hz] at hd
    omega
  have hcap : capped G U T = capped G U₁ (Y₁ ∪ R) + capped G U₂ (Y₂ ∪ R) := by
    unfold capped
    rw [← h.leftCover,sum_union h.leftDisjoint]
    congr 1
    · exact sum_congr rfl fun x hx => by rw [hleft x hx]
    · exact sum_congr rfl fun x hx => by rw [hright x hx]
  have hcuts := h.three_deficient_rank_cuts hi hthree hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR
  unfold rankTerm at hcuts
  omega


/-- Every fixed cross-lobe original degree-four pair works when at least three
original separator vertices are deficient. No lobe order bound is assumed. -/
theorem original_three_deficient_degreefour_fixed_omissions
    {U W S U₁ U₂ W₁ W₂ : Finset V}
    (hi : QB7Conditional.U2Input G U W) (h : Split G U W S U₁ U₂ W₁ W₂)
    (hthree : 3 ≤ #(S.filter fun s => dg G U s < 6))
    {z₁ z₂ : V} (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 4) (hd₂ : dg G U z₂ = 4) :
    FixedOmissionFactor G U W z₁ z₂ := by
  have hi' := U2Input.of_original hi
  exact factor_of_right_capped (h.retained_balanced hi' hz₁ hz₂)
    (fun T hT => h.three_deficient_capped_cuts hi' hthree hz₁ hz₂ hd₁ hd₂ hT)

#print axioms original_three_deficient_degreefour_fixed_omissions
#print original_three_deficient_degreefour_fixed_omissions
end Erdos585.QB7SmallLobeR643
