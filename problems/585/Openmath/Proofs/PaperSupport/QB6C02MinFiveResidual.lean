import Openmath.Proofs.PaperSupport.QB6C02MinFiveCore

/- 




-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
open Finset
open Erdos585.QB4 Erdos585.QB5 Erdos585.QB6Assembly
open Erdos585.QB6C02PartialFactor Erdos585.QB6C02NonlinearCore
open Erdos585.QB6C02NoTheta3 Erdos585.QB6C02Five4
namespace Erdos585.QB6C02MinFive
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def starPotential (B s : ℤ) : ℤ :=
  if s ≤ 0 then (if 13 ≤ B then 10 else (if 12 ≤ B then 8 else (if 7 ≤ B then 6 else (if 6 ≤ B then 4 else (if 5 ≤ B then 2 else (0)))))) else (if s ≤ 1 then (if 13 ≤ B then 13 else (if 12 ≤ B then 11 else (if 11 ≤ B then 9 else (if 6 ≤ B then 7 else (if 5 ≤ B then 5 else (if 4 ≤ B then 3 else (if 3 ≤ B then 1 else (0)))))))) else (if s ≤ 2 then (if 12 ≤ B then 14 else (if 11 ≤ B then 12 else (if 10 ≤ B then 10 else (if 5 ≤ B then 8 else (if 4 ≤ B then 6 else (if 3 ≤ B then 4 else (if 2 ≤ B then 2 else (0)))))))) else (if s ≤ 3 then (if 11 ≤ B then 15 else (if 10 ≤ B then 13 else (if 9 ≤ B then 11 else (if 4 ≤ B then 9 else (if 3 ≤ B then 7 else (if 2 ≤ B then 5 else (if 1 ≤ B then 3 else (if 0 ≤ B then 1 else (0))))))))) else (if 10 ≤ B then 16 else (if 9 ≤ B then 14 else (if 8 ≤ B then 12 else (if 3 ≤ B then 10 else (if 2 ≤ B then 8 else (if 1 ≤ B then 6 else (if 0 ≤ B then 4 else (0)))))))))))

lemma starPotential_nonneg (B s : ℤ) : 0 ≤ starPotential B s := by
  unfold starPotential
  omega

lemma starPotential_step (B s b a delta d : ℤ)
    (hB0 : 0 ≤ B) (hB : B ≤ 13) (hs0 : 0 ≤ s) (hs : s ≤ 4)
    (hb0 : 0 ≤ b) (hb : b ≤ B) (ha0 : 0 ≤ a) (ha : a ≤ s) (hdpos : 0 < delta)
    (hd : d ≤ 2) (hcost : 5 + d - a ≤ b) (hdelta : delta ≤ 2 + 2 * d + a) :
    delta + starPotential (B - b) (s - a) ≤ starPotential B s := by
  unfold starPotential
  omega

lemma star_resource_family {I : Type u} [DecidableEq I] (F : Finset I)
    (b a delta d : I → ℤ) (B s : ℤ)
    (hB0 : 0 ≤ B) (hB : B ≤ 13) (hs0 : 0 ≤ s) (hs : s ≤ 4)
    (hb0 : ∀ i ∈ F, 0 ≤ b i) (ha0 : ∀ i ∈ F, 0 ≤ a i)
    (hd0 : ∀ i ∈ F, 0 ≤ delta i)
    (hcost : ∑ i ∈ F, b i ≤ B) (hscar : ∑ i ∈ F, a i ≤ s)
    (hc : ∀ i ∈ F, d i ≤ 2 ∧ 5 + d i - a i ≤ b i ∧ delta i ≤ 2 + 2 * d i + a i) :
    (∑ i ∈ F, delta i) ≤ starPotential B s := by
  induction F using Finset.induction_on generalizing B s with
  | empty => simpa using starPotential_nonneg B s
  | @insert i F hi ih =>
    have hbFi := hb0 i (mem_insert_self i F)
    have haFi := ha0 i (mem_insert_self i F)
    have hdFi := hd0 i (mem_insert_self i F)
    have hbF : ∀ j ∈ F, 0 ≤ b j := fun j hj => hb0 j (mem_insert_of_mem hj)
    have haF : ∀ j ∈ F, 0 ≤ a j := fun j hj => ha0 j (mem_insert_of_mem hj)
    have hdF : ∀ j ∈ F, 0 ≤ delta j := fun j hj => hd0 j (mem_insert_of_mem hj)
    have hcF : ∀ j ∈ F, d j ≤ 2 ∧ 5 + d j - a j ≤ b j ∧ delta j ≤ 2 + 2 * d j + a j :=
      fun j hj => hc j (mem_insert_of_mem hj)
    rw [sum_insert hi] at hcost hscar ⊢
    have hbSum : (0 : ℤ) ≤ ∑ j ∈ F, b j := sum_nonneg hbF
    have haSum : (0 : ℤ) ≤ ∑ j ∈ F, a j := sum_nonneg haF
    by_cases hdz : delta i = 0
    · have hh := ih B s hB0 hB hs0 hs hbF haF hdF (by omega) (by omega) hcF
      omega
    · have hh := ih (B - b i) (s - a i) (by omega) (by omega) (by omega) (by omega)
        hbF haF hdF (by omega) (by omega) hcF
      have hic := hc i (mem_insert_self i F)
      have hstep := starPotential_step B s (b i) (a i) (delta i) (d i)
        hB0 hB hs0 hs hbFi (by omega) haFi (by omega) (by omega) hic.1 hic.2.1 hic.2.2
      omega

lemma star_resource_below_eleven {I : Type u} [DecidableEq I] (F : Finset I)
    (b a delta d : I → ℤ) (h : ℤ) (hh0 : 0 ≤ h) (hh : h ≤ 4)
    (hb0 : ∀ i ∈ F, 0 ≤ b i) (ha0 : ∀ i ∈ F, 0 ≤ a i)
    (hd0 : ∀ i ∈ F, 0 ≤ delta i)
    (hcost : ∑ i ∈ F, b i ≤ 13 - 3 * h) (hscar : ∑ i ∈ F, a i ≤ h)
    (hc : ∀ i ∈ F, d i ≤ 2 ∧ 5 + d i - a i ≤ b i ∧ delta i ≤ 2 + 2 * d i + a i) :
    (∑ i ∈ F, delta i) < 11 := by
  have hs := star_resource_family F b a delta d (13 - 3 * h) h
    (by omega) (by omega) hh0 hh hb0 ha0 hd0 hcost hscar hc
  interval_cases h <;> norm_num [starPotential] at hs <;> omega

lemma residual_high_deficit_one {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hH : H ∈ maxHighFamily G A C) : df G C H ≤ 1 := by
  have hd := high_data_all h hH
  have htB := theta_three h hd.1 hd.2.1
  by_cases ht3 : thetaC02 G C H = 3
  · have hl := theta3_original_loss h hd.1 ht3
    have he : (0 : ℤ) ≤ ec G H (C \ cpr G C H) := by positivity
    omega
  · have ht2 : thetaC02 G C H = 2 := by omega
    by_cases hdf : 0 < df G C H
    · obtain ⟨K, hK, p, hKdf, _, hpK, hHK, hp6, _⟩ := residual_high_shape h hm hr hapf hH ht2 hdf
      have hdH := df_sdiff_add (G := G) (S := C) (singleton_subset_iff.mpr (show p ∈ H by rw [hHK]; simp))
      have her : H \ {p} = K := by rw [hHK, sdiff_singleton_eq_erase, erase_insert hpK]
      have hdp : df G C ({p} : Finset V) = 0 := by simp [df, hp6]
      rw [her, hdp] at hdH
      omega
    · omega

variable (G) in
 def positiveStar (A C K : Finset V) : Finset (Finset V) :=
   (maxPositiveFamily G A C).filter fun T => K ⊆ T ∧ 0 < df G C (T \ K)

lemma mem_positiveStar {A C K T : Finset V} :
    T ∈ positiveStar G A C K ↔ T ∈ maxPositiveFamily G A C ∧ K ⊆ T ∧ 0 < df G C (T \ K) := mem_filter

lemma positiveStar_theta {A C K T : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1)
    (hT : T ∈ positiveStar G A C K) : thetaC02 G C T = 1 := by
  obtain ⟨hTF, hKT, hdT⟩ := mem_positiveStar.mp hT
  obtain ⟨hTA, h3T, htpos, _⟩ := maxPositive_data h hTF
  have hs := df_sdiff_add (G := G) (S := C) hKT
  have hdef : 2 ≤ df G C T := by omega
  by_contra hn
  obtain ⟨H, hH, hTH⟩ := high_extension (G := G) (C := C) hTA h3T (by omega)
  have hHdef := df_le_of_subset (G := G) hTH fun a ha => h.capA a ((high_data_all h hH).1 ha)
  have hb := residual_high_deficit_one h hm hr hapf hH
  omega

lemma core_subset_insert_eq {A C K L : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hL : L ∈ maxThetaThreeFamily G A C)
    {p : V} (hKL : K ⊆ insert p L) : K = L := by
  by_contra hn
  have hd := maximal_theta3_disjoint h hK hL hn
  have hs : K ⊆ {p} := by
    intro a ha
    rcases mem_insert.mp (hKL ha) with he | haL
    · exact mem_singleton.mpr he
    · exact False.elim (disjoint_left.mp hd ha haL)
  have hc := card_le_card hs
  have h3 := (theta3_large_proper h (core_data hK).1 (core_data hK).2.1).1
  simp only [card_singleton] at hc
  omega

lemma positiveStar_intersection {A C K T U : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1)
    (hT : T ∈ positiveStar G A C K) (hU : U ∈ positiveStar G A C K) (hne : T ≠ U) :
    T ∩ U = K ∨ ∃ p, Ordinary G A C p ∧ p ∉ K ∧ dg G C p = 6 ∧
      dg G (cpr G C K) p = 3 ∧ T ∩ U = insert p K := by
  obtain ⟨hTF, hKT, _⟩ := mem_positiveStar.mp hT
  obtain ⟨hUF, hKU, _⟩ := mem_positiveStar.mp hU
  obtain ⟨hTA, _, _, hmT⟩ := maxPositive_data h hTF
  obtain ⟨hUA, _, _, _⟩ := maxPositive_data h hUF
  have htT := positiveStar_theta h hm hr hapf hK hdK hT
  have htU := positiveStar_theta h hm hr hapf hK hdK hU
  have hnot : ¬ U ⊆ T := by
    intro hs
    obtain ⟨hTS, _⟩ := mem_maximalMembers.mp hTF
    obtain ⟨_, hmU⟩ := mem_maximalMembers.mp hUF
    exact hne (hmU T hTS hs)
  have hUn : T ∪ U ≠ T := by intro he; exact hnot (he ▸ subset_union_right)
  have hUb := hmT (T ∪ U) (union_subset hTA hUA) subset_union_left hUn
  have hKI := subset_inter hKT hKU
  have hK3 := (theta3_large_proper h (core_data hK).1 (core_data hK).2.1).1
  have hI3 := hK3.trans (card_le_card hKI)
  have hIb := theta_three h (inter_subset_left.trans hTA) hI3
  have hs := theta_supermodular (G := G) C T U
  have htI : 2 ≤ thetaC02 G C (T ∩ U) := by omega
  by_cases hi3 : thetaC02 G C (T ∩ U) = 3
  · exact Or.inl ((core_data hK).2.2 _ (inter_subset_left.trans hTA) hi3 hKI)
  · have hi2 : thetaC02 G C (T ∩ U) = 2 := by omega
    obtain ⟨H, hH, hIH⟩ := high_extension (G := G) (C := C) (inter_subset_left.trans hTA) hI3 htI
    have hdH : 0 < df G C H := by
      have hmH := df_le_of_subset (G := G) (hKI.trans hIH) fun a ha => h.capA a ((high_data_all h hH).1 ha)
      omega
    have htH : thetaC02 G C H = 2 := by
      have hd := high_data_all h hH
      have h3 := theta_three h hd.1 hd.2.1
      by_contra hh
      have ht3 : thetaC02 G C H = 3 := by omega
      have hHK := (core_data hK).2.2 H hd.1 ht3 (hKI.trans hIH)
      rw [hHK] at hIH
      have he := Subset.antisymm hIH hKI
      rw [he, (core_data hK).2.1] at hi2
      omega
    obtain ⟨L, hL, p, hdL, ho, hpL, hHL, hp6, hpY⟩ := residual_high_shape h hm hr hapf hH htH hdH
    have hKL : K = L := core_subset_insert_eq h hK hL (hHL ▸ hKI.trans hIH)
    subst L
    have hpI : p ∈ T ∩ U := by
      by_contra hn
      have hsub : T ∩ U ⊆ K := by
        intro a ha
        rcases mem_insert.mp (hHL ▸ hIH ha) with he | haK
        · exact False.elim (hn (he ▸ ha))
        · exact haK
      have he := Subset.antisymm hsub hKI
      rw [he, (core_data hK).2.1] at hi2
      omega
    have he : T ∩ U = insert p K := Subset.antisymm (hHL ▸ hIH) (insert_subset_iff.mpr ⟨hpI, hKI⟩)
    exact Or.inr ⟨p, ho, hpL, hp6, hpY, he⟩

lemma maxPositive_union_bound {A C T U : Finset V} (h : C02Input G A C)
    (hT : T ∈ maxPositiveFamily G A C) (hU : U ∈ maxPositiveFamily G A C) (hne : T ≠ U) :
    thetaC02 G C (T ∪ U) ≤ 0 := by
  obtain ⟨hTA, _, _, hmT⟩ := maxPositive_data h hT
  obtain ⟨hUA, _, _, _⟩ := maxPositive_data h hU
  have hnot : ¬ U ⊆ T := by
    intro hs
    obtain ⟨hTS, _⟩ := mem_maximalMembers.mp hT
    obtain ⟨_, hmU⟩ := mem_maximalMembers.mp hU
    exact hne (hmU T hTS hs)
  exact hmT _ (union_subset hTA hUA) subset_union_left (fun he => hnot (he ▸ subset_union_right))

lemma positive_core_closed {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1) :
    ec G K (C \ cpr G C K) = 0 ∧ ∀ c ∈ C \ cpr G C K, dg G K c = 0 := by
  have hl := theta3_original_loss h (core_data hK).1 (core_data hK).2.1
  have he : ec G K (C \ cpr G C K) = 0 := by omega
  refine ⟨he, ?_⟩
  intro c hc
  have hs := single_le_sum (f := fun c => dg G K c) (fun _ _ => Nat.zero_le _) hc
  change dg G K c ≤ ec G (C \ cpr G C K) K at hs
  rw [ec_comm, he] at hs
  omega

variable (G) in
 def starJ (C K T : Finset V) : Finset V :=
   (C \ cpr G C K).filter fun c => 3 ≤ dg G T c

lemma starJ_subset (C K T : Finset V) : starJ G C K T ⊆ C \ cpr G C K := filter_subset _ _

lemma star_cpr {A C K T : Finset V} (hKT : K ⊆ T) :
    cpr G C T = cpr G C K ∪ starJ G C K T := by
  apply Subset.antisymm
  · intro c hc
    by_cases hcK : c ∈ cpr G C K
    · exact mem_union_left _ hcK
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨(mem_cpr.mp hc).1, hcK⟩, (mem_cpr.mp hc).2⟩)
  · intro c hc
    rcases mem_union.mp hc with hc | hc
    · obtain ⟨hcC, hd⟩ := mem_cpr.mp hc
      exact mem_cpr.mpr ⟨hcC, hd.trans (dg_mono (G := G) hKT c)⟩
    · obtain ⟨hc, hd⟩ := mem_filter.mp hc
      exact mem_cpr.mpr ⟨(mem_sdiff.mp hc).1, hd⟩

lemma star_J_disjoint {A C K T U : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1)
    (hT : T ∈ positiveStar G A C K) (hU : U ∈ positiveStar G A C K) (hne : T ≠ U) :
    Disjoint (starJ G C K T) (starJ G C K U) := by
  have htT := positiveStar_theta h hm hr hapf hK hdK hT
  have htU := positiveStar_theta h hm hr hapf hK hdK hU
  have hUb := maxPositive_union_bound h (mem_positiveStar.mp hT).1 (mem_positiveStar.mp hU).1 hne
  have hgap := theta_gap_sum (G := G) C T U
  apply disjoint_left.mpr
  intro c hcT hcU
  have hcC := (mem_sdiff.mp (starJ_subset (G := G) C K T hcT)).1
  have hcNot := (mem_sdiff.mp (starJ_subset (G := G) C K T hcT)).2
  have hc3T := (mem_filter.mp hcT).2
  have hc3U := (mem_filter.mp hcU).2
  have hK0 := (positive_core_closed h hK hdK).2 c (mem_sdiff.mpr ⟨hcC, hcNot⟩)
  have hdu := dg_union_add_dg_inter (G := G) T U c
  have hsingle := single_le_sum (fun c _ => columnGap_nonneg (G := G) T U c) hcC
  have hnon := columnGap_nonneg (G := G) T U c
  rcases positiveStar_intersection h hm hr hapf hK hdK hT hU hne with hi | ⟨p, _, hpK, _, _, hi⟩
  · have htK := (core_data hK).2.1
    rw [hi, htK] at hgap
    rw [hi, hK0] at hdu
    have hg2 : 2 ≤ columnGap (G := G) T U c := by unfold columnGap; rw [hi, hK0]; omega
    omega
  · have htc : thetaC02 G C (insert p K) = 2 := by
      have hpT : p ∈ T := (inter_subset_left (s₁ := T) (s₂ := U)) (hi ▸ mem_insert_self p K)
      have hpo : Ordinary G A C p := by
        rcases positiveStar_intersection h hm hr hapf hK hdK hT hU hne with hi0 | ⟨q, hq, hqK, _, _, hiq⟩
        · have hpKi : p ∈ K := hi0 ▸ (hi ▸ mem_insert_self p K)
          exact False.elim (hpK hpKi)
        · have hpq : p = q := by
            have hpIq : p ∈ insert q K := hiq ▸ (hi ▸ mem_insert_self p K)
            rcases mem_insert.mp hpIq with he | hpK'
            · exact he
            · exact False.elim (hpK hpK')
          simpa [hpq] using hq
      have hcan := core_insert_cpr h (core_data hK).1 (core_data hK).2.1 hpK
      have heθ := theta_erase (G := G) (C := C) (T := insert p K) (mem_insert_self p K)
      rw [erase_insert hpK, hcan] at heθ
      have htK := (core_data hK).2.1
      rcases positiveStar_intersection h hm hr hapf hK hdK hT hU hne with hi0 | ⟨q, _, _, _, hq3, hiq⟩
      · exact False.elim (hpK (hi0 ▸ (hi ▸ mem_insert_self p K)))
      · have hpq : p = q := by
          rcases mem_insert.mp (hiq ▸ (hi ▸ mem_insert_self p K)) with he | hpK'
          · exact he
          · exact False.elim (hpK hpK')
        rw [← hpq] at hq3
        omega
    rw [hi, htc] at hgap
    have hI1 : dg G (insert p K) c ≤ 1 := by
      have hd := dg_union_of_disjoint (G := G) (disjoint_singleton_left.mpr hpK) c
      simp only [singleton_union] at hd
      have hh := dg_le_card (G := G) ({p} : Finset V) c
      simp only [card_singleton] at hh
      omega
    rw [hi] at hdu
    have hg1 : 1 ≤ columnGap (G := G) T U c := by unfold columnGap; rw [hi]; omega
    omega

lemma star_J_pairwise {A C K : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1) :
    (positiveStar G A C K : Set (Finset V)).PairwiseDisjoint (starJ G C K) :=
  fun _ hT _ hU hne => star_J_disjoint h hm hr hapf hK hdK hT hU hne

variable (G) in
 def starIncidence (A C K : Finset V) (p : V) : Finset (Finset V) :=
   (positiveStar G A C K).filter fun T => p ∈ T

variable (G) in
 def sharedRows (A C K : Finset V) : Finset V :=
   (A \ K).filter fun p => 2 ≤ #(starIncidence G A C K p)

lemma mem_sharedRows {A C K : Finset V} {p : V} :
    p ∈ sharedRows G A C K ↔ p ∈ A \ K ∧ 2 ≤ #(starIncidence G A C K p) := mem_filter

lemma shared_row_geometry {A C K : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1)
    {p : V} (hp : p ∈ sharedRows G A C K) :
    Ordinary G A C p ∧ dg G C p = 6 ∧ dg G (cpr G C K) p = 3 ∧
      dg G (C \ cpr G C K) p = 3 := by
  obtain ⟨hpAK, hp2⟩ := mem_sharedRows.mp hp
  obtain ⟨T, hT, U, hU, hne⟩ := one_lt_card.mp (show 1 < #(starIncidence G A C K p) by omega)
  obtain ⟨hTF, hpT⟩ := mem_filter.mp hT
  obtain ⟨hUF, hpU⟩ := mem_filter.mp hU
  rcases positiveStar_intersection h hm hr hapf hK hdK hTF hUF hne with hi | ⟨q, ho, hqK, hq6, hq3, hi⟩
  · exact False.elim ((mem_sdiff.mp hpAK).2 (hi ▸ mem_inter.mpr ⟨hpT, hpU⟩))
  · have hpq : p = q := by
      rcases mem_insert.mp (hi ▸ mem_inter.mpr ⟨hpT, hpU⟩) with he | hpK
      · exact he
      · exact False.elim ((mem_sdiff.mp hpAK).2 hpK)
    subst q
    have hd := dg_sdiff_add (G := G) (cpr_subset (G := G) C K) p
    exact ⟨ho, hq6, hq3, by omega⟩

lemma theta3_boundary {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) : ec G (A \ K) (cpr G C K) = 13 := by
  have hKA := (core_data hK).1
  have htK := (core_data hK).2.1
  obtain ⟨_, _, hcard, hedge, _⟩ := theta3_geometry h hKA htK
  have hsat : ec G A (cpr G C K) = 6 * #(cpr G C K) := by
    rw [ec_comm]
    unfold ec
    rw [sum_congr rfl (fun c hc => h.satC c (cpr_subset (G := G) C K hc))]
    simp [mul_comm]
  have hs := ec_sdiff_add_left (G := G) hKA (cpr G C K)
  have hsz : (ec G (A \ K) (cpr G C K) : ℤ) + ec G K (cpr G C K) = 6 * (#(cpr G C K) : ℤ) := by
    exact_mod_cast (hsat ▸ hs)
  have hcZ : (#(cpr G C K) : ℤ) = #K + 2 := by exact_mod_cast hcard
  omega

lemma shared_row_card {A C K : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1) :
    #(sharedRows G A C K) ≤ 4 := by
  have hs : ec G (sharedRows G A C K) (cpr G C K) = 3 * #(sharedRows G A C K) := by
    unfold ec
    rw [sum_congr rfl (fun p hp => (shared_row_geometry h hm hr hapf hK hdK hp).2.2.1)]
    simp [mul_comm]
  have hmE := ec_mono_left (G := G) (show sharedRows G A C K ⊆ A \ K from filter_subset _ _) (cpr G C K)
  rw [theta3_boundary h hK, hs] at hmE
  omega

lemma shared_ell_positive {A C K T : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1)
    (hT : T ∈ positiveStar G A C K) {p : V}
    (hp : p ∈ sharedRows G A C K) (hpT : p ∈ T) : 1 ≤ dg G (starJ G C K T) p := by
  have hg := shared_row_geometry h hm hr hapf hK hdK hp
  obtain ⟨hTF, hKT, hdefP⟩ := mem_positiveStar.mp hT
  obtain ⟨hTA, h3T, _, _⟩ := maxPositive_data h hTF
  have htT := positiveStar_theta h hm hr hapf hK hdK hT
  have hYJ : Disjoint (cpr G C K) (starJ G C K T) :=
    disjoint_left.mpr fun c hcY hcJ => (mem_sdiff.mp (starJ_subset (G := G) C K T hcJ)).2 hcY
  have hdu := dg_union_of_disjoint (G := G) hYJ p
  have hcan := star_cpr (G := G) (A := A) (C := C) hKT
  have he := theta_erase (G := G) (C := C) hpT
  rw [hcan] at he
  have h2 : 2 ≤ #(T.erase p) := by have hh := card_erase_add_one hpT; omega
  have heA : T.erase p ⊆ A := (erase_subset _ _).trans hTA
  by_contra hn
  have hell : dg G (starJ G C K T) p = 0 := by omega
  have htE : thetaC02 G C (T.erase p) = 2 := by omega
  have h3 : 3 ≤ #(T.erase p) := by
    by_contra hh
    have hs := theta_small (G := G) C (Z := T.erase p) (by omega)
    omega
  obtain ⟨H, hH, hEH⟩ := high_extension (G := G) (C := C) heA h3 (by omega)
  have hdT := df_sdiff_add (G := G) (S := C) hKT
  have hdE := df_sdiff_add (G := G) (S := C) (singleton_subset_iff.mpr hpT)
  have hsingle : df G C ({p} : Finset V) = 0 := by simp [df, hg.2.1]
  rw [sdiff_singleton_eq_erase, hsingle] at hdE
  have hEloss : 2 ≤ df G C (T.erase p) := by omega
  have hmon := df_le_of_subset (G := G) hEH fun a ha => h.capA a ((high_data_all h hH).1 ha)
  have hHloss := residual_high_deficit_one h hm hr hapf hH
  omega

lemma dg_biUnion {I : Type u} [DecidableEq I] (F : Finset I) (J : I → Finset V)
    (hJ : (F : Set I).PairwiseDisjoint J) (p : V) :
    dg G (F.biUnion J) p = ∑ T ∈ F, dg G (J T) p := by
  have hs := sum_biUnion (f := fun c => dg G ({p} : Finset V) c) hJ
  calc
    dg G (F.biUnion J) p = ec G {p} (F.biUnion J) := by simp [ec]
    _ = ec G (F.biUnion J) {p} := ec_comm _ _
    _ = ∑ T ∈ F, ec G (J T) {p} := hs
    _ = ∑ T ∈ F, dg G (J T) p := sum_congr rfl fun T _ => by rw [ec_comm]; simp [ec]

lemma shared_ell_sum {A C K : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1)
    {p : V} (hp : p ∈ sharedRows G A C K) :
    (∑ T ∈ starIncidence G A C K p, dg G (starJ G C K T) p) ≤ 3 := by
  have hsub : (positiveStar G A C K).biUnion (starJ G C K) ⊆ C \ cpr G C K := by
    intro c hc
    obtain ⟨T, _, hcT⟩ := mem_biUnion.mp hc
    exact starJ_subset (G := G) C K T hcT
  have hmono := dg_mono (G := G) hsub p
  have he := dg_biUnion (G := G) (positiveStar G A C K) (starJ G C K)
    (star_J_pairwise h hm hr hapf hK hdK) p
  have hgeom := (shared_row_geometry h hm hr hapf hK hdK hp).2.2.2
  have hs := sum_le_sum_of_subset_of_nonneg (show starIncidence G A C K p ⊆ positiveStar G A C K from filter_subset _ _)
    (f := fun T => dg G (starJ G C K T) p) (fun _ _ _ => Nat.zero_le _)
  omega

lemma shared_membership_scar {A C K : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1)
    {p : V} (hp : p ∈ sharedRows G A C K) :
    (∑ T ∈ starIncidence G A C K p, ((dg G (starJ G C K T) p : ℤ) - 1)) ≤ 1 := by
  have hs := shared_ell_sum h hm hr hapf hK hdK hp
  have hcard := (mem_sharedRows.mp hp).2
  have hsz : (∑ T ∈ starIncidence G A C K p, (dg G (starJ G C K T) p : ℤ)) ≤ 3 := by exact_mod_cast hs
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  omega

variable (G) in
 def starQ (A C K T : Finset V) : Finset V := (T \ K) \ sharedRows G A C K

variable (G) in
 def starRemoved (A C K T : Finset V) : Finset V := (T \ K) ∩ sharedRows G A C K

variable (G) in
 def starScar (A C K T : Finset V) : ℤ :=
   ∑ p ∈ starRemoved G A C K T, ((dg G (starJ G C K T) p : ℤ) - 1)

lemma removed_subset_S (A C K T : Finset V) :
    starRemoved G A C K T ⊆ sharedRows G A C K := inter_subset_right

lemma starQ_sdiff_removed (A C K T : Finset V) :
    starQ G A C K T = (T \ K) \ starRemoved G A C K T := by
  ext p
  simp only [starQ, starRemoved, mem_sdiff, mem_inter]
  tauto

lemma star_Q_pairwise {A C K : Finset V} (h : C02Input G A C) :
    (positiveStar G A C K : Set (Finset V)).PairwiseDisjoint (starQ G A C K) := by
  intro T hT U hU hne
  apply disjoint_left.mpr
  intro p hpT hpU
  obtain ⟨hpTK, hpNotS⟩ := mem_sdiff.mp hpT
  obtain ⟨hpUK, _⟩ := mem_sdiff.mp hpU
  have hpA := (maxPositive_data h (mem_positiveStar.mp hT).1).1 (mem_sdiff.mp hpTK).1
  have hcard : 2 ≤ #(starIncidence G A C K p) := by
    have hlt : 1 < #(starIncidence G A C K p) := one_lt_card.mpr ⟨T, mem_filter.mpr ⟨hT, (mem_sdiff.mp hpTK).1⟩,
      U, mem_filter.mpr ⟨hU, (mem_sdiff.mp hpUK).1⟩, hne⟩
    omega
  exact hpNotS (mem_sharedRows.mpr ⟨mem_sdiff.mpr ⟨hpA, (mem_sdiff.mp hpTK).2⟩, hcard⟩)

lemma starQ_union_subset {A C K : Finset V} (h : C02Input G A C) :
    (positiveStar G A C K).biUnion (starQ G A C K) ⊆ (A \ K) \ sharedRows G A C K := by
  intro p hp
  obtain ⟨T, hT, hpT⟩ := mem_biUnion.mp hp
  obtain ⟨hpTK, hpS⟩ := mem_sdiff.mp hpT
  obtain ⟨hpT, hpK⟩ := mem_sdiff.mp hpTK
  exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨(maxPositive_data h (mem_positiveStar.mp hT).1).1 hpT, hpK⟩, hpS⟩

lemma star_scar_nonneg {A C K T : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1)
    (hT : T ∈ positiveStar G A C K) : 0 ≤ starScar G A C K T := by
  apply sum_nonneg
  intro p hp
  have hell := shared_ell_positive h hm hr hapf hK hdK hT
    ((mem_inter.mp hp).2) (mem_sdiff.mp (mem_inter.mp hp).1).1
  omega

lemma star_scar_doublecount (A C K : Finset V) :
    (∑ T ∈ positiveStar G A C K, starScar G A C K T) =
      ∑ p ∈ sharedRows G A C K,
        ∑ T ∈ starIncidence G A C K p, ((dg G (starJ G C K T) p : ℤ) - 1) := by
  have hm : ∀ T, starRemoved G A C K T = (sharedRows G A C K).filter fun p => p ∈ T := by
    intro T
    ext p
    by_cases hpS : p ∈ sharedRows G A C K
    · have hpK := (mem_sdiff.mp (mem_sharedRows.mp hpS).1).2
      simp [starRemoved, hpS, hpK, and_comm]
    · simp [starRemoved, hpS]
  simp only [starScar, hm, sum_filter, starIncidence]
  rw [sum_comm]

lemma star_scar_budget {A C K : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1) :
    (∑ T ∈ positiveStar G A C K, starScar G A C K T) ≤ #(sharedRows G A C K) := by
  rw [star_scar_doublecount (G := G)]
  calc
    _ ≤ ∑ _p ∈ sharedRows G A C K, (1 : ℤ) :=
      sum_le_sum fun p hp => shared_membership_scar h hm hr hapf hK hdK hp
    _ = _ := by simp

lemma shared_original_deficit_zero {A C K : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1)
    {Z : Finset V} (hZ : Z ⊆ sharedRows G A C K) : df G C Z = 0 := by
  unfold df
  apply sum_eq_zero
  intro p hp
  have h6 := (shared_row_geometry h hm hr hapf hK hdK (hZ hp)).2.1
  omega

lemma star_part_exact {A C K T : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1)
    (hT : T ∈ positiveStar G A C K) :
    df G C (T \ K) + ec G (T \ K) (C \ (cpr G C K ∪ starJ G C K T)) =
      2 + 2 * ((#(T \ K) : ℤ) - #(starJ G C K T)) ∧
    gv G (T \ K) (starJ G C K T) =
      2 * (2 - ((#(T \ K) : ℤ) - #(starJ G C K T)) + ec G (T \ K) (cpr G C K)) ∧
    ((#(T \ K) : ℤ) - #(starJ G C K T)) ≤ 2 := by
  obtain ⟨hTF, hKT, _⟩ := mem_positiveStar.mp hT
  have htT := positiveStar_theta h hm hr hapf hK hdK hT
  have htK := (core_data hK).2.1
  have hY := cpr_subset (G := G) C K
  have hJ := starJ_subset (G := G) C K T
  have hYJ : Disjoint (cpr G C K) (starJ G C K T) :=
    disjoint_left.mpr fun c hcY hcJ => (mem_sdiff.mp (hJ hcJ)).2 hcY
  have hJU : cpr G C K ∪ starJ G C K T ⊆ C := union_subset hY (hJ.trans sdiff_subset)
  have hcan := star_cpr (G := G) (A := A) (C := C) hKT
  have hcP : (#(T \ K) : ℤ) + #K = #T := by exact_mod_cast card_sdiff_add_card_eq_card hKT
  have hcJ : (#(cpr G C K ∪ starJ G C K T) : ℤ) =
      #(cpr G C K) + #(starJ G C K T) := by exact_mod_cast card_union_of_disjoint hYJ
  have hePY : (ec G (T \ K) (cpr G C K) : ℤ) + ec G K (cpr G C K) = ec G T (cpr G C K) := by
    exact_mod_cast ec_sdiff_add_left (G := G) hKT (cpr G C K)
  have hePJ : (ec G (T \ K) (starJ G C K T) : ℤ) + ec G K (starJ G C K T) = ec G T (starJ G C K T) := by
    exact_mod_cast ec_sdiff_add_left (G := G) hKT (starJ G C K T)
  have heKJ : ec G K (starJ G C K T) = 0 := by
    rw [ec_comm]
    unfold ec
    exact sum_eq_zero fun c hc => (positive_core_closed h hK hdK).2 c (hJ hc)
  have hKY := (theta3_geometry h (core_data hK).1 htK).2.2.2.1
  have hCY := (theta3_geometry h (core_data hK).1 htK).2.2.1
  have hCYz : (#(cpr G C K) : ℤ) = #K + 2 := by exact_mod_cast hCY
  have hselected := theta_canonical (G := G) C T
  rw [hcan] at hselected
  have heTYJ : (ec G T (cpr G C K ∪ starJ G C K T) : ℤ) =
      ec G T (cpr G C K) + ec G T (starJ G C K T) := by
    have he : ec G T (cpr G C K ∪ starJ G C K T) = ec G T (cpr G C K) + ec G T (starJ G C K T) := by
      unfold ec
      rw [← sum_add_distrib]
      exact sum_congr rfl fun p _ => dg_union_of_disjoint hYJ p
    exact_mod_cast he
  have hePC : (ec G (T \ K) (C \ (cpr G C K ∪ starJ G C K T)) : ℤ) +
      ec G (T \ K) (cpr G C K) + ec G (T \ K) (starJ G C K T) = ec G (T \ K) C := by
    have he := ec_sdiff_add_right (G := G) hJU (T \ K)
    have heU : ec G (T \ K) (cpr G C K ∪ starJ G C K T) =
        ec G (T \ K) (cpr G C K) + ec G (T \ K) (starJ G C K T) := by
      unfold ec
      rw [← sum_add_distrib]
      exact sum_congr rfl fun p _ => dg_union_of_disjoint hYJ p
    rw [heU, ← add_assoc] at he
    exact_mod_cast he
  have hdef := df_eq (G := G) C (T \ K)
  have hA := (maxPositive_data h hTF).1
  have h3 := (maxPositive_data h hTF).2.1
  have hneq : T ≠ A := by intro he; rw [he, theta_whole h] at htT; omega
  have hb := (theta_proper_bounds h hA hneq h3).1
  rw [hcan] at hb
  refine ⟨by linarith, ?_, by omega⟩
  unfold gv
  linarith

lemma starQ_deficit {A C K T : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1) :
    df G C (starQ G A C K T) = df G C (T \ K) := by
  have hMsub : starRemoved G A C K T ⊆ T \ K := inter_subset_left
  have hz := shared_original_deficit_zero h hm hr hapf hK hdK (removed_subset_S (G := G) A C K T)
  have hs := df_sdiff_add (G := G) (S := C) hMsub
  rw [← starQ_sdiff_removed (G := G), hz] at hs
  omega

lemma starQ_positive {A C K T : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1)
    (hT : T ∈ positiveStar G A C K) : 0 < df G C (starQ G A C K T) := by
  rw [starQ_deficit h hm hr hapf hK hdK]
  exact (mem_positiveStar.mp hT).2.2

lemma star_Q_contains_core {A C K T : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1)
    (hT : T ∈ positiveStar G A C K) :
    ∃ L ∈ maxThetaThreeFamily G A C, L ⊆ starQ G A C K T := by
  have hTA := (maxPositive_data h (mem_positiveStar.mp hT).1).1
  have hQA : starQ G A C K T ⊆ A := sdiff_subset.trans (sdiff_subset.trans hTA)
  obtain ⟨p, hp, hp5⟩ := positive_deficit_row h hm hQA (starQ_positive h hm hr hapf hK hdK hT)
  obtain ⟨L, hL, hpL⟩ := hr p (hQA hp) hp5
  have hpT : p ∈ T := (mem_sdiff.mp (mem_sdiff.mp hp).1).1
  have hpK : p ∉ K := (mem_sdiff.mp (mem_sdiff.mp hp).1).2
  have hne : L ≠ K := fun he => hpK (he ▸ hpL)
  have hLK := maximal_theta3_disjoint h hL hK hne
  have hLT : L ⊆ T := by
    rcases n1_nesting h (core_data hL).1 (core_data hL).2.1 (mem_positiveStar.mp hT).1 with hd | hs
    · exact False.elim (disjoint_left.mp hd hpL hpT)
    · exact hs
  refine ⟨L, hL, ?_⟩
  intro q hqL
  refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hLT hqL, fun hqK => disjoint_left.mp hLK hqL hqK⟩, ?_⟩
  intro hqS
  exact (shared_row_geometry h hm hr hapf hK hdK hqS).1 L hL hqL

lemma star_Q_sparse {A C K T : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1)
    (hT : T ∈ positiveStar G A C K) : 14 ≤ gv G (starQ G A C K T) (starJ G C K T) := by
  have hTA := (maxPositive_data h (mem_positiveStar.mp hT).1).1
  have hQA : starQ G A C K T ⊆ A := sdiff_subset.trans (sdiff_subset.trans hTA)
  have hJC : starJ G C K T ⊆ C := (starJ_subset (G := G) C K T).trans sdiff_subset
  obtain ⟨L, hL, hLQ⟩ := star_Q_contains_core h hm hr hapf hK hdK hT
  have hQ3 : 3 ≤ #(starQ G A C K T) :=
    ((theta3_large_proper h (core_data hL).1 (core_data hL).2.1).1).trans (card_le_card hLQ)
  have hK3 := (theta3_large_proper h (core_data hK).1 (core_data hK).2.1).1
  have hQAminus : starQ G A C K T ⊆ A \ K := by
    intro p hp
    obtain ⟨hpTK, _⟩ := mem_sdiff.mp hp
    obtain ⟨hpT, hpK⟩ := mem_sdiff.mp hpTK
    exact mem_sdiff.mpr ⟨hTA hpT, hpK⟩
  have hQcard := card_le_card hQAminus
  have hAcard := card_sdiff_add_card_eq_card (core_data hK).1
  have hJcard := card_le_card hJC
  exact h.sparse _ hQA _ hJC (by omega) (by omega)

lemma star_covers_five {A C K : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1)
    {p : V} (hp : p ∈ A \ K) (hp5 : dg G C p = 5) :
    p ∈ (positiveStar G A C K).biUnion (starQ G A C K) := by
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < #K by
    have h3 := (theta3_large_proper h (core_data hK).1 (core_data hK).2.1).1
    omega)
  have hap : a ≠ p := fun he => (mem_sdiff.mp hp).2 (he ▸ ha)
  obtain ⟨T, hT, haT, hpT⟩ := hapf a ((core_data hK).1 ha) p (mem_sdiff.mp hp).1 hap
  have hKT : K ⊆ T := by
    rcases n1_nesting h (core_data hK).1 (core_data hK).2.1 hT with hd | hs
    · exact False.elim (disjoint_left.mp hd ha haT)
    · exact hs
  have hTA := (maxPositive_data h hT).1
  have hpP : p ∈ T \ K := mem_sdiff.mpr ⟨hpT, (mem_sdiff.mp hp).2⟩
  have hdP : 0 < df G C (T \ K) := by
    have hsingle : (6 : ℤ) - (dg G C p : ℤ) ≤ df G C (T \ K) :=
      single_le_sum (f := fun q => (6 : ℤ) - (dg G C q : ℤ))
        (fun q hq => by have hh := h.capA q (hTA (mem_sdiff.mp hq).1); omega) hpP
    omega
  have hTS := mem_positiveStar.mpr ⟨hT, hKT, hdP⟩
  have hpS : p ∉ sharedRows G A C K := by
    intro hpS
    have h6 := (shared_row_geometry h hm hr hapf hK hdK hpS).2.1
    omega
  exact mem_biUnion.mpr ⟨T, hTS, mem_sdiff.mpr ⟨hpP, hpS⟩⟩

lemma star_deficit_sum {A C K : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1) :
    (∑ T ∈ positiveStar G A C K, df G C (starQ G A C K T)) = 11 := by
  let U := (positiveStar G A C K).biUnion (starQ G A C K)
  have hsub : U ⊆ A \ K := (starQ_union_subset (K := K) h).trans sdiff_subset
  have hz : df G C ((A \ K) \ U) = 0 := by
    unfold df
    apply sum_eq_zero
    intro p hp
    obtain ⟨hpAK, hpN⟩ := mem_sdiff.mp hp
    have hpA := (mem_sdiff.mp hpAK).1
    have h5 := hm p hpA
    have h6 := h.capA p hpA
    have hn : dg G C p ≠ 5 := fun he => hpN (star_covers_five h hm hr hapf hK hdK hpAK he)
    omega
  have hdU := df_sdiff_add (G := G) (S := C) hsub
  have hdAK := df_sdiff_add (G := G) (S := C) (core_data hK).1
  have htot := c02_total_deficit h
  have hsum := sum_biUnion (f := fun p => (6 : ℤ) - (dg G C p : ℤ)) (star_Q_pairwise (K := K) h)
  change df G C U = ∑ T ∈ positiveStar G A C K, df G C (starQ G A C K T) at hsum
  omega

lemma star_boundary_budget {A C K : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1) :
    (∑ T ∈ positiveStar G A C K, (ec G (starQ G A C K T) (cpr G C K) : ℤ)) ≤
      13 - 3 * (#(sharedRows G A C K) : ℤ) := by
  have hs := sum_biUnion (f := fun p => dg G (cpr G C K) p) (star_Q_pairwise (K := K) h)
  have hmE := ec_mono_left (G := G) (starQ_union_subset (K := K) h) (cpr G C K)
  have hbound : (∑ T ∈ positiveStar G A C K, (ec G (starQ G A C K T) (cpr G C K) : ℤ)) ≤
      ec G ((A \ K) \ sharedRows G A C K) (cpr G C K) := by
    unfold ec at hmE
    rw [hs] at hmE
    exact_mod_cast hmE
  have he := ec_sdiff_add_left (G := G) (show sharedRows G A C K ⊆ A \ K from filter_subset _ _) (cpr G C K)
  have heS : ec G (sharedRows G A C K) (cpr G C K) = 3 * #(sharedRows G A C K) := by
    unfold ec
    rw [sum_congr rfl (fun p hp => (shared_row_geometry h hm hr hapf hK hdK hp).2.2.1)]
    simp [mul_comm]
  rw [theta3_boundary h hK, heS] at he
  have heZ : (ec G ((A \ K) \ sharedRows G A C K) (cpr G C K) : ℤ) +
      3 * #(sharedRows G A C K) = 13 := by exact_mod_cast he
  omega

lemma star_removed_Y {A C K T : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1) :
    ec G (starRemoved G A C K T) (cpr G C K) = 3 * #(starRemoved G A C K T) := by
  unfold ec
  rw [sum_congr rfl (fun p hp => (shared_row_geometry h hm hr hapf hK hdK
    (removed_subset_S (G := G) A C K T hp)).2.2.1)]
  simp [mul_comm]

lemma star_removed_J (A C K T : Finset V) :
    (ec G (starRemoved G A C K T) (starJ G C K T) : ℤ) =
      starScar G A C K T + #(starRemoved G A C K T) := by
  unfold starScar ec
  rw [Nat.cast_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
  ring

lemma star_removed_out {A C K T : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1) :
    (ec G (starRemoved G A C K T) (C \ (cpr G C K ∪ starJ G C K T)) : ℤ) +
      starScar G A C K T = 2 * #(starRemoved G A C K T) := by
  have hYJ : Disjoint (cpr G C K) (starJ G C K T) :=
    disjoint_left.mpr fun c hcY hcJ => (mem_sdiff.mp (starJ_subset (G := G) C K T hcJ)).2 hcY
  have hUC : cpr G C K ∪ starJ G C K T ⊆ C :=
    union_subset (cpr_subset (G := G) C K) ((starJ_subset (G := G) C K T).trans sdiff_subset)
  have heM : ec G (starRemoved G A C K T) C = 6 * #(starRemoved G A C K T) := by
    unfold ec
    rw [sum_congr rfl (fun p hp => (shared_row_geometry h hm hr hapf hK hdK
      (removed_subset_S (G := G) A C K T hp)).2.1)]
    simp [mul_comm]
  have heU : ec G (starRemoved G A C K T) (cpr G C K ∪ starJ G C K T) =
      ec G (starRemoved G A C K T) (cpr G C K) + ec G (starRemoved G A C K T) (starJ G C K T) := by
    unfold ec
    rw [← sum_add_distrib]
    exact sum_congr rfl fun p _ => dg_union_of_disjoint hYJ p
  have he := ec_sdiff_add_right (G := G) hUC (starRemoved G A C K T)
  rw [heU, heM, star_removed_Y h hm hr hapf hK hdK] at he
  have heZ : (ec G (starRemoved G A C K T) (C \ (cpr G C K ∪ starJ G C K T)) : ℤ) +
      (3 * #(starRemoved G A C K T) + (ec G (starRemoved G A C K T) (starJ G C K T) : ℤ)) =
      6 * #(starRemoved G A C K T) := by exact_mod_cast he
  have hj := star_removed_J (G := G) A C K T
  linarith

lemma star_deleted_exact {A C K T : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1)
    (hT : T ∈ positiveStar G A C K) :
    df G C (starQ G A C K T) + ec G (starQ G A C K T) (C \ (cpr G C K ∪ starJ G C K T)) =
      2 + 2 * ((#(starQ G A C K T) : ℤ) - #(starJ G C K T)) + starScar G A C K T ∧
    gv G (starQ G A C K T) (starJ G C K T) =
      2 * (2 - ((#(starQ G A C K T) : ℤ) - #(starJ G C K T)) +
        ec G (starQ G A C K T) (cpr G C K) + starScar G A C K T) ∧
    ((#(starQ G A C K T) : ℤ) - #(starJ G C K T)) ≤ 2 := by
  let M := starRemoved G A C K T
  have hMP : M ⊆ T \ K := inter_subset_left
  have hc : (#(starQ G A C K T) : ℤ) + #M = #(T \ K) := by
    have hh := card_sdiff_add_card_eq_card hMP
    rw [← starQ_sdiff_removed (G := G)] at hh
    exact_mod_cast hh
  have heY : (ec G (starQ G A C K T) (cpr G C K) : ℤ) + ec G M (cpr G C K) = ec G (T \ K) (cpr G C K) := by
    have hh := ec_sdiff_add_left (G := G) hMP (cpr G C K)
    rw [← starQ_sdiff_removed (G := G)] at hh
    exact_mod_cast hh
  have heJ : (ec G (starQ G A C K T) (starJ G C K T) : ℤ) + ec G M (starJ G C K T) = ec G (T \ K) (starJ G C K T) := by
    have hh := ec_sdiff_add_left (G := G) hMP (starJ G C K T)
    rw [← starQ_sdiff_removed (G := G)] at hh
    exact_mod_cast hh
  have heO : (ec G (starQ G A C K T) (C \ (cpr G C K ∪ starJ G C K T)) : ℤ) +
      ec G M (C \ (cpr G C K ∪ starJ G C K T)) = ec G (T \ K) (C \ (cpr G C K ∪ starJ G C K T)) := by
    have hh := ec_sdiff_add_left (G := G) hMP (C \ (cpr G C K ∪ starJ G C K T))
    rw [← starQ_sdiff_removed (G := G)] at hh
    exact_mod_cast hh
  have hY := star_removed_Y h hm hr hapf hK hdK (T := T)
  have hYZ : (ec G M (cpr G C K) : ℤ) = 3 * #M := by exact_mod_cast hY
  have hJ := star_removed_J (G := G) A C K T
  change (ec G M (starJ G C K T) : ℤ) = starScar G A C K T + #M at hJ
  have hO := star_removed_out h hm hr hapf hK hdK (T := T)
  change (ec G M (C \ (cpr G C K ∪ starJ G C K T)) : ℤ) + starScar G A C K T = 2 * #M at hO
  have hδ := starQ_deficit h hm hr hapf hK hdK (T := T)
  have he := star_part_exact h hm hr hapf hK hdK hT
  have hcard := card_le_card (show starQ G A C K T ⊆ T \ K from sdiff_subset)
  refine ⟨by linarith [he.1], ?_, by omega⟩
  have hgP := he.2.1
  unfold gv at hgP ⊢
  linarith

lemma star_actual_items {A C K : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hdK : df G C K = 1) :
    ∀ T ∈ positiveStar G A C K,
      ((#(starQ G A C K T) : ℤ) - #(starJ G C K T)) ≤ 2 ∧
      5 + ((#(starQ G A C K T) : ℤ) - #(starJ G C K T)) - starScar G A C K T ≤
        ec G (starQ G A C K T) (cpr G C K) ∧
      df G C (starQ G A C K T) ≤
        2 + 2 * ((#(starQ G A C K T) : ℤ) - #(starJ G C K T)) + starScar G A C K T := by
  intro T hT
  have he := star_deleted_exact h hm hr hapf hK hdK hT
  have hg := star_Q_sparse h hm hr hapf hK hdK hT
  have ho : (0 : ℤ) ≤ ec G (starQ G A C K T) (C \ (cpr G C K ∪ starJ G C K T)) := by positivity
  exact ⟨he.2.2, by linarith [he.2.1], by linarith [he.1]⟩

lemma residual_apf_impossible {A C : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C) : False := by
  obtain ⟨p, hp, hp5⟩ := positive_deficit_row h hm (subset_refl A) (by rw [c02_total_deficit h]; norm_num)
  obtain ⟨K, hK, hpK⟩ := hr p hp hp5
  have hδ : df G C K = 1 := by
    have hb := core_loss_bound h hK
    have hs : (6 : ℤ) - (dg G C p : ℤ) ≤ df G C K :=
      single_le_sum (f := fun q => (6 : ℤ) - (dg G C q : ℤ))
        (fun q hq => by have hh := h.capA q ((core_data hK).1 hq); omega) hpK
    omega
  have hS := shared_row_card h hm hr hapf hK hδ
  have hB := star_boundary_budget h hm hr hapf hK hδ
  have ha := star_scar_budget h hm hr hapf hK hδ
  have hloss := star_deficit_sum h hm hr hapf hK hδ
  have hout := star_resource_below_eleven (positiveStar G A C K)
    (fun T => (ec G (starQ G A C K T) (cpr G C K) : ℤ))
    (starScar G A C K) (fun T => df G C (starQ G A C K T))
    (fun T => (#(starQ G A C K T) : ℤ) - #(starJ G C K T))
    (#(sharedRows G A C K) : ℤ) (by positivity) (by exact_mod_cast hS)
    (fun _ _ => by positivity) (fun _ hT => star_scar_nonneg h hm hr hapf hK hδ hT)
    (fun _ hT => le_of_lt (starQ_positive h hm hr hapf hK hδ hT)) hB ha
    (star_actual_items h hm hr hapf hK hδ)
  omega

def PositiveCoreResidualGoodPair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V), C02Input G A C → MinFive G A C → PositiveCoreResidual G A C →
      ∃ D, GoodPair G A C D

theorem residual_good_pair : PositiveCoreResidualGoodPair.{u} := by
  classical
  intro V _ G _ A C h hm hr
  by_contra hn
  have hapf := apf_of_no_good_pair h (fun D _ _ hg => hn ⟨D, hg⟩)
  exact residual_apf_impossible h hm hr hapf

end Erdos585.QB6C02MinFive
