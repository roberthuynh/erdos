import Openmath.Proofs.PaperSupport.QB6C02NoTheta3
import Openmath.Proofs.PaperSupport.QB6C02TwoScarResource

/- 


-/
open Finset
open Erdos585.QB4 Erdos585.QB5 Erdos585.QB6Assembly
open Erdos585.QB6C02PartialFactor Erdos585.QB6C02NonlinearCore
open Erdos585.QB6C02NoTheta3
namespace Erdos585.QB6C02Five4
universe u
variable {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
set_option maxHeartbeats 1800000

def degreeFourRows (A C : Finset V) : Finset V := A.filter fun a => dg G C a = 4

def Five4GoodPair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V), C02Input G A C → 5 ≤ #(degreeFourRows G A C) →
      ∃ D, GoodPair G A C D

def Five4Repair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V), C02Input G A C → 5 ≤ #(degreeFourRows G A C) → Quartic G A C

variable {G}

omit [DecidableEq V] in
lemma mem_degreeFourRows {A C : Finset V} {a : V} :
    a ∈ degreeFourRows G A C ↔ a ∈ A ∧ dg G C a = 4 := mem_filter

omit [DecidableEq V] in
lemma theta_loss_identity (C Z : Finset V) :
    thetaC02 G C Z + df G (cpr G C Z) Z = 8 + 2 * ((#Z : ℤ) - #(cpr G C Z)) := by
  have ht := theta_canonical (G := G) C Z
  rw [df_eq]
  linarith

omit [DecidableEq V] in
lemma theta_loss_bound {A C Z : Finset V} (h : C02Input G A C)
    (hZ : Z ⊆ A) (hne : Z ≠ A) (h3 : 3 ≤ #Z) :
    3 * thetaC02 G C Z + df G (cpr G C Z) Z ≤ 10 := by
  have hb := (theta_proper_bounds h hZ hne h3).1
  have ht := theta_loss_identity (G := G) C Z
  linarith

lemma theta3_original_loss {A C K : Finset V} (h : C02Input G A C)
    (hK : K ⊆ A) (ht : thetaC02 G C K = 3) :
    df G C K + (ec G K (C \ cpr G C K) : ℤ) = 1 := by
  have he := (theta3_geometry h hK ht).2.2.2.1
  have hd : df G (cpr G C K) K = 1 := by rw [df_eq]; omega
  rw [df_eq_df_add_ec (G := G) (cpr_subset (G := G) C K) K] at hd
  exact hd

omit [DecidableEq V] in
lemma theta3_no_four {A C K : Finset V} (h : C02Input G A C)
    (hK : K ⊆ A) (ht : thetaC02 G C K = 3) {p : V} (hp : p ∈ K) : dg G C p ≠ 4 := by
  have hd := (theta3_geometry h hK ht).2.2.2.2.2 p hp
  have hm := dg_mono (G := G) (cpr_subset (G := G) C K) p
  omega

lemma theta_with_four_le_two {A C Z : Finset V} (h : C02Input G A C)
    (hZ : Z ⊆ A) (h2 : 2 ≤ #Z) {p : V} (hp : p ∈ Z) (hp4 : dg G C p = 4) :
    thetaC02 G C Z ≤ 2 := by
  by_cases h3 : 3 ≤ #Z
  · have hb := theta_three h hZ h3
    have hn : thetaC02 G C Z ≠ 3 := fun he => theta3_no_four h hZ he hp hp4
    omega
  · have hs := theta_small (G := G) C (Z := Z) (by omega)
    omega

lemma high_data {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (ht : thetaC02 G C K = 2) :
    K ⊆ A ∧ 3 ≤ #K ∧ K ≠ A ∧
      ∀ U, U ⊆ A → K ⊆ U → U ≠ K → thetaC02 G C U ≤ 1 := by
  obtain ⟨hs, hm⟩ := mem_maximalMembers.mp hK
  obtain ⟨hKA, h3, _⟩ := mem_highSets.mp hs
  have hne : K ≠ A := by intro he; rw [he, theta_whole h] at ht; omega
  refine ⟨hKA, h3, hne, ?_⟩
  intro U hUA hKU hUK
  by_contra hh
  have hc := card_le_card hKU
  exact hUK (hm U (mem_highSets.mpr ⟨hUA, by omega, by omega⟩) hKU)

lemma high_four_theta {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) {p : V} (hp : p ∈ K) (hp4 : dg G C p = 4) :
    thetaC02 G C K = 2 := by
  obtain ⟨hs, _⟩ := mem_maximalMembers.mp hK
  obtain ⟨hKA, h3, ht⟩ := mem_highSets.mp hs
  have hle := theta_with_four_le_two h hKA (by omega) hp hp4
  omega

lemma high_geometry {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (ht : thetaC02 G C K = 2) :
    (highLoss G C K = 0 ∨ highLoss G C K = 2 ∨ highLoss G C K = 4) ∧
    highLoss G C K = 6 + 2 * ((#K : ℤ) - #(corePlus G C K)) ∧
    14 ≤ gv G K (corePlus G C K) := by
  obtain ⟨hKA, h3K, hneK, _⟩ := high_data h hK ht
  have hY := corePlus_subset (G := G) C K
  have hcK := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hKA, hneK⟩)
  have hcY := card_le_card hY
  have hg := h.sparse K hKA (corePlus G C K) hY (by omega) (by omega)
  have hcap : ec G K (corePlus G C K) ≤ 6 * #K :=
    ec_le_six_mul fun a ha => (dg_mono hY a).trans (h.capA a (hKA ha))
  have hcapz : (ec G K (corePlus G C K) : ℤ) ≤ 6 * (#K : ℤ) := by exact_mod_cast hcap
  have htheta := theta_corePlus (G := G) C K
  have hl : highLoss G C K = 6 + 2 * ((#K : ℤ) - #(corePlus G C K)) := by
    unfold highLoss; linarith
  have hh : 0 ≤ highLoss G C K := by unfold highLoss; omega
  have hk : (#K : ℤ) - #(corePlus G C K) ≤ -1 := by unfold gv at hg; omega
  exact ⟨by omega, hl, hg⟩

lemma high_boundary {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (ht : thetaC02 G C K = 2) :
    (ec G (A \ K) (corePlus G C K) : ℤ) = 18 - 2 * highLoss G C K := by
  have hKA := (high_data h hK ht).1
  have hl := (high_geometry h hK ht).2.1
  have hY := corePlus_subset (G := G) C K
  have he : ec G A (corePlus G C K) = 6 * #(corePlus G C K) := by
    rw [ec_comm]; unfold ec
    rw [sum_congr rfl (fun c hc => h.satC c (hY hc)), sum_const, smul_eq_mul, mul_comm]
  have hs := ec_sdiff_add_left (G := G) hKA (corePlus G C K)
  have hsz : (ec G (A \ K) (corePlus G C K) : ℤ) + ec G K (corePlus G C K) =
      6 * (#(corePlus G C K) : ℤ) := by exact_mod_cast (he ▸ hs)
  unfold highLoss at hl ⊢
  linarith

lemma high_outside_alpha {C K : Finset V} :
    (ec G K (C \ corePlus G C K) : ℤ) = highLoss G C K - df G C K := by
  have hd := df_eq_df_add_ec (G := G) (corePlus_subset (G := G) C K) K
  have hl : df G (corePlus G C K) K = highLoss G C K := df_eq _ _
  rw [hl] at hd
  omega

variable (G) in
def strictContainingFamily (A C K : Finset V) : Finset (Finset V) :=
  (maxPositiveFamily G A C).filter fun T => K ⊆ T ∧ T ≠ K

lemma mem_strictContainingFamily {A C K T : Finset V} :
    T ∈ strictContainingFamily G A C K ↔
      T ∈ maxPositiveFamily G A C ∧ K ⊆ T ∧ T ≠ K := mem_filter

lemma strict_theta {A C K T : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2)
    (hT : T ∈ strictContainingFamily G A C K) : thetaC02 G C T = 1 := by
  obtain ⟨hTF, hKT, hne⟩ := mem_strictContainingFamily.mp hT
  have hTA := (maxPositive_data h hTF).1
  have hpos := (maxPositive_data h hTF).2.2.1
  have hbound := (high_data h hK htK).2.2.2 T hTA hKT hne
  omega

lemma strict_intersection {A C K T U : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2)
    (hT : T ∈ strictContainingFamily G A C K) (hU : U ∈ strictContainingFamily G A C K)
    (hne : T ≠ U) : T ∩ U = K ∧ thetaC02 G C (T ∪ U) = 0 ∧
      ∀ c ∈ C, columnGap (G := G) T U c = 0 := by
  obtain ⟨hTF, hKT, _⟩ := mem_strictContainingFamily.mp hT
  obtain ⟨hUF, hKU, _⟩ := mem_strictContainingFamily.mp hU
  obtain ⟨hTA, _, _, hmT⟩ := maxPositive_data h hTF
  obtain ⟨hUA, _, _, _⟩ := maxPositive_data h hUF
  have hUn : T ∪ U ≠ T := by
    intro he
    obtain ⟨hTs, _⟩ := mem_maximalMembers.mp hTF
    obtain ⟨_, hmU⟩ := mem_maximalMembers.mp hUF
    exact hne (hmU T hTs (he ▸ subset_union_right))
  have hUnb := hmT (T ∪ U) (union_subset hTA hUA) subset_union_left hUn
  have htT := strict_theta h hK htK hT
  have htU := strict_theta h hK htK hU
  have hKI : K ⊆ T ∩ U := subset_inter hKT hKU
  have hI3 := card_le_card hKI
  have h3K := (high_data h hK htK).2.1
  have hs := theta_supermodular (G := G) C T U
  have hIθ : 2 ≤ thetaC02 G C (T ∩ U) := by omega
  obtain ⟨_, hmK⟩ := mem_maximalMembers.mp hK
  have hI := hmK (T ∩ U)
    (mem_highSets.mpr ⟨inter_subset_left.trans hTA, by omega, hIθ⟩) hKI
  have hg := theta_gap_sum (G := G) C T U
  rw [hI, htK, htT, htU] at hg
  have hsum0 : (∑ c ∈ C, columnGap (G := G) T U c) = 0 := by
    have hnon : (0 : ℤ) ≤ ∑ c ∈ C, columnGap (G := G) T U c :=
      sum_nonneg fun c _ => columnGap_nonneg (G := G) T U c
    omega
  refine ⟨hI, by omega, ?_⟩
  intro c hc
  have hs := single_le_sum (fun c _ => columnGap_nonneg (G := G) T U c) hc
  have hn := columnGap_nonneg (G := G) T U c
  omega


lemma strict_petals_pairwise {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2) :
    (strictContainingFamily G A C K : Set (Finset V)).PairwiseDisjoint (fun T => T \ K) := by
  intro T hT U hU hne
  apply disjoint_left.mpr
  intro a ha hb
  have hi := (strict_intersection h hK htK hT hU hne).1
  obtain ⟨haT, haK⟩ := mem_sdiff.mp ha
  have haU := (mem_sdiff.mp hb).1
  exact haK (hi ▸ mem_inter.mpr ⟨haT, haU⟩)

lemma strict_Jparts_pairwise {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2) :
    (strictContainingFamily G A C K : Set (Finset V)).PairwiseDisjoint (petalJ G C K) := by
  intro T hT U hU hne
  apply disjoint_left.mpr
  intro c hc hd
  obtain ⟨hi, _, hg⟩ := strict_intersection h hK htK hT hU hne
  have hcC := (mem_sdiff.mp (petalJ_subset (G := G) C K T hc)).1
  have hT3 := (mem_filter.mp hc).2
  have hU3 := (mem_filter.mp hd).2
  have hlow : dg G (T ∩ U) c ≤ 1 := by rw [hi]; exact petalJ_low hc
  have he := column_gap_zero_low hT3 hlow (hg c hcC)
  have hm := dg_mono (G := G) (inter_subset_right (s₁ := T) (s₂ := U)) c
  omega

lemma strict_petal_selected {A C K T : Finset V}
    (hT : T ∈ strictContainingFamily G A C K) :
    thetaC02 G C T = 8 - 4 * #T - 2 * #(corePlus G C K ∪ petalJ G C K T) +
      ec G T (corePlus G C K ∪ petalJ G C K T) := by
  have hKT := (mem_strictContainingFamily.mp hT).2.1
  have hY : corePlus G C K ∪ petalJ G C K T ⊆ C :=
    union_subset (corePlus_subset (G := G) C K)
      ((petalJ_subset (G := G) C K T).trans sdiff_subset)
  apply theta_selected hY
  · intro c hc
    rcases mem_union.mp hc with hc | hc
    · exact (mem_filter.mp hc).2.trans (dg_mono hKT c)
    · exact (show 2 ≤ 3 from by omega).trans (mem_filter.mp hc).2
  · intro c hc
    obtain ⟨hcC, hcN⟩ := mem_sdiff.mp hc
    have hcY : c ∉ corePlus G C K := fun hh => hcN (mem_union_left _ hh)
    by_contra hh
    exact hcN (mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨hcC, hcY⟩, by omega⟩))

lemma strict_petal_exact {A C K T : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2)
    (hT : T ∈ strictContainingFamily G A C K) :
    df G C (T \ K) + ec G (T \ K) (C \ (corePlus G C K ∪ petalJ G C K T)) =
      1 + 2 * petalD G C K T + ec G K (petalJ G C K T) ∧
    gv G (T \ K) (petalJ G C K T) =
      2 * (1 - petalD G C K T + ec G (T \ K) (corePlus G C K) + ec G K (petalJ G C K T)) := by
  have hKT := (mem_strictContainingFamily.mp hT).2.1
  have hY := corePlus_subset (G := G) C K
  have hJ := petalJ_subset (G := G) C K T
  have hYJ : Disjoint (corePlus G C K) (petalJ G C K T) :=
    disjoint_left.mpr fun c hcY hcJ => (mem_sdiff.mp (hJ hcJ)).2 hcY
  have hJU : corePlus G C K ∪ petalJ G C K T ⊆ C := union_subset hY (hJ.trans sdiff_subset)
  have hcTK : (#(T \ K) : ℤ) + #K = #T := by exact_mod_cast card_sdiff_add_card_eq_card hKT
  have hcYJ : (#(corePlus G C K ∪ petalJ G C K T) : ℤ) =
      #(corePlus G C K) + #(petalJ G C K T) := by exact_mod_cast card_union_of_disjoint hYJ
  have heTYJ : ec G T (corePlus G C K ∪ petalJ G C K T) =
      ec G T (corePlus G C K) + ec G T (petalJ G C K T) := by
    unfold ec
    rw [← sum_add_distrib]
    exact sum_congr rfl fun r _ => dg_union_of_disjoint hYJ r
  have heTYJZ : (ec G T (corePlus G C K ∪ petalJ G C K T) : ℤ) =
      ec G T (corePlus G C K) + ec G T (petalJ G C K T) := by exact_mod_cast heTYJ
  have hePYZ : (ec G (T \ K) (corePlus G C K) : ℤ) + ec G K (corePlus G C K) =
      ec G T (corePlus G C K) := by exact_mod_cast ec_sdiff_add_left (G := G) hKT (corePlus G C K)
  have hePJZ : (ec G (T \ K) (petalJ G C K T) : ℤ) + ec G K (petalJ G C K T) =
      ec G T (petalJ G C K T) := by exact_mod_cast ec_sdiff_add_left (G := G) hKT (petalJ G C K T)
  have htT := strict_theta h hK htK hT
  have htTS := strict_petal_selected hT
  have htKS := theta_corePlus (G := G) C K
  have hePUnion : ec G (T \ K) (corePlus G C K ∪ petalJ G C K T) =
      ec G (T \ K) (corePlus G C K) + ec G (T \ K) (petalJ G C K T) := by
    unfold ec
    rw [← sum_add_distrib]
    exact sum_congr rfl fun r _ => dg_union_of_disjoint hYJ r
  have hePCZ : (ec G (T \ K) (C \ (corePlus G C K ∪ petalJ G C K T)) : ℤ) +
      ec G (T \ K) (corePlus G C K) + ec G (T \ K) (petalJ G C K T) = ec G (T \ K) C := by
    have he := ec_sdiff_add_right (G := G) hJU (T \ K)
    rw [hePUnion, ← add_assoc] at he
    exact_mod_cast he
  constructor
  · rw [df_eq]; unfold petalD; linarith
  · unfold gv petalD; linarith

lemma strict_d_bounds {A C K T : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2)
    (hT : T ∈ strictContainingFamily G A C K) :
    -3 ≤ ((#K : ℤ) - #(corePlus G C K)) + petalD G C K T ∧
    ((#K : ℤ) - #(corePlus G C K)) + petalD G C K T ≤ 0 := by
  obtain ⟨hTF, hKT, _⟩ := mem_strictContainingFamily.mp hT
  obtain ⟨hTA, h3, _, _⟩ := maxPositive_data h hTF
  have ht := strict_theta h hK htK hT
  have hne : T ≠ A := by intro he; rw [he, theta_whole h] at ht; omega
  have hYJ : Disjoint (corePlus G C K) (petalJ G C K T) :=
    disjoint_left.mpr fun c hcY hcJ => (mem_sdiff.mp (petalJ_subset (G := G) C K T hcJ)).2 hcY
  have hU := union_subset (corePlus_subset (G := G) C K)
    ((petalJ_subset (G := G) C K T).trans sdiff_subset)
  have htc := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTA, hne⟩)
  have huc := card_le_card hU
  have hg := h.sparse T hTA (corePlus G C K ∪ petalJ G C K T) hU (by omega) (by omega)
  have hdef := (c02_deficit_bounds h hTA).1
  have hcTK : (#(T \ K) : ℤ) + #K = #T := by exact_mod_cast card_sdiff_add_card_eq_card hKT
  have hcYJ : (#(corePlus G C K ∪ petalJ G C K T) : ℤ) =
      #(corePlus G C K) + #(petalJ G C K T) := by exact_mod_cast card_union_of_disjoint hYJ
  have htTS := strict_petal_selected hT
  have hsel := df_eq_df_add_ec (G := G) hU T
  have he0 : (0 : ℤ) ≤ ec G T (C \ (corePlus G C K ∪ petalJ G C K T)) := by positivity
  rw [df_eq] at hsel
  unfold gv at hg
  unfold petalD
  constructor <;> linarith

lemma strict_large {A C K T : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2)
    (hT : T ∈ strictContainingFamily G A C K)
    (hlarge : 3 ≤ #(T \ K) + #(petalJ G C K T)) :
    6 + petalD G C K T - ec G K (petalJ G C K T) ≤ ec G (T \ K) (corePlus G C K) := by
  have hTA := (maxPositive_data h (mem_strictContainingFamily.mp hT).1).1
  have ht := strict_theta h hK htK hT
  have hne : T ≠ A := by intro he; rw [he, theta_whole h] at ht; omega
  have htc := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTA, hne⟩)
  have hpc := card_le_card (sdiff_subset (s := T) (t := K))
  have hJC := (petalJ_subset (G := G) C K T).trans sdiff_subset
  have hjc := card_le_card hJC
  have hg := h.sparse (T \ K) (sdiff_subset.trans hTA) (petalJ G C K T) hJC hlarge (by omega)
  have he := (strict_petal_exact h hK htK hT).2
  linarith


lemma high_outside_degree {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2) {r : V}
    (hr : r ∈ A \ K) : dg G (corePlus G C K) r ≤ 3 := by
  obtain ⟨hKA, _, _, hmK⟩ := high_data h hK htK
  obtain ⟨hrA, hrK⟩ := mem_sdiff.mp hr
  have hsub : insert r K ⊆ A := insert_subset_iff.mpr ⟨hrA, hKA⟩
  have hne : insert r K ≠ K := by intro he; exact hrK (he ▸ mem_insert_self r K)
  have hmax := hmK (insert r K) hsub (subset_insert r K) hne
  have hY := corePlus_subset (G := G) C K
  have htheta : thetaC02 G C (insert r K) =
      8 - 4 * #(insert r K) - 2 * #(corePlus G C K) + ec G (insert r K) (corePlus G C K) := by
    apply theta_selected hY
    · intro c hc
      exact (mem_filter.mp hc).2.trans (dg_mono (subset_insert r K) c)
    · intro c hc
      obtain ⟨hcC, hcY⟩ := mem_sdiff.mp hc
      have hlo : dg G K c ≤ 1 := by
        by_contra hh
        exact hcY (mem_filter.mpr ⟨hcC, by omega⟩)
      have hd := dg_union_of_disjoint (G := G) (disjoint_singleton_left.mpr hrK) c
      simp only [singleton_union] at hd
      have hsingle := dg_le_card (G := G) ({r} : Finset V) c
      simp only [card_singleton] at hsingle
      omega
  have hcard : (#(insert r K) : ℤ) = #K + 1 := by exact_mod_cast card_insert_of_notMem hrK
  have he : ec G (insert r K) (corePlus G C K) =
      dg G (corePlus G C K) r + ec G K (corePlus G C K) := by unfold ec; rw [sum_insert hrK]
  have hez : (ec G (insert r K) (corePlus G C K) : ℤ) =
      dg G (corePlus G C K) r + ec G K (corePlus G C K) := by exact_mod_cast he
  have ht := theta_corePlus (G := G) C K
  omega

lemma strict_small {A C K T : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2)
    (hT : T ∈ strictContainingFamily G A C K)
    (hsmall : #(T \ K) + #(petalJ G C K T) ≤ 2) :
    #(T \ K) = 1 ∧ #(petalJ G C K T) = 0 ∧ petalD G C K T = 1 ∧
    ec G K (petalJ G C K T) = 0 ∧ ec G (T \ K) (corePlus G C K) = 3 ∧ df G C (T \ K) ≤ 2 := by
  obtain ⟨hTF, hKT, hne⟩ := mem_strictContainingFamily.mp hT
  have hTA := (maxPositive_data h hTF).1
  have hp0 : 0 < #(T \ K) := by
    by_contra hh
    have he : T \ K = ∅ := card_eq_zero.mp (by omega)
    exact hne (Subset.antisymm (sdiff_eq_empty_iff_subset.mp he) hKT)
  have hj : #(petalJ G C K T) = 0 := by
    by_contra hh
    obtain ⟨c, hc⟩ := card_pos.mp (show 0 < #(petalJ G C K T) by omega)
    have hlo := petalJ_low (G := G) hc
    have hd := dg_sdiff_add (G := G) hKT c
    have hdc := dg_le_card (G := G) (T \ K) c
    have hc3 := (mem_filter.mp hc).2
    omega
  have hJe : petalJ G C K T = ∅ := card_eq_zero.mp hj
  have ha : ec G K (petalJ G C K T) = 0 := by rw [hJe]; simp [ec, dg]
  have htT := strict_theta h hK htK hT
  have htTS := strict_petal_selected hT
  have htKS := theta_corePlus (G := G) C K
  have hcard : (#(T \ K) : ℤ) + #K = #T := by exact_mod_cast card_sdiff_add_card_eq_card hKT
  have hez : (ec G (T \ K) (corePlus G C K) : ℤ) + ec G K (corePlus G C K) =
      ec G T (corePlus G C K) := by exact_mod_cast ec_sdiff_add_left (G := G) hKT (corePlus G C K)
  rw [hJe, union_empty] at htTS
  have hrows : ec G (T \ K) (corePlus G C K) ≤ 3 * #(T \ K) := by
    unfold ec
    calc
      _ ≤ ∑ _r ∈ T \ K, 3 := sum_le_sum fun r hr =>
        high_outside_degree h hK htK (mem_sdiff.mpr ⟨hTA (mem_sdiff.mp hr).1, (mem_sdiff.mp hr).2⟩)
      _ = _ := by simp only [sum_const, smul_eq_mul]; omega
  have hrowsz : (ec G (T \ K) (corePlus G C K) : ℤ) ≤ 3 * (#(T \ K) : ℤ) := by exact_mod_cast hrows
  have hdef := (c02_deficit_bounds h (sdiff_subset (s := T) (t := K) |>.trans hTA)).2
  refine ⟨by omega, hj, ?_, ha, by omega, by omega⟩
  unfold petalD
  omega

lemma strict_union_subset {A C K : Finset V} (h : C02Input G A C) :
    (strictContainingFamily G A C K).biUnion (fun T => T \ K) ⊆ A \ K := by
  intro a ha
  obtain ⟨T, hT, haT⟩ := mem_biUnion.mp ha
  obtain ⟨haT, haK⟩ := mem_sdiff.mp haT
  exact mem_sdiff.mpr ⟨(maxPositive_data h (mem_strictContainingFamily.mp hT).1).1 haT, haK⟩

lemma strict_boundary_budget {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2) :
    (∑ T ∈ strictContainingFamily G A C K, (ec G (T \ K) (corePlus G C K) : ℤ)) ≤
      18 - 2 * highLoss G C K := by
  have hs := sum_biUnion (f := fun a => dg G (corePlus G C K) a) (strict_petals_pairwise h hK htK)
  have hm := ec_mono_left (G := G) (strict_union_subset (K := K) h) (corePlus G C K)
  have he : (∑ T ∈ strictContainingFamily G A C K, (ec G (T \ K) (corePlus G C K) : ℤ)) ≤
      ec G (A \ K) (corePlus G C K) := by
    unfold ec at hm
    rw [hs] at hm
    exact_mod_cast hm
  rw [high_boundary h hK htK] at he
  exact he

lemma strict_scar_budget {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2) :
    (∑ T ∈ strictContainingFamily G A C K, (ec G K (petalJ G C K T) : ℤ)) ≤
      highLoss G C K - df G C K := by
  have hs := sum_biUnion (f := fun c => dg G K c) (strict_Jparts_pairwise h hK htK)
  have hsub : (strictContainingFamily G A C K).biUnion (petalJ G C K) ⊆ C \ corePlus G C K := by
    intro c hc
    obtain ⟨T, _, hcT⟩ := mem_biUnion.mp hc
    exact petalJ_subset (G := G) C K T hcT
  have hm := ec_mono_left (G := G) hsub K
  have he : (∑ T ∈ strictContainingFamily G A C K, (ec G K (petalJ G C K T) : ℤ)) ≤
      ec G K (C \ corePlus G C K) := by
    have hnat : (∑ T ∈ strictContainingFamily G A C K, ec G K (petalJ G C K T)) ≤
        ec G K (C \ corePlus G C K) := by
      calc
        _ = ∑ T ∈ strictContainingFamily G A C K, ec G (petalJ G C K T) K := sum_congr rfl fun T _ => ec_comm _ _
        _ = ec G ((strictContainingFamily G A C K).biUnion (petalJ G C K)) K := hs.symm
        _ ≤ ec G (C \ corePlus G C K) K := hm
        _ = _ := ec_comm _ _
    exact_mod_cast hnat
  rw [high_outside_alpha] at he
  exact he

lemma strict_deficit_union {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2) :
    (∑ T ∈ strictContainingFamily G A C K, df G C (T \ K)) =
      df G C ((strictContainingFamily G A C K).biUnion (fun T => T \ K)) :=
  (sum_biUnion (f := fun a => (6 : ℤ) - (dg G C a : ℤ)) (strict_petals_pairwise h hK htK)).symm

lemma strict_loss_two_charge {A C K T : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2)
    (hl : highLoss G C K = 2) (hdf : 2 ≤ df G C K)
    (hT : T ∈ strictContainingFamily G A C K) :
    3 * df G C (T \ K) ≤ 2 * (ec G (T \ K) (corePlus G C K) : ℤ) := by
  have hscar := strict_scar_budget h hK htK
  have ha : ec G K (petalJ G C K T) = 0 := by
    have hsingle := single_le_sum (fun T _ => show (0 : ℤ) ≤ ec G K (petalJ G C K T) by positivity) hT
    omega
  by_cases hsmall : #(T \ K) + #(petalJ G C K T) ≤ 2
  · have hs := strict_small h hK htK hT hsmall
    omega
  · have hlarge := strict_large h hK htK hT (by omega)
    have he := (strict_petal_exact h hK htK hT).1
    have ho : (0 : ℤ) ≤ ec G (T \ K) (C \ (corePlus G C K ∪ petalJ G C K T)) := by positivity
    have hb := strict_d_bounds h hK htK hT
    have hgeom := (high_geometry h hK htK).2.1
    rw [ha] at hlarge he
    omega

lemma strict_loss_two_budget {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2)
    (hl : highLoss G C K = 2) (hdf : 2 ≤ df G C K) :
    (∑ T ∈ strictContainingFamily G A C K, df G C (T \ K)) ≤ 9 := by
  have hs := sum_le_sum fun T hT => strict_loss_two_charge h hK htK hl hdf hT
  have hb := strict_boundary_budget h hK htK
  rw [← mul_sum, ← mul_sum] at hs
  omega

lemma four_deficit {A C Z S : Finset V} (h : C02Input G A C)
    (hZ : Z ⊆ A) (hS : S ⊆ Z) (hf : ∀ a ∈ S, dg G C a = 4) :
    2 * (#S : ℤ) ≤ df G C Z := by
  have hd : df G C S = 2 * (#S : ℤ) := by
    unfold df
    calc
      _ = ∑ _a ∈ S, (2 : ℤ) := sum_congr rfl fun a ha => by norm_num [hf a ha]
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
  rw [← hd]
  exact df_le_of_subset hS fun a ha => h.capA a (hZ ha)

lemma four_deficit_one {A C Z : Finset V} (h : C02Input G A C)
    (hZ : Z ⊆ A) {p : V} (hp : p ∈ Z) (hp4 : dg G C p = 4) : 2 ≤ df G C Z := by
  have hd := four_deficit h hZ (singleton_subset_iff.mpr hp) (by simpa using hp4)
  simpa using hd

lemma theta_order_two_le_three {A C Z : Finset V} (h : C02Input G A C)
    (hZ : Z ⊆ A) (h2 : 2 ≤ #Z) : thetaC02 G C Z ≤ 3 := by
  by_cases h3 : 3 ≤ #Z
  · exact theta_three h hZ h3
  · have he := theta_small (G := G) C (Z := Z) (by omega)
    omega

lemma high_partial_singleton {A C K T : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2)
    (hT : T ∈ maxPositiveFamily G A C) (hnot : ¬ K ⊆ T)
    {p : V} (hpK : p ∈ K) (hpT : p ∈ T) (hp4 : dg G C p = 4) : K ∩ T = {p} := by
  obtain ⟨hKA, _, _, _⟩ := high_data h hK htK
  obtain ⟨hTA, _, htT, hmT⟩ := maxPositive_data h hT
  have hUne : K ∪ T ≠ T := by intro he; exact hnot (he ▸ subset_union_left)
  have hU := hmT (K ∪ T) (union_subset hKA hTA) subset_union_right hUne
  have hs := theta_supermodular (G := G) C K T
  have hpI : p ∈ K ∩ T := mem_inter.mpr ⟨hpK, hpT⟩
  have hI2 : #(K ∩ T) < 2 := by
    by_contra hh
    have hb := theta_with_four_le_two h (inter_subset_left.trans hKA) (by omega) hpI hp4
    omega
  have hI0 : 0 < #(K ∩ T) := card_pos.mpr ⟨p, hpI⟩
  obtain ⟨a, ha⟩ := card_eq_one.mp (show #(K ∩ T) = 1 by omega)
  have he : p = a := mem_singleton.mp (ha ▸ hpI)
  simpa [he] using ha

lemma singleton_gap_budget {A C K T : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2)
    (hT : T ∈ maxPositiveFamily G A C) (hnot : ¬ K ⊆ T)
    {p : V} (hi : K ∩ T = {p}) :
    (dg G (corePlus G C K ∩ cpr G C T) p : ℤ) ≤ 2 - thetaC02 G C T := by
  obtain ⟨hKA, _, _, _⟩ := high_data h hK htK
  obtain ⟨hTA, _, _, hmT⟩ := maxPositive_data h hT
  have hUne : K ∪ T ≠ T := by intro he; exact hnot (he ▸ subset_union_left)
  have hU := hmT (K ∪ T) (union_subset hKA hTA) subset_union_right hUne
  have hsingle : thetaC02 G C ({p} : Finset V) = 4 := by simpa using theta_small (G := G) C (Z := {p}) (by simp)
  have hg := theta_gap_sum (G := G) C K T
  rw [hi, hsingle, htK] at hg
  let S := (corePlus G C K ∩ cpr G C T).filter fun c => G.Adj p c
  have hSC : S ⊆ C := fun c hc => (mem_filter.mp (mem_inter.mp (mem_filter.mp hc).1).1).1
  have hunit : ∀ c ∈ S, columnGap (G := G) K T c = 1 := by
    intro c hc
    obtain ⟨hci, hac⟩ := mem_filter.mp hc
    obtain ⟨hcK, hcT⟩ := mem_inter.mp hci
    exact singleton_gap_one_plus hi (mem_filter.mp hcK).2 (mem_cpr.mp hcT).2 hac
  have hsum := sum_le_sum_of_subset_of_nonneg hSC (fun c _ _ => columnGap_nonneg (G := G) K T c)
  have hss : (∑ c ∈ S, columnGap (G := G) K T c) = (dg G (corePlus G C K ∩ cpr G C T) p : ℤ) := by
    rw [sum_congr rfl hunit]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    rfl
  rw [hss] at hsum
  omega

lemma high_closed_module {A C K T : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2)
    {p : V} (hpK : p ∈ K) (hp4 : dg G C p = 4) (hpplus : dg G (corePlus G C K) p = 4)
    (hT : T ∈ maxPositiveFamily G A C) (hpT : p ∈ T) : K ⊆ T := by
  by_contra hn
  have hi := high_partial_singleton h hK htK hT hn hpK hpT hp4
  have hb := singleton_gap_budget h hK htK hT hn hi
  have hTA := (maxPositive_data h hT).1
  have h3 := (maxPositive_data h hT).2.1
  have htpos := (maxPositive_data h hT).2.2.1
  have hd := dg_union_add_dg_inter (G := G) (corePlus G C K) (cpr G C T) p
  have hdu := dg_mono (G := G) (union_subset (corePlus_subset (G := G) C K) (cpr_subset (G := G) C T)) p
  have hEr := theta_erase (G := G) (C := C) hpT
  have h2 : 2 ≤ #(T.erase p) := by have hc := card_erase_add_one hpT; omega
  have htheta := theta_order_two_le_three h ((erase_subset _ _).trans hTA) h2
  omega


variable (G) in
def FourResourceBound (A C : Finset V) : Prop :=
  ∀ K ∈ maxHighFamily G A C, thetaC02 G C K = 2 → highLoss G C K = 4 → 2 ≤ df G C K →
    (∑ T ∈ strictContainingFamily G A C K, df G C (T \ K)) ≤ 7

lemma high_closed_cover {A C K : Finset V} (h : C02Input G A C)
    (hap : APF G A C) (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2)
    {p : V} (hpK : p ∈ K) (hp4 : dg G C p = 4) (hpplus : dg G (corePlus G C K) p = 4) :
    (strictContainingFamily G A C K).biUnion (fun T => T \ K) = A \ K := by
  apply Subset.antisymm (strict_union_subset (K := K) h)
  intro a ha
  obtain ⟨haA, haK⟩ := mem_sdiff.mp ha
  have hKA := (high_data h hK htK).1
  have hne : p ≠ a := by intro he; exact haK (he ▸ hpK)
  obtain ⟨T, hT, hpT, haT⟩ := hap p (hKA hpK) a haA hne
  have hKT := high_closed_module h hK htK hpK hp4 hpplus hT hpT
  have hTK : T ≠ K := by intro he; exact haK (he ▸ haT)
  exact mem_biUnion.mpr ⟨T, mem_strictContainingFamily.mpr ⟨hT, hKT, hTK⟩, mem_sdiff.mpr ⟨haT, haK⟩⟩

lemma high_four_outgoing {A C K : Finset V} (h : C02Input G A C)
    (hap : APF G A C) (hb4 : FourResourceBound G A C)
    (hK : K ∈ maxHighFamily G A C) {p : V} (hpK : p ∈ K) (hp4 : dg G C p = 4) :
    dg G (corePlus G C K) p ≤ 3 := by
  have htK := high_four_theta h hK hpK hp4
  have hKA := (high_data h hK htK).1
  have hdf := four_deficit_one h hKA hpK hp4
  have hgeom := high_geometry h hK htK
  have ho : (0 : ℤ) ≤ ec G K (C \ corePlus G C K) := by positivity
  have hout := high_outside_alpha (G := G) (C := C) (K := K)
  have hdfle : df G C K ≤ highLoss G C K := by omega
  have hdmono := dg_mono (G := G) (corePlus_subset (G := G) C K) p
  by_contra hn
  have hd4 : dg G (corePlus G C K) p = 4 := by omega
  have hcov := high_closed_cover h hap hK htK hpK hp4 hd4
  have he := strict_deficit_union h hK htK
  rw [hcov] at he
  have hs := df_sdiff_add (G := G) (S := C) hKA
  rw [c02_total_deficit h] at hs
  rcases hgeom.1 with hl | hl | hl
  · omega
  · have hb := strict_loss_two_budget h hK htK hl hdf
    omega
  · have hb := hb4 K hK htK hl hdf
    omega

lemma high_four_unique {A C K : Finset V} (h : C02Input G A C)
    (hap : APF G A C) (hb4 : FourResourceBound G A C)
    (hK : K ∈ maxHighFamily G A C) {p q : V}
    (hpK : p ∈ K) (hqK : q ∈ K) (hp4 : dg G C p = 4) (hq4 : dg G C q = 4) : p = q := by
  by_contra hne
  have htK := high_four_theta h hK hpK hp4
  have hKA := (high_data h hK htK).1
  have hp := high_four_outgoing h hap hb4 hK hpK hp4
  have hq := high_four_outgoing h hap hb4 hK hqK hq4
  have hcap : ∀ a ∈ K, dg G (corePlus G C K) a ≤ 6 := fun a ha =>
    (dg_mono (G := G) (corePlus_subset (G := G) C K) a).trans (h.capA a (hKA ha))
  have hs : ({p, q} : Finset V) ⊆ K := by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨hpK, hqK⟩
  have hd := df_le_of_subset (G := G) hs hcap
  have he : df G (corePlus G C K) ({p, q} : Finset V) =
      6 - (dg G (corePlus G C K) p : ℤ) + (6 - (dg G (corePlus G C K) q : ℤ)) := by
    simp only [df, sum_pair hne]
  have hl : df G (corePlus G C K) K = highLoss G C K := df_eq _ _
  rw [he, hl] at hd
  have hgeom := (high_geometry h hK htK).1
  omega

lemma maxPositive_two_four_theta {A C T : Finset V} (h : C02Input G A C)
    (hap : APF G A C) (hb4 : FourResourceBound G A C)
    (hT : T ∈ maxPositiveFamily G A C) {p q : V}
    (hpT : p ∈ T) (hqT : q ∈ T) (hp4 : dg G C p = 4) (hq4 : dg G C q = 4) (hne : p ≠ q) :
    thetaC02 G C T = 1 := by
  obtain ⟨hTA, h3, hpos, _⟩ := maxPositive_data h hT
  have hb := theta_with_four_le_two h hTA (by omega) hpT hp4
  by_contra hh
  obtain ⟨K, hK, hTK⟩ := high_extension (G := G) (C := C) hTA h3 (by omega)
  exact hne (high_four_unique h hap hb4 hK (hTK hpT) (hTK hqT) hp4 hq4)

lemma two_four_canonical_degree {A C T : Finset V} (h : C02Input G A C)
    (hT : T ∈ maxPositiveFamily G A C) {p q : V}
    (hpT : p ∈ T) (hqT : q ∈ T) (hq4 : dg G C q = 4) (hne : q ≠ p)
    (ht : thetaC02 G C T = 1) : 3 ≤ dg G (cpr G C T) p := by
  have hTA := (maxPositive_data h hT).1
  have h3 := (maxPositive_data h hT).2.1
  have hEr := theta_erase (G := G) (C := C) hpT
  have hqE : q ∈ T.erase p := mem_erase.mpr ⟨hne, hqT⟩
  have h2 : 2 ≤ #(T.erase p) := by have hc := card_erase_add_one hpT; omega
  have hb := theta_with_four_le_two h ((erase_subset _ _).trans hTA) h2 hqE hq4
  omega

lemma theta3_outside_low {A C K : Finset V} (h : C02Input G A C)
    (hK : K ⊆ A) (ht : thetaC02 G C K = 3) {c : V} (hc : c ∈ C \ cpr G C K) :
    dg G K c ≤ 1 := by
  have he := theta3_original_loss h hK ht
  have hd := (c02_deficit_bounds h hK).1
  have hs : dg G K c ≤ ec G (C \ cpr G C K) K :=
    single_le_sum (fun _ _ => Nat.zero_le _) hc
  rw [ec_comm] at hs
  omega

lemma high_four_shape {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) {p : V} (hpK : p ∈ K) (hp4 : dg G C p = 4)
    (hout : dg G (corePlus G C K) p ≤ 3) :
    thetaC02 G C (K.erase p) = 3 ∧
    K.erase p ∈ maxThetaThreeFamily G A C ∧
    corePlus G C K = cpr G C (K.erase p) ∧
    dg G (corePlus G C K) p = 3 ∧ highLoss G C K = 4 ∧
    2 ≤ df G C K ∧ df G C K ≤ 3 := by
  have htK := high_four_theta h hK hpK hp4
  obtain ⟨hKA, h3, _, hmK⟩ := high_data h hK htK
  have hEA : K.erase p ⊆ A := (erase_subset _ _).trans hKA
  have hEr := theta_erase (G := G) (C := C) hpK
  have h2 : 2 ≤ #(K.erase p) := by have hc := card_erase_add_one hpK; omega
  have hprplus : cpr G C K ⊆ corePlus G C K := by
    intro c hc
    obtain ⟨hcC, hd⟩ := mem_cpr.mp hc
    exact mem_filter.mpr ⟨hcC, by omega⟩
  have hdeg := dg_mono (G := G) hprplus p
  have hthetab := theta_order_two_le_three h hEA h2
  have htE : thetaC02 G C (K.erase p) = 3 := by omega
  have h3E := (theta3_large_proper h hEA htE).1
  have hcE := (theta3_geometry h hEA htE).2.2.1
  have hcan : cpr G C K = cpr G C (K.erase p) := by
    apply Subset.antisymm
    · intro c hc
      obtain ⟨hcC, hdK⟩ := mem_cpr.mp hc
      by_contra hn
      have hl := theta3_outside_low h hEA htE (mem_sdiff.mpr ⟨hcC, hn⟩)
      by_cases hadj : G.Adj c p
      · have hd := dg_erase_add (G := G) hpK c hadj
        omega
      · have hd := dg_erase_of_not_adj (G := G) (T := K) hadj
        omega
    · intro c hc
      obtain ⟨hcC, hdE⟩ := mem_cpr.mp hc
      exact mem_cpr.mpr ⟨hcC, hdE.trans (dg_mono (G := G) (erase_subset _ _) c)⟩
  have hdcan : dg G (cpr G C (K.erase p)) p = 3 := by rw [← hcan]; omega
  have hsubPlus : cpr G C (K.erase p) ⊆ corePlus G C K := hcan ▸ hprplus
  have hdplus : dg G (corePlus G C K) p = 3 := by
    have hm := dg_mono (G := G) hsubPlus p
    omega
  have hplus : corePlus G C K = cpr G C (K.erase p) := by
    apply Subset.antisymm _ hsubPlus
    intro c hc
    by_contra hn
    have hcC := (mem_filter.mp hc).1
    have hc2 := (mem_filter.mp hc).2
    have hlo := theta3_outside_low h hEA htE (mem_sdiff.mpr ⟨hcC, hn⟩)
    have hadj : G.Adj c p := by
      by_contra hh
      have hd := dg_erase_of_not_adj (G := G) (T := K) hh
      omega
    have hs := dg_sdiff_add (G := G) hsubPlus p
    have hpos : 0 < dg G (corePlus G C K \ cpr G C (K.erase p)) p := card_pos.mpr
      ⟨c, mem_filter.mpr ⟨mem_sdiff.mpr ⟨hc, hn⟩, G.adj_symm hadj⟩⟩
    omega
  have hmax : K.erase p ∈ maxThetaThreeFamily G A C := by
    apply mem_maximalMembers.mpr
    refine ⟨mem_thetaThreeSets.mpr ⟨hEA, htE⟩, ?_⟩
    intro M hM hEM
    obtain ⟨hMA, htM⟩ := mem_thetaThreeSets.mp hM
    have hpM : p ∉ M := fun hp => theta3_no_four h hMA htM hp hp4
    have hI : K ∩ M = K.erase p := by
      apply Subset.antisymm
      · intro a ha
        obtain ⟨haK, haM⟩ := mem_inter.mp ha
        exact mem_erase.mpr ⟨fun he => hpM (he ▸ haM), haK⟩
      · exact subset_inter (erase_subset _ _) hEM
    have hMK : M ⊆ K := by
      by_contra hh
      have hUn : K ∪ M ≠ K := by intro he; exact hh (he ▸ subset_union_right)
      have hUb := hmK (K ∪ M) (union_subset hKA hMA) subset_union_left hUn
      have hs := theta_supermodular (G := G) C K M
      rw [hI] at hs
      omega
    apply Subset.antisymm _ hEM
    intro a ha
    exact mem_erase.mpr ⟨fun he => hpM (he ▸ ha), hMK ha⟩
  have hgeom := (high_geometry h hK htK).2.1
  have hcard : (#(K.erase p) : ℤ) + 1 = #K := by exact_mod_cast card_erase_add_one hpK
  have hdefE := theta3_original_loss h hEA htE
  have hdef0 := (c02_deficit_bounds h hEA).1
  have hdf := df_sdiff_add (G := G) (S := C) (singleton_subset_iff.mpr hpK)
  have hsingle : df G C ({p} : Finset V) = 2 := by simp [df, hp4]
  rw [sdiff_singleton_eq_erase, hsingle] at hdf
  refine ⟨htE, hmax, hplus, hdplus, ?_, ?_, ?_⟩
  · rw [hplus] at hgeom
    omega
  · omega
  · omega


lemma theta_one_four_trace_bound {A C T : Finset V} (h : C02Input G A C)
    (hT : T ∈ maxPositiveFamily G A C) (ht : thetaC02 G C T = 1) :
    #(degreeFourRows G A C ∩ T) ≤ 3 := by
  obtain ⟨hTA, h3, _, _⟩ := maxPositive_data h hT
  have hne : T ≠ A := by intro he; rw [he, theta_whole h] at ht; omega
  have hb := theta_loss_bound h hTA hne h3
  have hd := df_anti (G := G) (cpr_subset (G := G) C T) (Z := T)
  have htrace := four_deficit h hTA (inter_subset_right (s₁ := degreeFourRows G A C))
    (fun a ha => (mem_degreeFourRows.mp (mem_inter.mp ha).1).2)
  omega

lemma two_four_contains_high {A C K T : Finset V} (h : C02Input G A C)
    (hap : APF G A C) (hb4 : FourResourceBound G A C)
    (hK : K ∈ maxHighFamily G A C) {p q : V}
    (hpK : p ∈ K) (hp4 : dg G C p = 4) (hq4 : dg G C q = 4) (hne : p ≠ q)
    (hT : T ∈ maxPositiveFamily G A C) (hpT : p ∈ T) (hqT : q ∈ T) : K ⊆ T := by
  have htK := high_four_theta h hK hpK hp4
  have hout := high_four_outgoing h hap hb4 hK hpK hp4
  have hshape := high_four_shape h hK hpK hp4 hout
  have htT := maxPositive_two_four_theta h hap hb4 hT hpT hqT hp4 hq4 hne
  have hdegT := two_four_canonical_degree h hT hpT hqT hq4 hne.symm htT
  by_contra hnot
  have hi := high_partial_singleton h hK htK hT hnot hpK hpT hp4
  have hb := singleton_gap_budget h hK htK hT hnot hi
  have hd := dg_union_add_dg_inter (G := G) (corePlus G C K) (cpr G C T) p
  have hdu := dg_mono (G := G) (union_subset (corePlus_subset (G := G) C K) (cpr_subset (G := G) C T)) p
  omega

lemma no_high_four {A C : Finset V} (h : C02Input G A C)
    (hfive : 5 ≤ #(degreeFourRows G A C)) (hap : APF G A C) (hb4 : FourResourceBound G A C) :
    ∀ K ∈ maxHighFamily G A C, ∀ p ∈ K, dg G C p ≠ 4 := by
  intro K hK p hpK hp4
  have htK := high_four_theta h hK hpK hp4
  have hKA := (high_data h hK htK).1
  have hout := high_four_outgoing h hap hb4 hK hpK hp4
  obtain ⟨_, _, _, _, hl4, hdflo, _⟩ := high_four_shape h hK hpK hp4 hout
  have hpD : p ∈ degreeFourRows G A C := mem_degreeFourRows.mpr ⟨hKA hpK, hp4⟩
  have hsub : (degreeFourRows G A C).erase p ⊆
      (strictContainingFamily G A C K).biUnion (fun T => T \ K) := by
    intro q hq
    obtain ⟨hqp, hqD⟩ := mem_erase.mp hq
    obtain ⟨hqA, hq4⟩ := mem_degreeFourRows.mp hqD
    obtain ⟨T, hT, hpT, hqT⟩ := hap p (hKA hpK) q hqA hqp.symm
    have hKT := two_four_contains_high h hap hb4 hK hpK hp4 hq4 hqp.symm hT hpT hqT
    have hqK : q ∉ K := fun hqK => hqp (high_four_unique h hap hb4 hK hqK hpK hq4 hp4)
    have hne : T ≠ K := by intro he; exact hqK (he ▸ hqT)
    exact mem_biUnion.mpr ⟨T, mem_strictContainingFamily.mpr ⟨hT, hKT, hne⟩, mem_sdiff.mpr ⟨hqT, hqK⟩⟩
  have hU : (strictContainingFamily G A C K).biUnion (fun T => T \ K) ⊆ A :=
    (strict_union_subset (K := K) h).trans sdiff_subset
  have hd := four_deficit h hU hsub
    (fun q hq => (mem_degreeFourRows.mp (mem_erase.mp hq).2).2)
  have hc := card_erase_add_one hpD
  have he := strict_deficit_union h hK htK
  have hb := hb4 K hK htK hl4 hdflo
  omega

lemma maxPositive_four_theta {A C T : Finset V} (h : C02Input G A C)
    (hno : ∀ K ∈ maxHighFamily G A C, ∀ p ∈ K, dg G C p ≠ 4)
    (hT : T ∈ maxPositiveFamily G A C) {p : V} (hpT : p ∈ T) (hp4 : dg G C p = 4) :
    thetaC02 G C T = 1 := by
  obtain ⟨hTA, h3, hpos, _⟩ := maxPositive_data h hT
  have hb := theta_with_four_le_two h hTA (by omega) hpT hp4
  by_contra hh
  obtain ⟨K, hK, hTK⟩ := high_extension (G := G) (C := C) hTA h3 (by omega)
  exact hno K hK p (hTK hpT) hp4

lemma positive_four_intersection {A C T U : Finset V} (h : C02Input G A C)
    (hno : ∀ K ∈ maxHighFamily G A C, ∀ p ∈ K, dg G C p ≠ 4)
    (hT : T ∈ maxPositiveFamily G A C) (hU : U ∈ maxPositiveFamily G A C) (hne : T ≠ U)
    {p : V} (hpT : p ∈ T) (hpU : p ∈ U) (hp4 : dg G C p = 4) : T ∩ U = {p} := by
  obtain ⟨hTA, _, _, hmT⟩ := maxPositive_data h hT
  obtain ⟨hUA, _, _, _⟩ := maxPositive_data h hU
  have hUn : T ∪ U ≠ T := by
    intro he
    obtain ⟨hTs, _⟩ := mem_maximalMembers.mp hT
    obtain ⟨_, hmU⟩ := mem_maximalMembers.mp hU
    exact hne (hmU T hTs (he ▸ subset_union_right))
  have hUb := hmT (T ∪ U) (union_subset hTA hUA) subset_union_left hUn
  have ht := maxPositive_four_theta h hno hT hpT hp4
  have hu := maxPositive_four_theta h hno hU hpU hp4
  have hs := theta_supermodular (G := G) C T U
  have hIA : T ∩ U ⊆ A := inter_subset_left.trans hTA
  have hpI : p ∈ T ∩ U := mem_inter.mpr ⟨hpT, hpU⟩
  have hIθ : 2 ≤ thetaC02 G C (T ∩ U) := by omega
  have hI2 : #(T ∩ U) < 2 := by
    by_contra hh
    by_cases h3 : 3 ≤ #(T ∩ U)
    · obtain ⟨K, hK, hIK⟩ := high_extension (G := G) (C := C) hIA h3 hIθ
      exact hno K hK p (hIK hpI) hp4
    · have hsmall := theta_small (G := G) C (Z := T ∩ U) (by omega)
      omega
  have hI0 := card_pos.mpr ⟨p, hpI⟩
  obtain ⟨a, ha⟩ := card_eq_one.mp (show #(T ∩ U) = 1 by omega)
  have he : p = a := mem_singleton.mp (ha ▸ hpI)
  simpa [he] using ha

lemma positive_singleton_gap_budget {A C T U : Finset V} (h : C02Input G A C)
    (hT : T ∈ maxPositiveFamily G A C) (hU : U ∈ maxPositiveFamily G A C) (hne : T ≠ U)
    (ht : thetaC02 G C T = 1) (hu : thetaC02 G C U = 1)
    {p : V} (hi : T ∩ U = {p}) :
    dg G (cpr G C T ∩ cpr G C U) p ≤ 2 := by
  obtain ⟨hTA, _, _, hmT⟩ := maxPositive_data h hT
  obtain ⟨hUA, _, _, _⟩ := maxPositive_data h hU
  have hUn : T ∪ U ≠ T := by
    intro he
    obtain ⟨hTs, _⟩ := mem_maximalMembers.mp hT
    obtain ⟨_, hmU⟩ := mem_maximalMembers.mp hU
    exact hne (hmU T hTs (he ▸ subset_union_right))
  have hUb := hmT (T ∪ U) (union_subset hTA hUA) subset_union_left hUn
  have hsingle : thetaC02 G C ({p} : Finset V) = 4 := by simpa using theta_small (G := G) C (Z := {p}) (by simp)
  have hg := theta_gap_sum (G := G) C T U
  rw [hi, hsingle, ht, hu] at hg
  let S := (cpr G C T ∩ cpr G C U).filter fun c => G.Adj p c
  have hSC : S ⊆ C := fun c hc => (mem_cpr.mp (mem_inter.mp (mem_filter.mp hc).1).1).1
  have hunit : ∀ c ∈ S, columnGap (G := G) T U c = 1 := by
    intro c hc
    obtain ⟨hci, hac⟩ := mem_filter.mp hc
    obtain ⟨hcT, hcU⟩ := mem_inter.mp hci
    exact singleton_gap_one hi (mem_cpr.mp hcT).2 (mem_cpr.mp hcU).2 hac
  have hsum := sum_le_sum_of_subset_of_nonneg hSC (fun c _ _ => columnGap_nonneg (G := G) T U c)
  have he : (∑ c ∈ S, columnGap (G := G) T U c) = (dg G (cpr G C T ∩ cpr G C U) p : ℤ) := by
    rw [sum_congr rfl hunit]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    rfl
  rw [he] at hsum
  omega

lemma erase_four_theta_le_one {A C T : Finset V} (h : C02Input G A C)
    (hno : ∀ K ∈ maxHighFamily G A C, ∀ p ∈ K, dg G C p ≠ 4)
    (hT : T ∈ maxPositiveFamily G A C) {p q : V} (hpT : p ∈ T) (hqT : q ∈ T)
    (hqp : q ≠ p) (hq4 : dg G C q = 4) : thetaC02 G C (T.erase p) ≤ 1 := by
  have hTA := (maxPositive_data h hT).1
  have hEA : T.erase p ⊆ A := (erase_subset _ _).trans hTA
  have h3 := (maxPositive_data h hT).2.1
  have h2 : 2 ≤ #(T.erase p) := by have hc := card_erase_add_one hpT; omega
  by_cases h3E : 3 ≤ #(T.erase p)
  · by_contra hh
    obtain ⟨K, hK, hEK⟩ := high_extension (G := G) (C := C) hEA h3E (by omega)
    exact hno K hK q (hEK (mem_erase.mpr ⟨hqp, hqT⟩)) hq4
  · have hs := theta_small (G := G) C (Z := T.erase p) (by omega)
    omega

lemma positive_four_trace_bound {A C T : Finset V} (h : C02Input G A C)
    (hfive : 5 ≤ #(degreeFourRows G A C)) (hap : APF G A C)
    (hno : ∀ K ∈ maxHighFamily G A C, ∀ p ∈ K, dg G C p ≠ 4)
    (hT : T ∈ maxPositiveFamily G A C) {p : V} (hpT : p ∈ T) (hp4 : dg G C p = 4) :
    #(degreeFourRows G A C ∩ T) ≤ 2 := by
  have ht := maxPositive_four_theta h hno hT hpT hp4
  have hb := theta_one_four_trace_bound h hT ht
  by_contra hh
  have hpD : p ∈ degreeFourRows G A C := mem_degreeFourRows.mpr ⟨(maxPositive_data h hT).1 hpT, hp4⟩
  have hpI : p ∈ degreeFourRows G A C ∩ T := mem_inter.mpr ⟨hpD, hpT⟩
  have hcard := card_erase_add_one hpI
  obtain ⟨q, hq⟩ := card_pos.mp (show 0 < #((degreeFourRows G A C ∩ T).erase p) by omega)
  obtain ⟨hqp, hqI⟩ := mem_erase.mp hq
  obtain ⟨hqD, hqT⟩ := mem_inter.mp hqI
  have hq4 := (mem_degreeFourRows.mp hqD).2
  have hEr := theta_erase (G := G) (C := C) hpT
  have hEθ := erase_four_theta_le_one h hno hT hpT hqT hqp hq4
  have hmono := dg_mono (G := G) (cpr_subset (G := G) C T) p
  have hdegT : dg G (cpr G C T) p = 4 := by omega
  have hnsub : ¬ degreeFourRows G A C ⊆ T := by
    intro hs
    have hi : degreeFourRows G A C ∩ T = degreeFourRows G A C := inter_eq_left.mpr hs
    rw [hi] at hb
    omega
  obtain ⟨s, hsD, hsT⟩ := not_subset.mp hnsub
  have hsA := (mem_degreeFourRows.mp hsD).1
  have hs4 := (mem_degreeFourRows.mp hsD).2
  have hps : p ≠ s := by intro he; exact hsT (he ▸ hpT)
  obtain ⟨U, hU, hpU, hsU⟩ := hap p ((maxPositive_data h hT).1 hpT) s hsA hps
  have hu := maxPositive_four_theta h hno hU hpU hp4
  have hdegU := two_four_canonical_degree h hU hpU hsU hs4 hps.symm hu
  have hne : T ≠ U := by intro he; exact hsT (he.symm ▸ hsU)
  have hi := positive_four_intersection h hno hT hU hne hpT hpU hp4
  have hg := positive_singleton_gap_budget h hT hU hne ht hu hi
  have hd := dg_union_add_dg_inter (G := G) (cpr G C T) (cpr G C U) p
  have hm := dg_mono (G := G) (union_subset (cpr_subset (G := G) C T) (cpr_subset (G := G) C U)) p
  omega


lemma low_four_apf_impossible {A C : Finset V} (h : C02Input G A C)
    (hfive : 5 ≤ #(degreeFourRows G A C)) (hap : APF G A C)
    (hno : ∀ K ∈ maxHighFamily G A C, ∀ p ∈ K, dg G C p ≠ 4) : False := by
  obtain ⟨p, hpD⟩ := card_pos.mp (show 0 < #(degreeFourRows G A C) by omega)
  obtain ⟨hpA, hp4⟩ := mem_degreeFourRows.mp hpD
  have hc := card_erase_add_one hpD
  obtain ⟨q, hq⟩ := card_pos.mp (show 0 < #((degreeFourRows G A C).erase p) by omega)
  obtain ⟨hqp, hqD⟩ := mem_erase.mp hq
  obtain ⟨hqA, hq4⟩ := mem_degreeFourRows.mp hqD
  obtain ⟨T, hT, hpT, hqT⟩ := hap p hpA q hqA hqp.symm
  have ht := maxPositive_four_theta h hno hT hpT hp4
  have hEr := theta_erase (G := G) (C := C) hpT
  have hEθ := erase_four_theta_le_one h hno hT hpT hqT hqp hq4
  have hmono := dg_mono (G := G) (cpr_subset (G := G) C T) p
  have hdegT : dg G (cpr G C T) p = 4 := by omega
  have hb := theta_one_four_trace_bound h hT ht
  have hnsub : ¬ degreeFourRows G A C ⊆ T := by
    intro hs
    have hi : degreeFourRows G A C ∩ T = degreeFourRows G A C := inter_eq_left.mpr hs
    rw [hi] at hb
    omega
  obtain ⟨s, hsD, hsT⟩ := not_subset.mp hnsub
  obtain ⟨hsA, hs4⟩ := mem_degreeFourRows.mp hsD
  have hps : p ≠ s := by intro he; exact hsT (he ▸ hpT)
  obtain ⟨U, hU, hpU, hsU⟩ := hap p hpA s hsA hps
  have hu := maxPositive_four_theta h hno hU hpU hp4
  have hdegU := two_four_canonical_degree h hU hpU hsU hs4 hps.symm hu
  have hne : T ≠ U := by intro he; exact hsT (he.symm ▸ hsU)
  have hi := positive_four_intersection h hno hT hU hne hpT hpU hp4
  have hg := positive_singleton_gap_budget h hT hU hne ht hu hi
  have hd := dg_union_add_dg_inter (G := G) (cpr G C T) (cpr G C U) p
  have hm := dg_mono (G := G) (union_subset (cpr_subset (G := G) C T) (cpr_subset (G := G) C U)) p
  omega

lemma five_four_apf_impossible_with_resource {A C : Finset V} (h : C02Input G A C)
    (hfive : 5 ≤ #(degreeFourRows G A C)) (hb4 : FourResourceBound G A C) (hap : APF G A C) : False := by
  have hno := no_high_four h hfive hap hb4
  exact low_four_apf_impossible h hfive hap hno


lemma actual_h4_items {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2)
    (hl4 : highLoss G C K = 4) :
    ∀ T ∈ strictContainingFamily G A C K,
      (petalD G C K T = 1 ∧ ec G (T \ K) (corePlus G C K) = 3 ∧
        ec G K (petalJ G C K T) = 0 ∧ df G C (T \ K) ≤ 2) ∨
      (-2 ≤ petalD G C K T ∧ petalD G C K T ≤ 1 ∧
        6 + petalD G C K T - (ec G K (petalJ G C K T) : ℤ) ≤ ec G (T \ K) (corePlus G C K) ∧
        df G C (T \ K) ≤ 1 + 2 * petalD G C K T + ec G K (petalJ G C K T)) := by
  intro T hT
  by_cases hsmall : #(T \ K) + #(petalJ G C K T) ≤ 2
  · obtain ⟨_, _, hd, ha, hb, hdf⟩ := strict_small h hK htK hT hsmall
    exact Or.inl ⟨hd, hb, ha, hdf⟩
  · have he := (strict_petal_exact h hK htK hT).1
    have ho : (0 : ℤ) ≤ ec G (T \ K) (C \ (corePlus G C K ∪ petalJ G C K T)) := by positivity
    have hb := strict_d_bounds h hK htK hT
    have hgeom := (high_geometry h hK htK).2.1
    have hlarge := strict_large h hK htK hT (by omega)
    exact Or.inr ⟨by omega, by omega, hlarge, by omega⟩

lemma actual_h4_budgets {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxHighFamily G A C) (htK : thetaC02 G C K = 2)
    (hl4 : highLoss G C K = 4) (hdf : 2 ≤ df G C K) :
    (∑ T ∈ strictContainingFamily G A C K, ec G (T \ K) (corePlus G C K)) ≤ 10 ∧
    (∑ T ∈ strictContainingFamily G A C K, ec G K (petalJ G C K T)) ≤ 2 := by
  have hb := strict_boundary_budget h hK htK
  have ha := strict_scar_budget h hK htK
  constructor
  · have hh : (∑ T ∈ strictContainingFamily G A C K, (ec G (T \ K) (corePlus G C K) : ℤ)) ≤ 10 := by omega
    exact_mod_cast hh
  · have hh : (∑ T ∈ strictContainingFamily G A C K, (ec G K (petalJ G C K T) : ℤ)) ≤ 2 := by omega
    exact_mod_cast hh


lemma four_resource_bound {A C : Finset V} (h : C02Input G A C) : FourResourceBound G A C := by
  intro K hK htK hl4 hdf
  have hitems := actual_h4_items h hK htK hl4
  obtain ⟨hb, ha⟩ := actual_h4_budgets h hK htK hl4 hdf
  apply Erdos585.QB6C02TwoScar.two_scar_int (strictContainingFamily G A C K)
    (petalD G C K) (fun T => df G C (T \ K))
    (fun T => ec G (T \ K) (corePlus G C K)) (fun T => ec G K (petalJ G C K T))
  · intro T hT
    have hTA := (maxPositive_data h (mem_strictContainingFamily.mp hT).1).1
    exact (c02_deficit_bounds h (sdiff_subset (s := T) (t := K) |>.trans hTA)).1
  · exact hitems
  · exact hb
  · exact ha

lemma five_four_apf_impossible {A C : Finset V} (h : C02Input G A C)
    (hfive : 5 ≤ #(degreeFourRows G A C)) (hap : APF G A C) : False :=
  five_four_apf_impossible_with_resource h hfive (four_resource_bound h) hap

theorem five4_good_pair : Five4GoodPair.{u} := by
  intro V _ G _ A C h hfive
  classical
  by_contra hnone
  have hap : APF G A C := apf_of_no_good_pair h fun D _ _ hgood => hnone ⟨D, hgood⟩
  exact five_four_apf_impossible h hfive hap

theorem five4_repair : Five4Repair.{u} := by
  intro V _ G _ A C h hfive
  obtain ⟨D, hD⟩ := five4_good_pair G A C h hfive
  exact goodPair_quartic h hD

#print axioms four_resource_bound
#print axioms five4_good_pair
#print axioms five4_repair
end Erdos585.QB6C02Five4
