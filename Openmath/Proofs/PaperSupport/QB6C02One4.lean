import Openmath.Proofs.PaperSupport.QB6C02Five4
import Openmath.Proofs.PaperSupport.QB6C02PointIncidence

/- 

-/
open Finset
open Erdos585.QB4 Erdos585.QB5 Erdos585.QB6Assembly
open Erdos585.QB6C02PartialFactor Erdos585.QB6C02NonlinearCore
open Erdos585.QB6C02NoTheta3 Erdos585.QB6C02Five4
namespace Erdos585.QB6C02One4
universe u
variable {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
set_option maxHeartbeats 1800000

def One4GoodPair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V), C02Input G A C → 1 ≤ #(degreeFourRows G A C) →
      ∃ D, GoodPair G A C D

def One4Repair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V), C02Input G A C → 1 ≤ #(degreeFourRows G A C) → Quartic G A C

variable {G}

lemma high_private_row {A C H : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) (htH : thetaC02 G C H = 2)
    (hl : highLoss G C H = 4) (hdflo : 2 ≤ df G C H) (hdfhi : df G C H ≤ 3) :
    ∃ r ∈ A \ (H ∪ (strictContainingFamily G A C H).biUnion (fun T => T \ H)),
      0 < 6 - (dg G C r : ℤ) := by
  let R := (strictContainingFamily G A C H).biUnion (fun T => T \ H)
  let W := A \ (H ∪ R)
  have hHA := (high_data h hH htH).1
  have hRA : R ⊆ A := (strict_union_subset (K := H) h).trans sdiff_subset
  have hdis : Disjoint H R := by
    apply disjoint_left.mpr
    intro r hrH hrR
    exact (mem_sdiff.mp (strict_union_subset (K := H) h hrR)).2 hrH
  have hdUnion : df G C (H ∪ R) = df G C H + df G C R := sum_union hdis
  have hdR : df G C R ≤ 7 := by
    have he := strict_deficit_union h hH htH
    have hb := four_resource_bound h H hH htH hl hdflo
    change _ = df G C R at he
    omega
  have hdW : 2 ≤ df G C W := by
    have hs := df_sdiff_add (G := G) (S := C) (union_subset hHA hRA)
    rw [c02_total_deficit h, hdUnion] at hs
    change df G C W + _ = _ at hs
    omega
  change ∃ r ∈ W, 0 < 6 - (dg G C r : ℤ)
  by_contra hn
  push Not at hn
  have hnon : df G C W ≤ 0 := sum_nonpos fun r hr => hn r hr
  omega

lemma erased_theta3_maximal {A C T : Finset V} (h : C02Input G A C)
    (hT : T ∈ maxPositiveFamily G A C) {p : V} (hpT : p ∈ T) (hp4 : dg G C p = 4)
    (htE : thetaC02 G C (T.erase p) = 3) :
    T.erase p ∈ maxThetaThreeFamily G A C ∧ cpr G C T = cpr G C (T.erase p) := by
  obtain ⟨hTA, _, htpos, hmT⟩ := maxPositive_data h hT
  have hEA : T.erase p ⊆ A := (erase_subset _ _).trans hTA
  constructor
  · apply mem_maximalMembers.mpr
    refine ⟨mem_thetaThreeSets.mpr ⟨hEA, htE⟩, ?_⟩
    intro M hM hEM
    obtain ⟨hMA, htM⟩ := mem_thetaThreeSets.mp hM
    have hpM : p ∉ M := fun hp => theta3_no_four h hMA htM hp hp4
    have hI : T ∩ M = T.erase p := by
      apply Subset.antisymm
      · intro a ha
        obtain ⟨haT, haM⟩ := mem_inter.mp ha
        exact mem_erase.mpr ⟨fun he => hpM (he ▸ haM), haT⟩
      · exact subset_inter (erase_subset _ _) hEM
    have hMT : M ⊆ T := by
      by_contra hh
      have hUn : T ∪ M ≠ T := by intro he; exact hh (he ▸ subset_union_right)
      have hUb := hmT (T ∪ M) (union_subset hTA hMA) subset_union_left hUn
      have hs := theta_supermodular (G := G) C T M
      rw [hI] at hs
      omega
    apply Subset.antisymm _ hEM
    intro a ha
    exact mem_erase.mpr ⟨fun he => hpM (he ▸ ha), hMT ha⟩
  · apply Subset.antisymm
    · intro c hc
      obtain ⟨hcC, hdT⟩ := mem_cpr.mp hc
      by_contra hn
      have hlo := theta3_outside_low h hEA htE (mem_sdiff.mpr ⟨hcC, hn⟩)
      by_cases hadj : G.Adj c p
      · have hd := dg_erase_add (G := G) hpT c hadj
        omega
      · have hd := dg_erase_of_not_adj (G := G) (T := T) hadj
        omega
    · intro c hc
      obtain ⟨hcC, hdE⟩ := mem_cpr.mp hc
      exact mem_cpr.mpr ⟨hcC, hdE.trans (dg_mono (G := G) (erase_subset _ _) c)⟩

lemma theta3_p_traces_disjoint {A C K L : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hL : L ∈ maxThetaThreeFamily G A C)
    (hne : K ≠ L) {p : V} (hpA : p ∈ A) (hp4 : dg G C p = 4) :
    dg G (cpr G C K ∩ cpr G C L) p = 0 := by
  obtain ⟨hKA, htK⟩ := mem_thetaThreeSets.mp (mem_maximalMembers.mp hK).1
  obtain ⟨hLA, htL⟩ := mem_thetaThreeSets.mp (mem_maximalMembers.mp hL).1
  have hdis := maximal_theta3_disjoint h hK hL hne
  have hpK : p ∉ K := fun hp => theta3_no_four h hKA htK hp hp4
  have hpL : p ∉ L := fun hp => theta3_no_four h hLA htL hp hp4
  have hpUn : p ∉ K ∪ L := by simpa only [mem_union, not_or] using And.intro hpK hpL
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro c hc hadj
  obtain ⟨hcK, hcL⟩ := mem_inter.mp hc
  have hcC := (mem_cpr.mp hcK).1
  have hk3 := (mem_cpr.mp hcK).2
  have hl3 := (mem_cpr.mp hcL).2
  have hd := dg_union_of_disjoint (G := G) hdis c
  have hds := dg_union_of_disjoint (G := G) (disjoint_singleton_left.mpr hpUn) c
  simp only [singleton_union] at hds
  have hsingle : dg G ({p} : Finset V) c = 1 := by
    simp only [dg, filter_singleton, if_pos (G.adj_symm hadj), card_singleton]
  have hsub : insert p (K ∪ L) ⊆ A := insert_subset_iff.mpr ⟨hpA, union_subset hKA hLA⟩
  have hmono := dg_mono (G := G) hsub c
  rw [hsingle] at hds
  rw [h.satC c hcC] at hmono
  omega

lemma one4_no_high {A C : Finset V} (h : C02Input G A C) (hap : APF G A C) :
    ∀ H ∈ maxHighFamily G A C, ∀ p ∈ H, dg G C p ≠ 4 := by
  intro H hH p hpH hp4
  have htH := high_four_theta h hH hpH hp4
  have hHA := (high_data h hH htH).1
  have hpA := hHA hpH
  have hout := high_four_outgoing h hap (four_resource_bound h) hH hpH hp4
  obtain ⟨htK, hK, hPlus, hdp, hl4, hdflo, hdfhi⟩ := high_four_shape h hH hpH hp4 hout
  obtain ⟨r, hrW, _⟩ := high_private_row h hH htH hl4 hdflo hdfhi
  obtain ⟨hrA, hrOut⟩ := mem_sdiff.mp hrW
  have hrH : r ∉ H := fun hh => hrOut (mem_union_left _ hh)
  have hrR : r ∉ (strictContainingFamily G A C H).biUnion (fun T => T \ H) :=
    fun hh => hrOut (mem_union_right _ hh)
  have hpr : p ≠ r := by intro he; exact hrH (he ▸ hpH)
  obtain ⟨T, hT, hpT, hrT⟩ := hap p hpA r hrA hpr
  have hnot : ¬ H ⊆ T := by
    intro hHT
    have hne : T ≠ H := by intro he; exact hrH (he ▸ hrT)
    exact hrR (mem_biUnion.mpr ⟨T, mem_strictContainingFamily.mpr ⟨hT, hHT, hne⟩,
      mem_sdiff.mpr ⟨hrT, hrH⟩⟩)
  have hi := high_partial_singleton h hH htH hT hnot hpH hpT hp4
  have hb := singleton_gap_budget h hH htH hT hnot hi
  obtain ⟨hTA, h3T, hpos, _⟩ := maxPositive_data h hT
  have hEr := theta_erase (G := G) (C := C) hpT
  have h2E : 2 ≤ #(T.erase p) := by have hc := card_erase_add_one hpT; omega
  have hEb := theta_order_two_le_three h ((erase_subset _ _).trans hTA) h2E
  have hd := dg_union_add_dg_inter (G := G) (corePlus G C H) (cpr G C T) p
  have hdu := dg_mono (G := G) (union_subset (corePlus_subset (G := G) C H) (cpr_subset (G := G) C T)) p
  have htT : thetaC02 G C T = 1 := by omega
  have hdegT : dg G (cpr G C T) p = 2 := by omega
  have htL : thetaC02 G C (T.erase p) = 3 := by omega
  obtain ⟨hL, hcan⟩ := erased_theta3_maximal h hT hpT hp4 htL
  have hKL : H.erase p ≠ T.erase p := by
    intro he
    have hrL : r ∈ T.erase p := mem_erase.mpr ⟨hpr.symm, hrT⟩
    exact hrH ((erase_subset _ _) (he.symm ▸ hrL))
  have hzero := theta3_p_traces_disjoint h hK hL hKL hpA hp4
  have hsum := dg_union_add_dg_inter (G := G) (cpr G C (H.erase p)) (cpr G C (T.erase p)) p
  have hmono := dg_mono (G := G)
    (union_subset (cpr_subset (G := G) C (H.erase p)) (cpr_subset (G := G) C (T.erase p))) p
  rw [hPlus] at hdp
  rw [hcan] at hdegT
  omega

/- The complete actual family through p, with no favorable selector. -/
def pointFamily (G : SimpleGraph V) [DecidableRel G.Adj] (A C : Finset V) (p : V) : Finset (Finset V) := by
  classical
  exact (maxPositiveFamily G A C).filter fun T => p ∈ T

lemma mem_pointFamily {A C T : Finset V} {p : V} :
    T ∈ pointFamily G A C p ↔ T ∈ maxPositiveFamily G A C ∧ p ∈ T := by
  classical
  simp [pointFamily]

lemma point_theta {A C T : Finset V} (h : C02Input G A C) (hap : APF G A C)
    {p : V} (hp4 : dg G C p = 4) (hT : T ∈ pointFamily G A C p) :
    thetaC02 G C T = 1 :=
  maxPositive_four_theta h (one4_no_high h hap) (mem_pointFamily.mp hT).1
    (mem_pointFamily.mp hT).2 hp4

lemma point_meet {A C T U : Finset V} (h : C02Input G A C) (hap : APF G A C)
    {p : V} (hp4 : dg G C p = 4) (hT : T ∈ pointFamily G A C p)
    (hU : U ∈ pointFamily G A C p) (hne : T ≠ U) : T ∩ U = {p} :=
  positive_four_intersection h (one4_no_high h hap) (mem_pointFamily.mp hT).1
    (mem_pointFamily.mp hU).1 hne (mem_pointFamily.mp hT).2 (mem_pointFamily.mp hU).2 hp4

lemma point_petals_pairwise {A C : Finset V} (h : C02Input G A C) (hap : APF G A C)
    {p : V} (hp4 : dg G C p = 4) :
    (pointFamily G A C p : Set (Finset V)).Pairwise
      (fun T U => Disjoint (T.erase p) (U.erase p)) := by
  intro T hT U hU hne
  have hi := point_meet h hap hp4 hT hU hne
  apply disjoint_left.mpr
  intro a haT haU
  obtain ⟨hapn, haT⟩ := mem_erase.mp haT
  have haI := mem_inter.mpr ⟨haT, (mem_erase.mp haU).2⟩
  exact hapn (mem_singleton.mp (hi ▸ haI))

lemma point_cover {A C : Finset V} (h : C02Input G A C) (hap : APF G A C)
    {p : V} (hpA : p ∈ A) :
    (pointFamily G A C p).biUnion (fun T => T.erase p) = A.erase p := by
  classical
  apply Subset.antisymm
  · intro a ha
    obtain ⟨T, hT, haT⟩ := mem_biUnion.mp ha
    obtain ⟨hapn, haT⟩ := mem_erase.mp haT
    exact mem_erase.mpr ⟨hapn, (maxPositive_data h (mem_pointFamily.mp hT).1).1 haT⟩
  · intro a ha
    obtain ⟨hapn, haA⟩ := mem_erase.mp ha
    obtain ⟨T, hT, hpT, haT⟩ := hap p hpA a haA hapn.symm
    exact mem_biUnion.mpr ⟨T, mem_pointFamily.mpr ⟨hT, hpT⟩,
      mem_erase.mpr ⟨hapn, haT⟩⟩

lemma point_family_two {A C : Finset V} (h : C02Input G A C) (hap : APF G A C)
    {p : V} (hpA : p ∈ A) : 2 ≤ #(pointFamily G A C p) := by
  classical
  have hAc : 2 ≤ #A := by have hc := h.card; omega
  have hEc := card_erase_add_one hpA
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < #(A.erase p) by omega)
  have hcover := point_cover h hap hpA
  have haUn : a ∈ (pointFamily G A C p).biUnion (fun T => T.erase p) := hcover ▸ ha
  obtain ⟨T, hT, _⟩ := mem_biUnion.mp haUn
  have hn := card_pos.mpr ⟨T, hT⟩
  by_contra hsmall
  obtain ⟨U, hEq⟩ := card_eq_one.mp (show #(pointFamily G A C p) = 1 by omega)
  have hU : U ∈ pointFamily G A C p := hEq.symm ▸ mem_singleton_self U
  have hpU := (mem_pointFamily.mp hU).2
  have hUA := (maxPositive_data h (mem_pointFamily.mp hU).1).1
  have hpetal : U.erase p = A.erase p := by simpa [hEq] using hcover
  have hfull : U = A := by
    apply Subset.antisymm hUA
    intro b hb
    by_cases he : b = p
    · exact he ▸ hpU
    · exact (erase_subset _ _) (hpetal.symm ▸ mem_erase.mpr ⟨he, hb⟩)
  have htpos := (maxPositive_data h (mem_pointFamily.mp hU).1).2.2.1
  rw [hfull, theta_whole h] at htpos
  omega

lemma point_deficit_sum {A C : Finset V} (h : C02Input G A C) (hap : APF G A C)
    {p : V} (hpA : p ∈ A) (hp4 : dg G C p = 4) :
    (∑ T ∈ pointFamily G A C p, df G C (T.erase p)) = 10 := by
  classical
  have hs := sum_biUnion (f := fun a => (6 : ℤ) - (dg G C a : ℤ))
    (point_petals_pairwise h hap hp4)
  rw [point_cover h hap hpA] at hs
  have he := sum_erase_add A (fun a => (6 : ℤ) - (dg G C a : ℤ)) hpA
  change df G C (A.erase p) + _ = df G C A at he
  rw [hp4, c02_total_deficit h] at he
  change df G C (A.erase p) = ∑ T ∈ pointFamily G A C p, df G C (T.erase p) at hs
  rw [← hs]
  norm_num at he
  omega

lemma point_identities {A C T : Finset V} (_h : C02Input G A C)
    (_hT : T ∈ maxPositiveFamily G A C) (ht : thetaC02 G C T = 1)
    {p : V} (hpT : p ∈ T) :
    df G C (T.erase p) + (ec G (T.erase p) (C \ cpr G C T) : ℤ) =
      3 + 2 * ((#(T.erase p) : ℤ) - #(cpr G C T)) + dg G (cpr G C T) p ∧
    gv G (T.erase p) (cpr G C T) =
      2 * (3 - ((#(T.erase p) : ℤ) - #(cpr G C T)) + dg G (cpr G C T) p) := by
  have hc := card_erase_add_one hpT
  have hEc := sum_erase_add T (fun a => dg G (cpr G C T) a) hpT
  change ec G (T.erase p) (cpr G C T) + dg G (cpr G C T) p = ec G T (cpr G C T) at hEc
  have hcast : (ec G (T.erase p) (cpr G C T) : ℤ) + dg G (cpr G C T) p =
      ec G T (cpr G C T) := by exact_mod_cast hEc
  have hccast : (#(T.erase p) : ℤ) + 1 = #T := by exact_mod_cast hc
  have htheta := theta_canonical (G := G) C T
  rw [ht] at htheta
  have hd := df_eq_df_add_ec (G := G) (cpr_subset (G := G) C T) (T.erase p)
  rw [df_eq] at hd
  constructor
  · linarith
  · unfold gv
    linarith

lemma point_charge {A C T : Finset V} (h : C02Input G A C)
    (hT : T ∈ maxPositiveFamily G A C) (ht : thetaC02 G C T = 1)
    {p : V} (hpT : p ∈ T) :
    df G C (T.erase p) ≤ 3 * (dg G (cpr G C T) p : ℤ) - 5 := by
  obtain ⟨hTA, h3T, _, _⟩ := maxPositive_data h hT
  have hneT : T ≠ A := by intro he; rw [he, theta_whole h] at ht; omega
  have hJbound := (theta_proper_bounds h hTA hneT h3T).1
  have h2E : 2 ≤ #(T.erase p) := by have hc := card_erase_add_one hpT; omega
  have hEA : T.erase p ⊆ A := (erase_subset _ _).trans hTA
  have hneE : T.erase p ≠ A := by
    intro he
    exact (mem_erase.mp (he.symm ▸ hTA hpT)).1 rfl
  have hltE : #(T.erase p) < #A := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hEA, hneE⟩)
  have hJ := cpr_subset (G := G) C T
  have hJc := card_le_card hJ
  have h3 : 3 ≤ #(T.erase p) + #(cpr G C T) := by omega
  have hproper : #(T.erase p) + #(cpr G C T) < #A + #C := by omega
  have hg := h.sparse (T.erase p) hEA (cpr G C T) hJ h3 hproper
  obtain ⟨hd, hv⟩ := point_identities h hT ht hpT
  have hout : (0 : ℤ) ≤ ec G (T.erase p) (C \ cpr G C T) := Nat.cast_nonneg _
  linarith

lemma point_pair_incidence {A C T U : Finset V} (h : C02Input G A C) (hap : APF G A C)
    {p : V} (hp4 : dg G C p = 4) (hT : T ∈ pointFamily G A C p)
    (hU : U ∈ pointFamily G A C p) (hne : T ≠ U) :
    dg G (cpr G C T) p + dg G (cpr G C U) p ≤ 6 := by
  have hg := positive_singleton_gap_budget h (mem_pointFamily.mp hT).1
    (mem_pointFamily.mp hU).1 hne (point_theta h hap hp4 hT) (point_theta h hap hp4 hU)
    (point_meet h hap hp4 hT hU hne)
  have hd := dg_union_add_dg_inter (G := G) (cpr G C T) (cpr G C U) p
  have hm := dg_mono (G := G) (union_subset (cpr_subset (G := G) C T) (cpr_subset (G := G) C U)) p
  omega

lemma point_charge_sum {A C : Finset V} (h : C02Input G A C) (hap : APF G A C)
    {p : V} (hp4 : dg G C p = 4) :
    (∑ T ∈ pointFamily G A C p, df G C (T.erase p)) ≤
      3 * ((∑ T ∈ pointFamily G A C p, dg G (cpr G C T) p : ℕ) : ℤ) -
        5 * (#(pointFamily G A C p) : ℤ) := by
  classical
  calc
    _ ≤ ∑ T ∈ pointFamily G A C p, (3 * (dg G (cpr G C T) p : ℤ) - 5) :=
      sum_le_sum fun T hT => point_charge h (mem_pointFamily.mp hT).1
        (point_theta h hap hp4 hT) (mem_pointFamily.mp hT).2
    _ = _ := by
      simp only [sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, ← Nat.cast_sum]
      ring

lemma point_two_incidence {A C : Finset V} (h : C02Input G A C) (hap : APF G A C)
    {p : V} (hp4 : dg G C p = 4) (hc : #(pointFamily G A C p) = 2) :
    (∑ T ∈ pointFamily G A C p, dg G (cpr G C T) p) ≤ 6 := by
  classical
  obtain ⟨T, U, hne, hF⟩ := card_eq_two.mp hc
  have hT : T ∈ pointFamily G A C p := hF.symm ▸ (by simp)
  have hU : U ∈ pointFamily G A C p := hF.symm ▸ (by simp)
  simpa [hF, hne] using point_pair_incidence h hap hp4 hT hU hne

/-- Only the actual incidence helper is imported at the producer. -/
lemma one4_apf_impossible {A C : Finset V} (h : C02Input G A C) (hap : APF G A C)
    {p : V} (hpA : p ∈ A) (hp4 : dg G C p = 4) : False := by
  classical
  have hd := point_deficit_sum h hap hpA hp4
  have hc := point_family_two h hap hpA
  have hs := point_charge_sum h hap hp4
  by_cases hc2 : #(pointFamily G A C p) = 2
  · have hb := point_two_incidence h hap hp4 hc2
    omega
  · have hb := Erdos585.QB6C02PointIncidence.point_incidence_eight h hpA hp4
      (pointFamily G A C p)
      (fun T hT => (maxPositive_data h (mem_pointFamily.mp hT).1).1)
      (fun T hT => (mem_pointFamily.mp hT).2)
      (fun T hT U hU hne => point_meet h hap hp4 hT hU hne)
    omega

theorem one4_good_pair : One4GoodPair.{u} := by
  intro V _ G _ A C h hone
  classical
  obtain ⟨p, hpD⟩ := card_pos.mp (show 0 < #(degreeFourRows G A C) by omega)
  obtain ⟨hpA, hp4⟩ := mem_degreeFourRows.mp hpD
  by_contra hnone
  have hap : APF G A C := apf_of_no_good_pair h fun D _ _ hgood => hnone ⟨D, hgood⟩
  exact one4_apf_impossible h hap hpA hp4

theorem one4_repair : One4Repair.{u} := by
  intro V _ G _ A C h hone
  obtain ⟨D, hD⟩ := one4_good_pair G A C h hone
  exact goodPair_quartic h hD

#print axioms one4_apf_impossible
#print axioms one4_good_pair
#print axioms one4_repair
#print axioms pointFamily
#print axioms mem_pointFamily
#print axioms point_theta
#print axioms point_meet
#print axioms point_petals_pairwise
#print axioms point_cover
#print axioms point_family_two
#print axioms point_deficit_sum
#print axioms point_identities
#print axioms point_charge
#print axioms point_pair_incidence
#print axioms point_charge_sum
#print axioms point_two_incidence

#print axioms high_private_row
#print axioms erased_theta3_maximal
#print axioms theta3_p_traces_disjoint
#print axioms one4_no_high
end Erdos585.QB6C02One4
