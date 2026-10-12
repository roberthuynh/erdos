import Openmath.Proofs.PaperSupport.QB6C02MinFiveCore
import Openmath.Proofs.PaperSupport.QB6C02One4

/- 


-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
open Finset
open Erdos585.QB4 Erdos585.QB5 Erdos585.QB6Assembly
open Erdos585.QB6C02PartialFactor Erdos585.QB6C02NonlinearCore
open Erdos585.QB6C02NoTheta3 Erdos585.QB6C02Five4
open Erdos585.QB6C02MinFive
open Erdos585.QB6C02One4
namespace Erdos585.QB6C02OrdinaryFive
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma ordinary_high_theta {A C H : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) {p : V} (hpH : p ∈ H)
    (ho : Ordinary G A C p) : thetaC02 G C H = 2 := by
  obtain ⟨hHA, hH3, htH, _, _⟩ := high_data_all h hH
  have ht := ordinary_theta_le_two h hHA (by omega) hpH ho
  omega

lemma erased_core_maximal {A C T : Finset V} (h : C02Input G A C)
    (hT : T ∈ maxPositiveFamily G A C) {p : V} (hpT : p ∈ T)
    (ho : Ordinary G A C p) (htE : thetaC02 G C (T.erase p) = 3) :
    T.erase p ∈ maxThetaThreeFamily G A C ∧ cpr G C T = cpr G C (T.erase p) := by
  obtain ⟨hTA, _, htpos, hmT⟩ := maxPositive_data h hT
  have hEA : T.erase p ⊆ A := (erase_subset _ _).trans hTA
  have hmax : T.erase p ∈ maxThetaThreeFamily G A C := by
    apply mem_maximalMembers.mpr
    refine ⟨mem_thetaThreeSets.mpr ⟨hEA, htE⟩, ?_⟩
    intro M hM hEM
    obtain ⟨hMA, htM⟩ := mem_thetaThreeSets.mp hM
    have hpM : p ∉ M := by
      obtain ⟨K, hK, hMK⟩ := exists_maximal_extension hM
      exact fun hp => ho K hK (hMK hp)
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
  have hTe : T = insert p (T.erase p) := (insert_erase hpT).symm
  refine ⟨hmax, ?_⟩
  conv_lhs => rw [hTe]
  exact core_insert_cpr h hEA htE (notMem_erase _ _)

lemma high_erased_core_maximal {A C H : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) {p : V} (hpH : p ∈ H)
    (ho : Ordinary G A C p) (htE : thetaC02 G C (H.erase p) = 3) :
    H.erase p ∈ maxThetaThreeFamily G A C ∧ cpr G C H = cpr G C (H.erase p) := by
  obtain ⟨hHA, _, _, _, hmH⟩ := high_data_all h hH
  have htH := ordinary_high_theta h hH hpH ho
  have hEA : H.erase p ⊆ A := (erase_subset _ _).trans hHA
  have hmax : H.erase p ∈ maxThetaThreeFamily G A C := by
    apply mem_maximalMembers.mpr
    refine ⟨mem_thetaThreeSets.mpr ⟨hEA, htE⟩, ?_⟩
    intro M hM hEM
    obtain ⟨hMA, htM⟩ := mem_thetaThreeSets.mp hM
    have hpM : p ∉ M := by
      obtain ⟨K, hK, hMK⟩ := exists_maximal_extension hM
      exact fun hp => ho K hK (hMK hp)
    have hI : H ∩ M = H.erase p := by
      apply Subset.antisymm
      · intro a ha
        obtain ⟨haH, haM⟩ := mem_inter.mp ha
        exact mem_erase.mpr ⟨fun he => hpM (he ▸ haM), haH⟩
      · exact subset_inter (erase_subset _ _) hEM
    have hMH : M ⊆ H := by
      by_contra hh
      have hUn : H ∪ M ≠ H := by intro he; exact hh (he ▸ subset_union_right)
      have hUb := hmH (H ∪ M) (union_subset hHA hMA) subset_union_left hUn
      have hs := theta_supermodular (G := G) C H M
      rw [hI] at hs
      omega
    apply Subset.antisymm _ hEM
    intro a ha
    exact mem_erase.mpr ⟨fun he => hpM (he ▸ ha), hMH ha⟩
  have hHe : H = insert p (H.erase p) := (insert_erase hpH).symm
  refine ⟨hmax, ?_⟩
  conv_lhs => rw [hHe]
  exact core_insert_cpr h hEA htE (notMem_erase _ _)

lemma core_point_traces_disjoint {A C K L : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hL : L ∈ maxThetaThreeFamily G A C)
    (hne : K ≠ L) {p : V} (hpA : p ∈ A) (hpK : p ∉ K) (hpL : p ∉ L) :
    dg G (cpr G C K ∩ cpr G C L) p = 0 := by
  have hdis := maximal_theta3_disjoint h hK hL hne
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
  have hsub : insert p (K ∪ L) ⊆ A := insert_subset_iff.mpr ⟨hpA, union_subset (core_data hK).1 (core_data hL).1⟩
  have hmono := dg_mono (G := G) hsub c
  rw [hsingle] at hds
  rw [h.satC c hcC] at hmono
  omega

lemma common_trace_le_gap (C K T : Finset V) {p : V} (hi : K ∩ T = {p}) :
    (dg G (cpr G C K ∩ cpr G C T) p : ℤ) ≤ ∑ c ∈ C, columnGap (G := G) K T c := by
  let S := (cpr G C K ∩ cpr G C T).filter fun c => G.Adj p c
  have hSC : S ⊆ C := fun c hc => (mem_cpr.mp (mem_inter.mp (mem_filter.mp hc).1).1).1
  have hunit : ∀ c ∈ S, columnGap (G := G) K T c = 1 := by
    intro c hc
    obtain ⟨hci, hac⟩ := mem_filter.mp hc
    obtain ⟨hcK, hcT⟩ := mem_inter.mp hci
    exact singleton_gap_one hi (mem_cpr.mp hcK).2 (mem_cpr.mp hcT).2 hac
  have hsum := sum_le_sum_of_subset_of_nonneg hSC (fun c _ _ => columnGap_nonneg (G := G) K T c)
  have hss : (∑ c ∈ S, columnGap (G := G) K T c) = (dg G (cpr G C K ∩ cpr G C T) p : ℤ) := by
    rw [sum_congr rfl hunit]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    rfl
  rw [hss] at hsum
  exact hsum

lemma ordinary_high_unique {A C H L : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) (hL : L ∈ maxHighFamily G A C)
    {p : V} (hpH : p ∈ H) (hpL : p ∈ L) (hp5 : dg G C p = 5)
    (ho : Ordinary G A C p) : H = L := by
  by_contra hne
  obtain ⟨hHA, hH3, _, _, hmH⟩ := high_data_all h hH
  obtain ⟨hLA, hL3, _, _, _⟩ := high_data_all h hL
  have htH := ordinary_high_theta h hH hpH ho
  have htL := ordinary_high_theta h hL hpL ho
  have hnot : ¬ L ⊆ H := by
    intro hs
    have he := (mem_maximalMembers.mp hL).2 H (mem_maximalMembers.mp hH).1 hs
    exact hne he
  have hUn : H ∪ L ≠ H := by intro he; exact hnot (he ▸ subset_union_right)
  have hUb := hmH (H ∪ L) (union_subset hHA hLA) subset_union_left hUn
  have hs := theta_supermodular (G := G) C H L
  have hpI : p ∈ H ∩ L := mem_inter.mpr ⟨hpH, hpL⟩
  have hIlt : #(H ∩ L) < 2 := by
    by_contra hh
    have hb := ordinary_theta_le_two h (inter_subset_left.trans hHA) (by omega) hpI ho
    omega
  have hIp : H ∩ L = {p} := by
    have hc : 0 < #(H ∩ L) := card_pos.mpr ⟨p, hpI⟩
    obtain ⟨a, ha⟩ := card_eq_one.mp (show #(H ∩ L) = 1 by omega)
    have he : p = a := mem_singleton.mp (ha ▸ hpI)
    simpa [he] using ha
  have hg := theta_gap_sum (G := G) C H L
  have hsingle : thetaC02 G C ({p} : Finset V) = 4 := by
    simpa using theta_small (G := G) C (Z := {p}) (by simp)
  rw [hIp, hsingle, htH, htL] at hg
  have hb := common_trace_le_gap (G := G) C H L hIp
  have herH := theta_erase (G := G) (C := C) hpH
  have herL := theta_erase (G := G) (C := C) hpL
  have hcH := card_erase_add_one hpH
  have hcL := card_erase_add_one hpL
  have htEH := theta_order_two_le_three h ((erase_subset p H).trans hHA) (by omega)
  have htEL := theta_order_two_le_three h ((erase_subset p L).trans hLA) (by omega)
  have hd := dg_union_add_dg_inter (G := G) (cpr G C H) (cpr G C L) p
  have hu := dg_mono (G := G) (union_subset (cpr_subset (G := G) C H) (cpr_subset (G := G) C L)) p
  have hdH : dg G (cpr G C H) p = 3 := by omega
  have hdL : dg G (cpr G C L) p = 3 := by omega
  have ht3H : thetaC02 G C (H.erase p) = 3 := by omega
  have ht3L : thetaC02 G C (L.erase p) = 3 := by omega
  obtain ⟨hKH, hcanH⟩ := high_erased_core_maximal h hH hpH ho ht3H
  obtain ⟨hKL, hcanL⟩ := high_erased_core_maximal h hL hpL ho ht3L
  have hneKL : H.erase p ≠ L.erase p := by
    intro he
    have hiH := insert_erase hpH
    have hiL := insert_erase hpL
    rw [he] at hiH
    exact hne (hiH.symm.trans hiL)
  have hz := core_point_traces_disjoint h hKH hKL hneKL (hHA hpH)
    (notMem_erase _ _) (notMem_erase _ _)
  rw [← hcanH, ← hcanL] at hz
  omega

lemma positive_is_high {A C T : Finset V} (h : C02Input G A C)
    (hT : T ∈ maxPositiveFamily G A C) (ht : thetaC02 G C T = 2) :
    T ∈ maxHighFamily G A C := by
  obtain ⟨hTA, h3T, _, hmax⟩ := maxPositive_data h hT
  apply mem_maximalMembers.mpr
  refine ⟨mem_highSets.mpr ⟨hTA, h3T, by omega⟩, ?_⟩
  intro U hU hTU
  by_contra hne
  obtain ⟨hUA, _, htU⟩ := mem_highSets.mp hU
  have hb := hmax U hUA hTU hne
  omega

lemma high_partial_theta_one {A C H T : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) {p : V} (hpH : p ∈ H)
    (hp5 : dg G C p = 5) (ho : Ordinary G A C p)
    (hT : T ∈ maxPositiveFamily G A C) (hpT : p ∈ T) (hnot : ¬ H ⊆ T) :
    thetaC02 G C T = 1 := by
  obtain ⟨hTA, h3T, htpos, _⟩ := maxPositive_data h hT
  have ht2 := ordinary_theta_le_two h hTA (by omega) hpT ho
  by_contra hh
  have ht : thetaC02 G C T = 2 := by omega
  have hHT := ordinary_high_unique h hH (positive_is_high h hT ht) hpH hpT hp5 ho
  exact hnot (hHT ▸ Subset.rfl)

lemma ordinary_high_positive_deficit {A C H : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) {p : V} (hpH : p ∈ H)
    (hp5 : dg G C p = 5) : 0 < df G C H := by
  have hHA := (high_data_all h hH).1
  have hs := single_le_sum (f := fun a => (6 : ℤ) - dg G C a)
    (fun a ha => by have hh := h.capA a (hHA ha); omega) hpH
  change (6 : ℤ) - dg G C p ≤ df G C H at hs
  omega

lemma private_apf_member {A C H : Finset V} (h : C02Input G A C)
    (hapf : APF G A C) (hH : H ∈ maxHighFamily G A C)
    {p r : V} (hpH : p ∈ H) (hr : r ∈ privateRows G A C H) :
    ∃ T ∈ maxPositiveFamily G A C, p ∈ T ∧ r ∈ T ∧ ¬ H ⊆ T := by
  have hrA := (private_not_H hr).1
  have hrH := (private_not_H hr).2
  have hpA := (high_data_all h hH).1 hpH
  have hpr : p ≠ r := by intro he; exact hrH (he ▸ hpH)
  obtain ⟨T, hT, hpT, hrT⟩ := hapf p hpA r hrA hpr
  refine ⟨T, hT, hpT, hrT, ?_⟩
  intro hs
  have hne : T ≠ H := by intro he; exact hrH (he ▸ hrT)
  exact private_not_strict hr (mem_strictContainingFamily.mpr ⟨hT, hs, hne⟩) hrT

lemma ordinary_high_outgoing {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hapf : APF G A C) (hH : H ∈ maxHighFamily G A C)
    {p : V} (hpH : p ∈ H) (hp5 : dg G C p = 5) (ho : Ordinary G A C p) :
    1 ≤ dg G (C \ corePlus G C H) p ∧ dg G (C \ corePlus G C H) p ≤ 2 := by
  have htH := ordinary_high_theta h hH hpH ho
  have hdH := ordinary_high_positive_deficit h hH hpH hp5
  have hHA := (high_data_all h hH).1
  have hEr := theta_erase (G := G) (C := C) hpH
  have hcEr := card_erase_add_one hpH
  have hEb := theta_order_two_le_three h ((erase_subset p H).trans hHA)
    (by have hh := (high_data_all h hH).2.1; omega)
  have hcplus : cpr G C H ⊆ corePlus G C H := by
    intro c hc
    obtain ⟨hcC, hd⟩ := mem_cpr.mp hc
    exact mem_filter.mpr ⟨hcC, by omega⟩
  have hdegree := dg_mono (G := G) hcplus p
  have hsplit := dg_sdiff_add (G := G) (corePlus_subset (G := G) C H) p
  have hout : dg G (C \ corePlus G C H) p ≠ 0 := by
    intro hz
    obtain ⟨r, hr, _⟩ := minfive_private_row h hm hH htH hdH
    obtain ⟨T, hT, hpT, _, hnot⟩ := private_apf_member h hapf hH hpH hr
    have hi := high_partial_ordinary h hH htH hT hnot hpH hpT ho
    have hg := singleton_gap_budget h hH htH hT hnot hi
    have htT := high_partial_theta_one h hH hpH hp5 ho hT hpT hnot
    obtain ⟨hTA, h3T, _, _⟩ := maxPositive_data h hT
    have heT := theta_erase (G := G) (C := C) hpT
    have hcT := card_erase_add_one hpT
    have hbT := theta_order_two_le_three h ((erase_subset p T).trans hTA) (by omega)
    have hdu := dg_union_add_dg_inter (G := G) (corePlus G C H) (cpr G C T) p
    have hmono := dg_mono (G := G)
      (union_subset (corePlus_subset (G := G) C H) (cpr_subset (G := G) C T)) p
    omega
  omega

lemma private_members_meet {A C H T U : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) {p : V} (hpH : p ∈ H)
    (hp5 : dg G C p = 5) (ho : Ordinary G A C p)
    (hT : T ∈ maxPositiveFamily G A C) (hpT : p ∈ T) (hnotT : ¬ H ⊆ T)
    (hU : U ∈ maxPositiveFamily G A C) (hpU : p ∈ U) (hnotU : ¬ H ⊆ U)
    (hne : T ≠ U) : T ∩ U = {p} := by
  obtain ⟨hTA, h3T, _, hmT⟩ := maxPositive_data h hT
  obtain ⟨hUA, _, _, _⟩ := maxPositive_data h hU
  have htT := high_partial_theta_one h hH hpH hp5 ho hT hpT hnotT
  have htU := high_partial_theta_one h hH hpH hp5 ho hU hpU hnotU
  have hnotUT : ¬ U ⊆ T := by
    intro hs
    exact hne ((mem_maximalMembers.mp hU).2 T (mem_maximalMembers.mp hT).1 hs)
  have hUn : T ∪ U ≠ T := by intro he; exact hnotUT (he ▸ subset_union_right)
  have hUb := hmT (T ∪ U) (union_subset hTA hUA) subset_union_left hUn
  have hs := theta_supermodular (G := G) C T U
  have hpI : p ∈ T ∩ U := mem_inter.mpr ⟨hpT, hpU⟩
  have hIlt : #(T ∩ U) < 2 := by
    by_contra hh
    by_cases hI3 : 3 ≤ #(T ∩ U)
    · obtain ⟨L, hL, hIL⟩ := exists_maximal_extension
        ((mem_highSets (G := G) (A := A) (C := C)).mpr ⟨inter_subset_left.trans hTA, hI3, by omega⟩)
      have hHL := ordinary_high_unique h hH hL hpH (hIL hpI) hp5 ho
      have hi := high_partial_ordinary h hH (ordinary_high_theta h hH hpH ho) hT hnotT hpH hpT ho
      have hIinH : T ∩ U ⊆ H := hHL ▸ hIL
      have hIin : T ∩ U ⊆ H ∩ T := subset_inter hIinH inter_subset_left
      have hc := card_le_card hIin
      rw [hi] at hc
      simp only [card_singleton] at hc
      omega
    · have hb := theta_small (G := G) C (Z := T ∩ U) (by omega)
      omega
  obtain ⟨a, ha⟩ := card_eq_one.mp (show #(T ∩ U) = 1 by
    have hc := card_pos.mpr ⟨p, hpI⟩; omega)
  have he : p = a := mem_singleton.mp (ha ▸ hpI)
  simpa [he] using ha

lemma one_outside_private_trace {A C H T : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) {p : V} (hpH : p ∈ H)
    (hp5 : dg G C p = 5) (ho : Ordinary G A C p)
    (hout : dg G (C \ corePlus G C H) p = 1)
    (hT : T ∈ maxPositiveFamily G A C) (hpT : p ∈ T) (hnot : ¬ H ⊆ T) :
    dg G (cpr G C T) p = 2 ∧ thetaC02 G C (T.erase p) = 3 ∧
      1 ≤ dg G (cpr G C T \ corePlus G C H) p := by
  have htH := ordinary_high_theta h hH hpH ho
  have hi := high_partial_ordinary h hH htH hT hnot hpH hpT ho
  have hb := singleton_gap_budget h hH htH hT hnot hi
  have htT := high_partial_theta_one h hH hpH hp5 ho hT hpT hnot
  obtain ⟨hTA, h3T, _, _⟩ := maxPositive_data h hT
  have her := theta_erase (G := G) (C := C) hpT
  have hc := card_erase_add_one hpT
  have hEb := theta_order_two_le_three h ((erase_subset p T).trans hTA) (by omega)
  have hsplit := dg_sdiff_add (G := G)
    (inter_subset_right (s₁ := corePlus G C H) (s₂ := cpr G C T)) p
  have heq : cpr G C T \ (corePlus G C H ∩ cpr G C T) = cpr G C T \ corePlus G C H := by
    ext c; simp only [mem_sdiff, mem_inter]; tauto
  rw [heq] at hsplit
  have hsub : cpr G C T \ corePlus G C H ⊆ C \ corePlus G C H :=
    sdiff_subset_sdiff_left (corePlus G C H) (cpr_subset (G := G) C T)
  have hmono := dg_mono (G := G) hsub p
  exact ⟨by omega, by omega, by omega⟩

lemma one_outside_members_equal {A C H T U : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) {p : V} (hpH : p ∈ H)
    (hp5 : dg G C p = 5) (ho : Ordinary G A C p)
    (hout : dg G (C \ corePlus G C H) p = 1)
    (hT : T ∈ maxPositiveFamily G A C) (hpT : p ∈ T) (hnotT : ¬ H ⊆ T)
    (hU : U ∈ maxPositiveFamily G A C) (hpU : p ∈ U) (hnotU : ¬ H ⊆ U) : T = U := by
  by_contra hne
  obtain ⟨_, htET, hNTP⟩ := one_outside_private_trace h hH hpH hp5 ho hout hT hpT hnotT
  obtain ⟨_, htEU, hNUP⟩ := one_outside_private_trace h hH hpH hp5 ho hout hU hpU hnotU
  obtain ⟨hKT, hcanT⟩ := erased_core_maximal h hT hpT ho htET
  obtain ⟨hKU, hcanU⟩ := erased_core_maximal h hU hpU ho htEU
  have hneK : T.erase p ≠ U.erase p := by
    intro he
    have hiT := insert_erase hpT
    have hiU := insert_erase hpU
    rw [he] at hiT
    exact hne (hiT.symm.trans hiU)
  have hz := core_point_traces_disjoint h hKT hKU hneK ((maxPositive_data h hT).1 hpT)
    (notMem_erase _ _) (notMem_erase _ _)
  rw [← hcanT, ← hcanU] at hz
  have hd := dg_union_add_dg_inter (G := G)
    (cpr G C T \ corePlus G C H) (cpr G C U \ corePlus G C H) p
  have hUnion : (cpr G C T \ corePlus G C H) ∪ (cpr G C U \ corePlus G C H) ⊆ C \ corePlus G C H :=
    union_subset (sdiff_subset_sdiff_left (corePlus G C H) (cpr_subset (G := G) C T))
      (sdiff_subset_sdiff_left (corePlus G C H) (cpr_subset (G := G) C U))
  have hu := dg_mono (G := G) hUnion p
  have hInter : (cpr G C T \ corePlus G C H) ∩ (cpr G C U \ corePlus G C H) ⊆ cpr G C T ∩ cpr G C U :=
    inter_subset_inter sdiff_subset sdiff_subset
  have hi := dg_mono (G := G) hInter p
  omega

lemma private_deficit_le_member {A C H T : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hT : T ⊆ A) {p : V} (hpH : p ∈ H)
    (hcover : ∀ r ∈ privateRows G A C H, dg G C r = 5 → r ∈ T) :
    df G C (privateRows G A C H) ≤ df G C (T.erase p) := by
  let W := privateRows G A C H
  have hWA : W ⊆ A := sdiff_subset.trans sdiff_subset
  have hz : df G C (W \ T.erase p) = 0 := by
    unfold df
    apply sum_eq_zero
    intro r hr
    obtain ⟨hrW, hrN⟩ := mem_sdiff.mp hr
    have h5 := hm r (hWA hrW)
    have h6 := h.capA r (hWA hrW)
    have hrP : r ≠ p := by intro he; exact (private_not_H hrW).2 (he ▸ hpH)
    have hne : dg G C r ≠ 5 := fun he => hrN (mem_erase.mpr ⟨hrP, hcover r hrW he⟩)
    omega
  have hs := df_sdiff_add (G := G) (S := C) (inter_subset_left (s₁ := W) (s₂ := T.erase p))
  have heq : W \ (W ∩ T.erase p) = W \ T.erase p := by ext a; simp only [mem_sdiff, mem_inter]; tauto
  rw [heq, hz] at hs
  have hb := df_le_of_subset (G := G) (S := C) (inter_subset_right (s₁ := W) (s₂ := T.erase p))
    (fun a ha => h.capA a (hT ((erase_subset _ _) ha)))
  change df G C W ≤ _
  omega

lemma ordinary_high_one_outside_impossible {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hapf : APF G A C) (hH : H ∈ maxHighFamily G A C)
    {p : V} (hpH : p ∈ H) (hp5 : dg G C p = 5) (ho : Ordinary G A C p)
    (hout : dg G (C \ corePlus G C H) p = 1) : False := by
  have htH := ordinary_high_theta h hH hpH ho
  have hdH := ordinary_high_positive_deficit h hH hpH hp5
  have hW := (minfive_private_deficit h hm hH htH hdH).1
  obtain ⟨r, hr, _⟩ := minfive_private_row h hm hH htH hdH
  obtain ⟨T, hT, hpT, _, hnotT⟩ := private_apf_member h hapf hH hpH hr
  have hcover : ∀ s ∈ privateRows G A C H, dg G C s = 5 → s ∈ T := by
    intro s hs _
    obtain ⟨U, hU, hpU, hsU, hnotU⟩ := private_apf_member h hapf hH hpH hs
    exact (one_outside_members_equal h hH hpH hp5 ho hout hT hpT hnotT hU hpU hnotU) ▸ hsU
  have hbound := private_deficit_le_member h hm (maxPositive_data h hT).1 hpH hcover
  have htE := (one_outside_private_trace h hH hpH hp5 ho hout hT hpT hnotT).2.1
  obtain ⟨hK, _⟩ := erased_core_maximal h hT hpT ho htE
  have hcore := core_loss_bound h hK
  omega

lemma ordinary_high_two_shape {A C H : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) {p : V} (hpH : p ∈ H)
    (hp5 : dg G C p = 5) (ho : Ordinary G A C p)
    (hout : dg G (C \ corePlus G C H) p = 2) :
    H.erase p ∈ maxThetaThreeFamily G A C ∧
      corePlus G C H = cpr G C (H.erase p) ∧
      dg G (cpr G C (H.erase p)) p = 3 ∧ highLoss G C H = 4 ∧
      1 ≤ df G C H ∧ df G C H ≤ 2 := by
  have htH := ordinary_high_theta h hH hpH ho
  have hHA := (high_data_all h hH).1
  have hEA : H.erase p ⊆ A := (erase_subset p H).trans hHA
  have her := theta_erase (G := G) (C := C) hpH
  have h2E : 2 ≤ #(H.erase p) := by
    have hc := card_erase_add_one hpH
    have hh := (high_data_all h hH).2.1
    omega
  have hb := theta_order_two_le_three h hEA h2E
  have hsubcan : cpr G C H ⊆ corePlus G C H := by
    intro c hc
    obtain ⟨hcC, hd⟩ := mem_cpr.mp hc
    exact mem_filter.mpr ⟨hcC, by omega⟩
  have hdmono := dg_mono (G := G) hsubcan p
  have hsplit := dg_sdiff_add (G := G) (corePlus_subset (G := G) C H) p
  have hdH : dg G (cpr G C H) p = 3 := by omega
  have htE : thetaC02 G C (H.erase p) = 3 := by omega
  obtain ⟨hK, hcan⟩ := high_erased_core_maximal h hH hpH ho htE
  have hsubPlus : cpr G C (H.erase p) ⊆ corePlus G C H := hcan ▸ hsubcan
  have hdcan : dg G (cpr G C (H.erase p)) p = 3 := by rw [← hcan]; exact hdH
  have hdplus : dg G (corePlus G C H) p = 3 := by omega
  have hplus : corePlus G C H = cpr G C (H.erase p) := by
    apply Subset.antisymm _ hsubPlus
    intro c hc
    by_contra hn
    have hcC := (mem_filter.mp hc).1
    have hc2 := (mem_filter.mp hc).2
    have hlo := theta3_outside_low h hEA htE (mem_sdiff.mpr ⟨hcC, hn⟩)
    have hadj : G.Adj c p := by
      by_contra hh
      have hd := dg_erase_of_not_adj (G := G) (T := H) hh
      omega
    have hs := dg_sdiff_add (G := G) hsubPlus p
    have hpos : 0 < dg G (corePlus G C H \ cpr G C (H.erase p)) p := card_pos.mpr
      ⟨c, mem_filter.mpr ⟨mem_sdiff.mpr ⟨hc, hn⟩, G.adj_symm hadj⟩⟩
    omega
  have hgeom := (high_geometry h hH htH).2.1
  have hcE := (theta3_geometry h hEA htE).2.2.1
  have hcard : (#(H.erase p) : ℤ) + 1 = #H := by exact_mod_cast card_erase_add_one hpH
  have hdK := core_loss_bound h hK
  have hdf := df_sdiff_add (G := G) (S := C) (singleton_subset_iff.mpr hpH)
  have hsingle : df G C ({p} : Finset V) = 1 := by simp [df, hp5]
  rw [sdiff_singleton_eq_erase, hsingle] at hdf
  refine ⟨hK, hplus, hdcan, ?_, by omega, by omega⟩
  rw [hplus] at hgeom
  omega

lemma two_outside_private_degree {A C H T : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) {p : V} (hpH : p ∈ H)
    (hp5 : dg G C p = 5) (ho : Ordinary G A C p)
    (hout : dg G (C \ corePlus G C H) p = 2)
    (hT : T ∈ maxPositiveFamily G A C) (hpT : p ∈ T) (hnot : ¬ H ⊆ T) :
    2 ≤ dg G (cpr G C T) p ∧ dg G (cpr G C T) p ≤ 3 := by
  have htH := ordinary_high_theta h hH hpH ho
  have hi := high_partial_ordinary h hH htH hT hnot hpH hpT ho
  have hb := singleton_gap_budget h hH htH hT hnot hi
  have htT := high_partial_theta_one h hH hpH hp5 ho hT hpT hnot
  obtain ⟨hTA, h3T, _, _⟩ := maxPositive_data h hT
  have her := theta_erase (G := G) (C := C) hpT
  have hc := card_erase_add_one hpT
  have hEb := theta_order_two_le_three h ((erase_subset p T).trans hTA) (by omega)
  have hs := dg_union_add_dg_inter (G := G) (corePlus G C H) (cpr G C T) p
  have hcap := dg_mono (G := G)
    (union_subset (corePlus_subset (G := G) C H) (cpr_subset (G := G) C T)) p
  have hsplit := dg_sdiff_add (G := G) (corePlus_subset (G := G) C H) p
  exact ⟨by omega, by omega⟩

lemma erased_private_high {A C H T : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) {p : V} (hpH : p ∈ H)
    (hp5 : dg G C p = 5) (ho : Ordinary G A C p)
    (hT : T ∈ maxPositiveFamily G A C) (hpT : p ∈ T) (hnot : ¬ H ⊆ T)
    (hdT : dg G (cpr G C T) p = 3) :
    T.erase p ∈ maxHighFamily G A C ∧ thetaC02 G C (T.erase p) = 2 := by
  have htH := ordinary_high_theta h hH hpH ho
  have hi := high_partial_ordinary h hH htH hT hnot hpH hpT ho
  have htT := high_partial_theta_one h hH hpH hp5 ho hT hpT hnot
  obtain ⟨hTA, h3T, _, hmT⟩ := maxPositive_data h hT
  have hEA : T.erase p ⊆ A := (erase_subset p T).trans hTA
  have her := theta_erase (G := G) (C := C) hpT
  have htE : thetaC02 G C (T.erase p) = 2 := by omega
  have h3E : 3 ≤ #(T.erase p) := by
    have hc := card_erase_add_one hpT
    by_contra hh
    have hb := theta_small (G := G) C (Z := T.erase p) (by omega)
    omega
  obtain ⟨L, hL, hEL⟩ := exists_maximal_extension
    ((mem_highSets (G := G) (A := A) (C := C)).mpr ⟨hEA, h3E, by omega⟩)
  have hpL : p ∉ L := by
    intro hpL
    have hHL := ordinary_high_unique h hH hL hpH hpL hp5 ho
    have hEH : T.erase p ⊆ H := hHL ▸ hEL
    have hEI : T.erase p ⊆ H ∩ T := subset_inter hEH (erase_subset p T)
    have hc := card_le_card hEI
    rw [hi] at hc
    simp only [card_singleton] at hc
    omega
  have hI : T ∩ L = T.erase p := by
    apply Subset.antisymm
    · intro a ha
      exact mem_erase.mpr ⟨fun he => hpL (he ▸ (mem_inter.mp ha).2), (mem_inter.mp ha).1⟩
    · exact subset_inter (erase_subset p T) hEL
  have hLE : L = T.erase p := by
    apply Subset.antisymm _ hEL
    intro a ha
    by_contra hn
    have hUn : T ∪ L ≠ T := by
      intro he
      have haT := (he ▸ subset_union_right) ha
      exact hn (mem_erase.mpr ⟨fun he' => hpL (he' ▸ ha), haT⟩)
    have hUb := hmT (T ∪ L) (union_subset hTA (high_data_all h hL).1) subset_union_left hUn
    have hs := theta_supermodular (G := G) C T L
    have htL := (high_data_all h hL).2.2.1
    rw [hI] at hs
    omega
  exact ⟨hLE ▸ hL, htE⟩

lemma disjoint_core_shadow {A C K T : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) (hT : T ∈ maxPositiveFamily G A C)
    (htT : thetaC02 G C T = 1) (hdis : Disjoint K T) :
    (∑ c ∈ cpr G C K, min (2 : ℤ) (dg G T c : ℤ)) ≤ 4 := by
  have hKA := (core_data hK).1
  have htK := (core_data hK).2.1
  obtain ⟨hTA, _, _, hmT⟩ := maxPositive_data h hT
  have hUn : K ∪ T ≠ T := by
    intro he
    have hsub : K ⊆ T := he ▸ subset_union_left
    have hzero : K = ∅ := disjoint_self.mp (hdis.mono_right hsub)
    have hcard := (theta3_large_proper h hKA htK).1
    rw [hzero] at hcard
    simp at hcard
  have hUb := hmT (K ∪ T) (union_subset hKA hTA) subset_union_right hUn
  have hcol : ∀ c ∈ C,
      (if 3 ≤ dg G K c then min (2 : ℤ) (dg G T c : ℤ) else 0) ≤
        max 0 ((dg G (K ∪ T) c : ℤ) - 2) -
          max 0 ((dg G T c : ℤ) - 2) - max 0 ((dg G K c : ℤ) - 2) := by
    intro c _
    have hd := dg_union_of_disjoint (G := G) hdis c
    split_ifs <;> omega
  have hs := sum_le_sum hcol
  have hleft : (∑ c ∈ C, if 3 ≤ dg G K c then min (2 : ℤ) (dg G T c : ℤ) else 0) =
      ∑ c ∈ cpr G C K, min (2 : ℤ) (dg G T c : ℤ) := by
    exact (sum_filter _ _).symm
  rw [hleft, sum_sub_distrib, sum_sub_distrib] at hs
  have hcard : (#(K ∪ T) : ℤ) = #K + #T := by exact_mod_cast card_union_of_disjoint hdis
  unfold thetaC02 at htK htT hUb
  linarith

lemma shadow_trace_bound {C K T : Finset V} {p : V}
    (hshadow : (∑ c ∈ cpr G C K, min (2 : ℤ) (dg G T c : ℤ)) ≤ 4)
    (hpT : p ∈ T) (hinside : dg G (cpr G C K) p = 3) :
    dg G (cpr G C K ∩ cpr G C T) p ≤ 1 := by
  let Y := cpr G C K
  have hcol : ∀ c ∈ Y, (if G.Adj p c then (1 : ℤ) else 0) +
      (if c ∈ cpr G C T ∧ G.Adj p c then (1 : ℤ) else 0) ≤ min (2 : ℤ) (dg G T c : ℤ) := by
    intro c _
    by_cases hadj : G.Adj p c
    · have hd : 0 < dg G T c := card_pos.mpr ⟨p, mem_filter.mpr ⟨hpT, G.adj_symm hadj⟩⟩
      by_cases hcanon : c ∈ cpr G C T
      · have h3 := (mem_cpr.mp hcanon).2
        simp only [if_pos hadj, if_pos (And.intro hcanon hadj)]
        omega
      · have hn : ¬ (c ∈ cpr G C T ∧ G.Adj p c) := fun hh => hcanon hh.1
        simp only [if_pos hadj, if_neg hn]
        omega
    · have hn : ¬ (c ∈ cpr G C T ∧ G.Adj p c) := fun hh => hadj hh.2
      simp only [if_neg hadj, if_neg hn]
      omega
  have hs := sum_le_sum hcol
  rw [sum_add_distrib, ← sum_filter, ← sum_filter] at hs
  have he1 : (∑ _c ∈ Y.filter (fun c => G.Adj p c), (1 : ℤ)) = dg G Y p := by
    simp only [sum_const, nsmul_eq_mul, mul_one]; rfl
  have he2 : (∑ _c ∈ Y.filter (fun c => c ∈ cpr G C T ∧ G.Adj p c), (1 : ℤ)) =
      dg G (Y ∩ cpr G C T) p := by
    have hset : Y.filter (fun c => c ∈ cpr G C T ∧ G.Adj p c) =
        (Y ∩ cpr G C T).filter (fun c => G.Adj p c) := by
      ext c
      simp only [mem_filter, mem_inter]
      tauto
    rw [hset]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    rfl
  rw [he1, he2] at hs
  change dg G (Y ∩ cpr G C T) p ≤ 1
  change dg G Y p = 3 at hinside
  change (∑ c ∈ Y, min (2 : ℤ) (dg G T c : ℤ)) ≤ 4 at hshadow
  omega

lemma outside_trace_full {C Y T : Finset V} {p : V}
    (htrace : dg G (C \ Y) p ≤ dg G (cpr G C T \ Y) p) :
    ∀ c ∈ C \ Y, G.Adj p c → c ∈ cpr G C T := by
  let S := (cpr G C T \ Y).filter fun c => G.Adj p c
  let N := (C \ Y).filter fun c => G.Adj p c
  have hSN : S ⊆ N := by
    intro c hc
    obtain ⟨hcs, hadj⟩ := mem_filter.mp hc
    obtain ⟨hcT, hcY⟩ := mem_sdiff.mp hcs
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨(mem_cpr.mp hcT).1, hcY⟩, hadj⟩
  have hNS : #N ≤ #S := htrace
  have he : S = N := eq_of_subset_of_card_le hSN hNS
  intro c hc hadj
  have hcN : c ∈ N := mem_filter.mpr ⟨hc, hadj⟩
  have hcS : c ∈ S := he.symm ▸ hcN
  exact (mem_sdiff.mp (mem_filter.mp hcS).1).1

omit [DecidableEq V] in
lemma degree_five_deficit_pos {A C Z : Finset V} (h : C02Input G A C)
    (hZ : Z ⊆ A) {r : V} (hrZ : r ∈ Z) (hr5 : dg G C r = 5) :
    0 < df G C Z := by
  have hs := single_le_sum (f := fun a => (6 : ℤ) - dg G C a)
    (fun a ha => by have hh := h.capA a (hZ ha); omega) hrZ
  change (6 : ℤ) - dg G C r ≤ df G C Z at hs
  omega

lemma count_two_loss {A C Q : Finset V} (h : C02Input G A C)
    (hQA : Q ⊆ A) (htQ : thetaC02 G C Q = 2) (hdf : 0 < df G C Q)
    {c0 : V} (hc0 : c0 ∈ C) (hd0 : dg G Q c0 = 2) :
    df G C Q ≤ 2 ∧ ∀ c ∈ C, c ≠ c0 → dg G Q c ≠ 2 := by
  have hne : Q ≠ A := by intro he; rw [he, theta_whole h] at htQ; omega
  have h3 : 3 ≤ #Q := by
    by_contra hh
    have hb := theta_small (G := G) C (Z := Q) (by omega)
    omega
  have hloss := theta_loss_bound h hQA hne h3
  have he := df_eq_df_add_ec (G := G) (cpr_subset (G := G) C Q) Q
  have hc0O : c0 ∈ C \ cpr G C Q := mem_sdiff.mpr ⟨hc0, fun hh => by
    have hh3 := (mem_cpr.mp hh).2; omega⟩
  have hsum : (ec G Q (C \ cpr G C Q) : ℤ) =
      ∑ c ∈ C \ cpr G C Q, (dg G Q c : ℤ) := by rw [ec_comm]; simp only [ec, Nat.cast_sum]
  have htwo := single_le_sum (f := fun c => (dg G Q c : ℤ))
    (fun c _ => by positivity) hc0O
  rw [← hsum] at htwo
  refine ⟨by omega, ?_⟩
  intro c hc hne0 hd2
  have hcO : c ∈ C \ cpr G C Q := mem_sdiff.mpr ⟨hc, fun hh => by
    have hh3 := (mem_cpr.mp hh).2; omega⟩
  have hs := sum_erase_add (C \ cpr G C Q) (fun c => (dg G Q c : ℤ)) hc0O
  have ht := single_le_sum (f := fun c => (dg G Q c : ℤ))
    (fun c _ => by positivity) (mem_erase.mpr ⟨hne0, hcO⟩)
  rw [← hsum] at hs
  omega

lemma two_outside_private_bound {A C H T : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) {p : V} (hpH : p ∈ H)
    (hp5 : dg G C p = 5) (ho : Ordinary G A C p)
    (hout : dg G (C \ corePlus G C H) p = 2)
    (hT : T ∈ maxPositiveFamily G A C) (hpT : p ∈ T) (hnot : ¬ H ⊆ T)
    (hpositive : 0 < df G C (T.erase p)) :
    df G C (T.erase p) ≤ 2 ∧
      ∀ c ∈ C \ corePlus G C H, G.Adj p c → 3 ≤ dg G (T.erase p) c := by
  obtain ⟨hK, hplus, hdK, _, _, _⟩ := ordinary_high_two_shape h hH hpH hp5 ho hout
  have htH := ordinary_high_theta h hH hpH ho
  have hHA := (high_data_all h hH).1
  have hTA := (maxPositive_data h hT).1
  have hi := high_partial_ordinary h hH htH hT hnot hpH hpT ho
  have htT := high_partial_theta_one h hH hpH hp5 ho hT hpT hnot
  have hdeg := two_outside_private_degree h hH hpH hp5 ho hout hT hpT hnot
  have her := theta_erase (G := G) (C := C) hpT
  have hcanSplit := dg_sdiff_add (G := G)
    (inter_subset_right (s₁ := corePlus G C H) (s₂ := cpr G C T)) p
  have hsdiff : cpr G C T \ (corePlus G C H ∩ cpr G C T) = cpr G C T \ corePlus G C H := by
    ext c; simp only [mem_sdiff, mem_inter]; tauto
  rw [hsdiff] at hcanSplit
  by_cases hd2 : dg G (cpr G C T) p = 2
  · have htE : thetaC02 G C (T.erase p) = 3 := by omega
    obtain ⟨hL, hcanT⟩ := erased_core_maximal h hT hpT ho htE
    have hneKL : H.erase p ≠ T.erase p := by
      intro he
      have hiH := insert_erase hpH
      have hiT := insert_erase hpT
      rw [he] at hiH
      have heq := hiH.symm.trans hiT
      exact hnot (heq ▸ Subset.rfl)
    have hz := core_point_traces_disjoint h hK hL hneKL (hHA hpH)
      (notMem_erase _ _) (notMem_erase _ _)
    rw [← hplus, ← hcanT] at hz
    have hfull := outside_trace_full (G := G) (C := C) (Y := corePlus G C H) (T := T)
      (p := p) (by omega)
    refine ⟨(core_loss_bound h hL).2.trans (by norm_num), ?_⟩
    intro c hc hadj
    have hcT := hfull c hc hadj
    rw [hcanT] at hcT
    exact (mem_cpr.mp hcT).2
  · have hd3 : dg G (cpr G C T) p = 3 := by omega
    obtain ⟨hQ, htQ⟩ := erased_private_high h hH hpH hp5 ho hT hpT hnot hd3
    have hdis : Disjoint (H.erase p) T := by
      apply disjoint_left.mpr
      intro a haK haT
      have haH := (mem_erase.mp haK).2
      have haI : a ∈ H ∩ T := mem_inter.mpr ⟨haH, haT⟩
      rw [hi] at haI
      exact (mem_erase.mp haK).1 (mem_singleton.mp haI)
    have hshadow := disjoint_core_shadow h hK hT htT hdis
    have htrace := shadow_trace_bound hshadow hpT hdK
    rw [← hplus] at htrace
    have houtside : dg G (cpr G C T \ corePlus G C H) p = 2 := by
      have hm := dg_mono (G := G)
        (sdiff_subset_sdiff_left (corePlus G C H) (cpr_subset (G := G) C T)) p
      omega
    have hinside : dg G (corePlus G C H ∩ cpr G C T) p = 1 := by omega
    obtain ⟨c0, hc0⟩ := card_pos.mp (show 0 < dg G (corePlus G C H ∩ cpr G C T) p by omega)
    obtain ⟨hc0I, hadj0⟩ := mem_filter.mp hc0
    obtain ⟨hc0K, hc0T⟩ := mem_inter.mp hc0I
    rw [hplus] at hc0K
    have hc0C := (mem_cpr.mp hc0K).1
    have hK3 := (mem_cpr.mp hc0K).2
    have hT3 := (mem_cpr.mp hc0T).2
    have hdUnion := dg_union_of_disjoint (G := G) hdis c0
    have hcap := dg_mono (G := G) (union_subset ((erase_subset p H).trans hHA) hTA) c0
    rw [h.satC c0 hc0C] at hcap
    have hdErase := dg_erase_add (G := G) hpT c0 (G.adj_symm hadj0)
    have hQ2 : dg G (T.erase p) c0 = 2 := by omega
    have hQloss := count_two_loss h ((erase_subset p T).trans hTA) htQ hpositive hc0C hQ2
    have hfull := outside_trace_full (G := G) (C := C) (Y := corePlus G C H) (T := T)
      (p := p) (by omega)
    refine ⟨hQloss.1, ?_⟩
    intro c hc hadj
    have hcT := hfull c hc hadj
    have h3 := (mem_cpr.mp hcT).2
    have hdEr := dg_erase_add (G := G) hpT c (G.adj_symm hadj)
    have hne0 : c ≠ c0 := by
      intro he
      have hcK : c0 ∈ corePlus G C H := hplus.symm ▸ hc0K
      exact (mem_sdiff.mp hc).2 (he.symm ▸ hcK)
    have hno2 := hQloss.2 c (mem_sdiff.mp hc).1 hne0
    omega

lemma two_outside_members_equal {A C H T U : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) {p : V} (hpH : p ∈ H)
    (hp5 : dg G C p = 5) (ho : Ordinary G A C p)
    (hout : dg G (C \ corePlus G C H) p = 2)
    (hT : T ∈ maxPositiveFamily G A C) (hpT : p ∈ T) (hnotT : ¬ H ⊆ T)
    (hU : U ∈ maxPositiveFamily G A C) (hpU : p ∈ U) (hnotU : ¬ H ⊆ U)
    (hdT : 0 < df G C (T.erase p)) (hdU : 0 < df G C (U.erase p)) : T = U := by
  by_contra hne
  have hi := private_members_meet h hH hpH hp5 ho hT hpT hnotT hU hpU hnotU hne
  have hboundT := (two_outside_private_bound h hH hpH hp5 ho hout hT hpT hnotT hdT).2
  have hboundU := (two_outside_private_bound h hH hpH hp5 ho hout hU hpU hnotU hdU).2
  obtain ⟨c, hc⟩ := card_pos.mp (show 0 < dg G (C \ corePlus G C H) p by omega)
  obtain ⟨hcOut, hadj⟩ := mem_filter.mp hc
  have hcC := (mem_sdiff.mp hcOut).1
  have hT3 := hboundT c hcOut hadj
  have hU3 := hboundU c hcOut hadj
  have heT := dg_erase_add (G := G) hpT c (G.adj_symm hadj)
  have heU := dg_erase_add (G := G) hpU c (G.adj_symm hadj)
  have hdu := dg_union_add_dg_inter (G := G) T U c
  have hcap := dg_mono (G := G)
    (union_subset (maxPositive_data h hT).1 (maxPositive_data h hU).1) c
  have hs : dg G ({p} : Finset V) c = 1 := by
    simp only [dg, filter_singleton, if_pos (G.adj_symm hadj), card_singleton]
  rw [hi, hs] at hdu
  rw [h.satC c hcC] at hcap
  omega

lemma ordinary_high_two_outside_impossible {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hapf : APF G A C) (hH : H ∈ maxHighFamily G A C)
    {p : V} (hpH : p ∈ H) (hp5 : dg G C p = 5) (ho : Ordinary G A C p)
    (hout : dg G (C \ corePlus G C H) p = 2) : False := by
  have htH := ordinary_high_theta h hH hpH ho
  have hdH := ordinary_high_positive_deficit h hH hpH hp5
  have hshape := ordinary_high_two_shape h hH hpH hp5 ho hout
  have hW := (minfive_private_deficit h hm hH htH hdH).2 hshape.2.2.2.1 hshape.2.2.2.2.2
  obtain ⟨r, hr, hr5⟩ := minfive_private_row h hm hH htH hdH
  obtain ⟨T, hT, hpT, hrT, hnotT⟩ := private_apf_member h hapf hH hpH hr
  have hpr : r ≠ p := by intro he; exact (private_not_H hr).2 (he ▸ hpH)
  have hdT := degree_five_deficit_pos h ((erase_subset p T).trans (maxPositive_data h hT).1)
    (mem_erase.mpr ⟨hpr, hrT⟩) hr5
  have hcover : ∀ s ∈ privateRows G A C H, dg G C s = 5 → s ∈ T := by
    intro s hs hs5
    obtain ⟨U, hU, hpU, hsU, hnotU⟩ := private_apf_member h hapf hH hpH hs
    have hsp : s ≠ p := by intro he; exact (private_not_H hs).2 (he ▸ hpH)
    have hdU := degree_five_deficit_pos h ((erase_subset p U).trans (maxPositive_data h hU).1)
      (mem_erase.mpr ⟨hsp, hsU⟩) hs5
    exact (two_outside_members_equal h hH hpH hp5 ho hout hT hpT hnotT hU hpU hnotU hdT hdU) ▸ hsU
  have hbound := private_deficit_le_member h hm (maxPositive_data h hT).1 hpH hcover
  have hT2 := (two_outside_private_bound h hH hpH hp5 ho hout hT hpT hnotT hdT).1
  omega

lemma ordinary_inside_high_impossible {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hapf : APF G A C) (hH : H ∈ maxHighFamily G A C)
    {p : V} (hpH : p ∈ H) (hp5 : dg G C p = 5) (ho : Ordinary G A C p) : False := by
  have hout := ordinary_high_outgoing h hm hapf hH hpH hp5 ho
  by_cases h1 : dg G (C \ corePlus G C H) p = 1
  · exact ordinary_high_one_outside_impossible h hm hapf hH hpH hp5 ho h1
  · exact ordinary_high_two_outside_impossible h hm hapf hH hpH hp5 ho (by omega)

lemma outside_high_point_theta {A C : Finset V} (h : C02Input G A C)
    {p : V} (hno : ∀ H ∈ maxHighFamily G A C, p ∉ H)
    {T : Finset V} (hT : T ∈ pointFamily G A C p) : thetaC02 G C T = 1 := by
  have hTF := (mem_pointFamily.mp hT).1
  have hpT := (mem_pointFamily.mp hT).2
  obtain ⟨hTA, h3T, htpos, _⟩ := maxPositive_data h hTF
  by_contra hh
  obtain ⟨H, hH, hTH⟩ := high_extension (G := G) (C := C) hTA h3T (by omega)
  exact hno H hH (hTH hpT)

lemma outside_high_point_meet {A C : Finset V} (h : C02Input G A C)
    {p : V} (hno : ∀ H ∈ maxHighFamily G A C, p ∉ H)
    {T U : Finset V} (hT : T ∈ pointFamily G A C p)
    (hU : U ∈ pointFamily G A C p) (hne : T ≠ U) : T ∩ U = {p} := by
  have hTF := (mem_pointFamily.mp hT).1
  have hUF := (mem_pointFamily.mp hU).1
  have hpI := mem_inter.mpr ⟨(mem_pointFamily.mp hT).2, (mem_pointFamily.mp hU).2⟩
  obtain ⟨hTA, _, _, hmT⟩ := maxPositive_data h hTF
  obtain ⟨hUA, _, _, _⟩ := maxPositive_data h hUF
  have htT := outside_high_point_theta h hno hT
  have htU := outside_high_point_theta h hno hU
  have hUn : T ∪ U ≠ T := by
    intro he
    exact hne ((mem_maximalMembers.mp hUF).2 T (mem_maximalMembers.mp hTF).1 (he ▸ subset_union_right))
  have hUb := hmT (T ∪ U) (union_subset hTA hUA) subset_union_left hUn
  have hs := theta_supermodular (G := G) C T U
  have hIlt : #(T ∩ U) < 2 := by
    by_contra hh
    by_cases h3 : 3 ≤ #(T ∩ U)
    · obtain ⟨H, hH, hIH⟩ := high_extension (G := G) (C := C)
        (inter_subset_left.trans hTA) h3 (by omega)
      exact hno H hH (hIH hpI)
    · have hb := theta_small (G := G) C (Z := T ∩ U) (by omega)
      omega
  obtain ⟨a, ha⟩ := card_eq_one.mp (show #(T ∩ U) = 1 by
    have hc := card_pos.mpr ⟨p, hpI⟩; omega)
  have he : p = a := mem_singleton.mp (ha ▸ hpI)
  simpa [he] using ha

lemma outside_high_petals {A C : Finset V} (h : C02Input G A C)
    {p : V} (hno : ∀ H ∈ maxHighFamily G A C, p ∉ H) :
    (pointFamily G A C p : Set (Finset V)).Pairwise
      (fun T U => Disjoint (T.erase p) (U.erase p)) := by
  intro T hT U hU hne
  have hi := outside_high_point_meet h hno hT hU hne
  apply disjoint_left.mpr
  intro a haT haU
  have haI : a ∈ T ∩ U := mem_inter.mpr ⟨(mem_erase.mp haT).2, (mem_erase.mp haU).2⟩
  rw [hi] at haI
  exact (mem_erase.mp haT).1 (mem_singleton.mp haI)

lemma outside_high_deficit_sum {A C : Finset V} (h : C02Input G A C)
    (hapf : APF G A C) {p : V} (hpA : p ∈ A) (hp5 : dg G C p = 5)
    (hno : ∀ H ∈ maxHighFamily G A C, p ∉ H) :
    (∑ T ∈ pointFamily G A C p, df G C (T.erase p)) = 11 := by
  have hs := sum_biUnion (f := fun a => (6 : ℤ) - (dg G C a : ℤ))
    (outside_high_petals h hno)
  rw [point_cover h hapf hpA] at hs
  have he := sum_erase_add A (fun a => (6 : ℤ) - (dg G C a : ℤ)) hpA
  change df G C (A.erase p) + _ = df G C A at he
  rw [hp5, c02_total_deficit h] at he
  change df G C (A.erase p) = ∑ T ∈ pointFamily G A C p, df G C (T.erase p) at hs
  omega

lemma outside_high_point_bounds {A C : Finset V} (h : C02Input G A C)
    {p : V} (hp5 : dg G C p = 5) (hno : ∀ H ∈ maxHighFamily G A C, p ∉ H)
    {T : Finset V} (hT : T ∈ pointFamily G A C p) :
    2 ≤ dg G (cpr G C T) p ∧ dg G (cpr G C T) p ≤ 5 ∧
      df G C (T.erase p) ≤ (dg G (cpr G C T) p : ℤ) + 1 ∧
      df G C (T.erase p) ≤ 3 * (dg G (cpr G C T) p : ℤ) - 5 := by
  have hTF := (mem_pointFamily.mp hT).1
  have hpT := (mem_pointFamily.mp hT).2
  have ht := outside_high_point_theta h hno hT
  obtain ⟨hTA, h3T, _, _⟩ := maxPositive_data h hTF
  have her := theta_erase (G := G) (C := C) hpT
  have h2E : 2 ≤ #(T.erase p) := by have hc := card_erase_add_one hpT; omega
  have hEb := theta_order_two_le_three h ((erase_subset p T).trans hTA) h2E
  have hmono := dg_mono (G := G) (cpr_subset (G := G) C T) p
  have hne : T ≠ A := by intro he; rw [he, theta_whole h] at ht; omega
  have hproper := theta_proper_bounds h hTA hne h3T
  have hcEr := card_erase_add_one hpT
  have hpId := (point_identities h hTF ht hpT).1
  have ho0 : (0 : ℤ) ≤ ec G (T.erase p) (C \ cpr G C T) := by positivity
  exact ⟨by omega, by omega, by omega, point_charge h hTF ht hpT⟩

lemma outside_high_pair_sum {A C : Finset V} (h : C02Input G A C)
    {p : V} (hp5 : dg G C p = 5) (hno : ∀ H ∈ maxHighFamily G A C, p ∉ H)
    {T U : Finset V} (hT : T ∈ pointFamily G A C p)
    (hU : U ∈ pointFamily G A C p) (hne : T ≠ U) :
    dg G (cpr G C T) p + dg G (cpr G C U) p ≤ 7 := by
  have hgap := positive_singleton_gap_budget h (mem_pointFamily.mp hT).1 (mem_pointFamily.mp hU).1 hne
    (outside_high_point_theta h hno hT) (outside_high_point_theta h hno hU)
    (outside_high_point_meet h hno hT hU hne)
  have hd := dg_union_add_dg_inter (G := G) (cpr G C T) (cpr G C U) p
  have hm := dg_mono (G := G) (union_subset (cpr_subset (G := G) C T) (cpr_subset (G := G) C U)) p
  omega

lemma outside_high_incidence {A C : Finset V} (h : C02Input G A C)
    {p : V} (hpA : p ∈ A) (hp5 : dg G C p = 5)
    (hno : ∀ H ∈ maxHighFamily G A C, p ∉ H) :
    (∑ T ∈ pointFamily G A C p, dg G (cpr G C T) p) ≤ 10 := by
  rw [Erdos585.QB6C02PointIncidence.canonical_incidence_double_count]
  have hb : ∀ c ∈ C.filter (fun c => G.Adj p c),
      #(pointFamily G A C p |>.filter fun T => c ∈ cpr G C T) ≤ 2 := by
    intro c hc
    exact Erdos585.QB6C02PointIncidence.canonical_members_at_neighbor_le_two h hpA
      (pointFamily G A C p) (fun T hT => (maxPositive_data h (mem_pointFamily.mp hT).1).1)
      (fun T hT => (mem_pointFamily.mp hT).2)
      (fun T hT U hU hne => outside_high_point_meet h hno hT hU hne)
      (mem_filter.mp hc).1 (mem_filter.mp hc).2
  have hs := sum_le_sum hb
  have hN : #(C.filter fun c => G.Adj p c) = 5 := hp5
  simpa only [sum_const, smul_eq_mul, hN] using hs

lemma outside_high_no_full_trace {A C : Finset V} (h : C02Input G A C)
    (hapf : APF G A C) {p : V} (hpA : p ∈ A) (hp5 : dg G C p = 5)
    (hno : ∀ H ∈ maxHighFamily G A C, p ∉ H) :
    ∀ T ∈ pointFamily G A C p, dg G (cpr G C T) p ≤ 4 := by
  classical
  let F := pointFamily G A C p
  have hsumD := outside_high_deficit_sum h hapf hpA hp5 hno
  have hsumA := outside_high_incidence h hpA hp5 hno
  intro T hT
  by_contra hh
  have hBT := outside_high_point_bounds h hp5 hno hT
  have haT : dg G (cpr G C T) p = 5 := by omega
  have haOther : ∀ U ∈ F.erase T, dg G (cpr G C U) p = 2 := by
    intro U hU
    have hUF := (mem_erase.mp hU).2
    have hne := (mem_erase.mp hU).1
    have hpair := outside_high_pair_sum h hp5 hno hUF hT hne
    have hBU := outside_high_point_bounds h hp5 hno hUF
    omega
  have hsA := sum_erase_add F (fun U => dg G (cpr G C U) p) hT
  have hsumOtherA : (∑ U ∈ F.erase T, dg G (cpr G C U) p) = 2 * #(F.erase T) := by
    rw [sum_congr rfl haOther, sum_const]
    simp only [smul_eq_mul, mul_comm]
  have hcard : #(F.erase T) ≤ 2 := by
    change (∑ U ∈ F, dg G (cpr G C U) p) ≤ 10 at hsumA
    omega
  have hsD := sum_erase_add F (fun U => df G C (U.erase p)) hT
  have hDOther : (∑ U ∈ F.erase T, df G C (U.erase p)) ≤ #(F.erase T) := by
    have hb : ∀ U ∈ F.erase T, df G C (U.erase p) ≤ (1 : ℤ) := by
      intro U hU
      have hBU := outside_high_point_bounds h hp5 hno (mem_erase.mp hU).2
      have ha := haOther U hU
      omega
    simpa only [sum_const, nsmul_eq_mul, mul_one] using sum_le_sum hb
  change (∑ U ∈ F, df G C (U.erase p)) = 11 at hsumD
  omega

lemma actual_column_outside_charge {A C : Finset V} (h : C02Input G A C)
    {p : V} (hpA : p ∈ A) (F : Finset (Finset V))
    (hsub : ∀ T ∈ F, T ⊆ A) (hpoint : ∀ T ∈ F, p ∈ T)
    (hmeet : ∀ T ∈ F, ∀ U ∈ F, T ≠ U → T ∩ U = {p})
    {c : V} (hc : c ∈ C) (hadj : G.Adj p c) :
    2 * ((#(F.filter fun T => c ∈ cpr G C T) : ℤ) - 1) ≤
      ∑ T ∈ F, if c ∈ cpr G C (T.erase p) then (0 : ℤ) else (dg G (T.erase p) c : ℤ) := by
  classical
  let J := F.filter fun T => c ∈ cpr G C T
  have hJF : ∀ T ∈ J, T ∈ F := fun T hT => (mem_filter.mp hT).1
  have hJtwo : #J ≤ 2 :=
    Erdos585.QB6C02PointIncidence.canonical_members_at_neighbor_le_two h hpA F hsub hpoint hmeet hc hadj
  have hnon : ∀ T ∈ F, (0 : ℤ) ≤
      if c ∈ cpr G C (T.erase p) then (0 : ℤ) else (dg G (T.erase p) c : ℤ) := by
    intro T _
    split_ifs <;> omega
  have hs0 := sum_nonneg hnon
  by_cases hJsmall : #J ≤ 1
  · change 2 * ((#J : ℤ) - 1) ≤ _
    omega
  · have hJ2 : #J = 2 := by omega
    obtain ⟨T, U, hne, hJU⟩ := card_eq_two.mp hJ2
    have hTJ : T ∈ J := hJU.symm ▸ mem_insert_self _ _
    have hUJ : U ∈ J := hJU.symm ▸ mem_insert_of_mem (mem_singleton_self U)
    have hTF := hJF T hTJ
    have hUF := hJF U hUJ
    have hT3 := (mem_cpr.mp (mem_filter.mp hTJ).2).2
    have hU3 := (mem_cpr.mp (mem_filter.mp hUJ).2).2
    have heT := dg_erase_add (G := G) (hpoint T hTF) c (G.adj_symm hadj)
    have heU := dg_erase_add (G := G) (hpoint U hUF) c (G.adj_symm hadj)
    have hsumJ := Erdos585.QB6C02PointIncidence.erased_neighbor_sum_le_five h hpA J
      (fun T hT => hsub T (hJF T hT))
      (fun T hT U hU hTU => hmeet T (hJF T hT) U (hJF U hU) hTU) hc hadj
    rw [hJU, sum_pair hne] at hsumJ
    have htwo : dg G (T.erase p) c = 2 ∨ dg G (U.erase p) c = 2 := by omega
    have hpaid : ∀ W ∈ F, dg G (W.erase p) c = 2 →
        (2 : ℤ) ≤ ∑ T ∈ F,
          if c ∈ cpr G C (T.erase p) then (0 : ℤ) else (dg G (T.erase p) c : ℤ) := by
      intro W hW hdW
      have hn : c ∉ cpr G C (W.erase p) := by
        intro hh
        have h3 := (mem_cpr.mp hh).2
        omega
      have hs := single_le_sum hnon hW
      rw [if_neg hn, hdW] at hs
      norm_num at hs
      exact hs
    have hbound := htwo.elim (hpaid T hTF) (hpaid U hUF)
    change 2 * ((#J : ℤ) - 1) ≤ _
    omega

lemma outside_count_sum (C T : Finset V) {p : V} :
    (∑ c ∈ C, if c ∈ cpr G C (T.erase p) then (0 : ℤ) else (dg G (T.erase p) c : ℤ)) =
      ec G (T.erase p) (C \ cpr G C (T.erase p)) := by
  have hsub := cpr_subset (G := G) C (T.erase p)
  have hs := sum_sdiff hsub (f := fun c =>
    if c ∈ cpr G C (T.erase p) then (0 : ℤ) else (dg G (T.erase p) c : ℤ))
  have hz : (∑ c ∈ cpr G C (T.erase p),
      if c ∈ cpr G C (T.erase p) then (0 : ℤ) else (dg G (T.erase p) c : ℤ)) = 0 := by
    exact sum_eq_zero fun c hc => if_pos hc
  have hout : (∑ c ∈ C \ cpr G C (T.erase p),
      if c ∈ cpr G C (T.erase p) then (0 : ℤ) else (dg G (T.erase p) c : ℤ)) =
      ∑ c ∈ C \ cpr G C (T.erase p), (dg G (T.erase p) c : ℤ) := by
    exact sum_congr rfl fun c hc => if_neg (mem_sdiff.mp hc).2
  rw [hz, hout, add_zero] at hs
  rw [ec_comm]
  simp only [ec, Nat.cast_sum]
  exact hs.symm

lemma actual_outside_incidence_charge {A C : Finset V} (h : C02Input G A C)
    {p : V} (hpA : p ∈ A) (hp5 : dg G C p = 5) (F : Finset (Finset V))
    (hsub : ∀ T ∈ F, T ⊆ A) (hpoint : ∀ T ∈ F, p ∈ T)
    (hmeet : ∀ T ∈ F, ∀ U ∈ F, T ≠ U → T ∩ U = {p}) :
    2 * ((∑ T ∈ F, (dg G (cpr G C T) p : ℤ)) - 5) ≤
      ∑ T ∈ F, (ec G (T.erase p) (C \ cpr G C (T.erase p)) : ℤ) := by
  let N := C.filter fun c => G.Adj p c
  have hNsub : N ⊆ C := filter_subset _ _
  have hpointwise : ∀ c ∈ N,
      2 * ((#(F.filter fun T => c ∈ cpr G C T) : ℤ) - 1) ≤
        ∑ T ∈ F, if c ∈ cpr G C (T.erase p) then (0 : ℤ) else (dg G (T.erase p) c : ℤ) := by
    intro c hc
    exact actual_column_outside_charge h hpA F hsub hpoint hmeet (mem_filter.mp hc).1 (mem_filter.mp hc).2
  have hs := sum_le_sum hpointwise
  rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one] at hs
  have hdouble : (∑ c ∈ N, (#(F.filter fun T => c ∈ cpr G C T) : ℤ)) =
      ∑ T ∈ F, (dg G (cpr G C T) p : ℤ) := by
    exact_mod_cast (Erdos585.QB6C02PointIncidence.canonical_incidence_double_count (G := G) C p F).symm
  have hN5 : (#N : ℤ) = 5 := by exact_mod_cast hp5
  rw [hdouble, hN5] at hs
  have hbound : (∑ c ∈ N, ∑ T ∈ F,
      if c ∈ cpr G C (T.erase p) then (0 : ℤ) else (dg G (T.erase p) c : ℤ)) ≤
      ∑ T ∈ F, (ec G (T.erase p) (C \ cpr G C (T.erase p)) : ℤ) := by
    rw [sum_comm]
    apply sum_le_sum
    intro T _
    calc
      _ ≤ ∑ c ∈ C, if c ∈ cpr G C (T.erase p) then (0 : ℤ) else (dg G (T.erase p) c : ℤ) :=
        sum_le_sum_of_subset_of_nonneg hNsub (fun c _ _ => by split_ifs <;> omega)
      _ = _ := outside_count_sum (G := G) C T
  exact hs.trans hbound

lemma outside_high_deleted_loss {A C : Finset V} (h : C02Input G A C)
    (hapf : APF G A C) {p : V} (hpA : p ∈ A) (hp5 : dg G C p = 5)
    (hno : ∀ H ∈ maxHighFamily G A C, p ∉ H)
    {T : Finset V} (hT : T ∈ pointFamily G A C p) :
    df G C (T.erase p) + (ec G (T.erase p) (C \ cpr G C (T.erase p)) : ℤ) ≤
      3 * (dg G (cpr G C T) p : ℤ) - 5 := by
  have hTF := (mem_pointFamily.mp hT).1
  have hpT := (mem_pointFamily.mp hT).2
  have hTA := (maxPositive_data h hTF).1
  have hEA : T.erase p ⊆ A := (erase_subset p T).trans hTA
  have htT := outside_high_point_theta h hno hT
  have hbound := outside_high_point_bounds h hp5 hno hT
  have h4 := outside_high_no_full_trace h hapf hpA hp5 hno T hT
  have her := theta_erase (G := G) (C := C) hpT
  have htE : thetaC02 G C (T.erase p) = 5 - (dg G (cpr G C T) p : ℤ) := by omega
  have h3E : 3 ≤ #(T.erase p) := by
    by_contra hh
    have hb := theta_small (G := G) C (Z := T.erase p) (by omega)
    omega
  have hneE : T.erase p ≠ A := by intro he; exact (notMem_erase p T) (he.symm ▸ hpA)
  have hloss := theta_loss_bound h hEA hneE h3E
  have hsplit := df_eq_df_add_ec (G := G) (cpr_subset (G := G) C (T.erase p)) (T.erase p)
  omega

lemma outside_high_impossible {A C : Finset V} (h : C02Input G A C)
    (hapf : APF G A C) {p : V} (hpA : p ∈ A) (hp5 : dg G C p = 5)
    (hno : ∀ H ∈ maxHighFamily G A C, p ∉ H) : False := by
  let F := pointFamily G A C p
  have hdef := outside_high_deficit_sum h hapf hpA hp5 hno
  have hcard := point_family_two h hapf hpA
  have hinc := outside_high_incidence h hpA hp5 hno
  have hincZ : (∑ T ∈ F, (dg G (cpr G C T) p : ℤ)) ≤ 10 := by exact_mod_cast hinc
  have hcharge := actual_outside_incidence_charge h hpA hp5 F
    (fun T hT => (maxPositive_data h (mem_pointFamily.mp hT).1).1)
    (fun T hT => (mem_pointFamily.mp hT).2)
    (fun T hT U hU hne => outside_high_point_meet h hno hT hU hne)
  have hloss := sum_le_sum (fun T hT => outside_high_deleted_loss h hapf hpA hp5 hno hT)
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at hloss
  change (∑ T ∈ F, df G C (T.erase p)) = 11 at hdef
  change 2 ≤ #F at hcard
  change (∑ T ∈ F, df G C (T.erase p)) +
      (∑ T ∈ F, (ec G (T.erase p) (C \ cpr G C (T.erase p)) : ℤ)) ≤
      3 * (∑ T ∈ F, (dg G (cpr G C T) p : ℤ)) - (#F : ℤ) * 5 at hloss
  omega

/-- Literal original C02 graph endpoint, with APF produced internally only. -/
theorem ordinary5_good_pair (G : SimpleGraph V) [DecidableRel G.Adj] (A C : Finset V)
    (h : C02Input G A C) (hm : MinFive G A C)
    (hp : ∃ p ∈ A, dg G C p = 5 ∧ Ordinary G A C p) :
    ∃ D, GoodPair G A C D := by
  obtain ⟨p, hpA, hp5, ho⟩ := hp
  by_contra hn
  have hapf : APF G A C := apf_of_no_good_pair h fun D _ _ hgood => hn ⟨D, hgood⟩
  by_cases hhigh : ∃ H ∈ maxHighFamily G A C, p ∈ H
  · obtain ⟨H, hH, hpH⟩ := hhigh
    exact ordinary_inside_high_impossible h hm hapf hH hpH hp5 ho
  · have hno : ∀ H ∈ maxHighFamily G A C, p ∉ H := by
      intro H hH hpH
      exact hhigh ⟨H, hH, hpH⟩
    exact outside_high_impossible h hapf hpA hp5 hno

/-- The omission pair is extracted as an actual nonempty four-regular subgraph. -/
theorem ordinary5_repair (G : SimpleGraph V) [DecidableRel G.Adj] (A C : Finset V)
    (h : C02Input G A C) (hm : MinFive G A C)
    (hp : ∃ p ∈ A, dg G C p = 5 ∧ Ordinary G A C p) : Quartic G A C := by
  obtain ⟨D, hD⟩ := ordinary5_good_pair G A C h hm hp
  exact goodPair_quartic h hD

end Erdos585.QB6C02OrdinaryFive
