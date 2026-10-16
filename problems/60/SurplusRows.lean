import HighSurplus
import DegreeDeficiency
import DeficientNeighborParity
import OverlapBound

namespace Erdos60.SurplusRows
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def deficientVertices (G : SimpleGraph V) (q : ℕ) : Finset V :=
  Finset.univ.filter fun x => 0 < Statistics.degreeDeficiency G q x

omit [DecidableEq V] in
 theorem surplus_eq_high_sum (G : SimpleGraph V) (q : ℕ) :
    Statistics.totalSurplus G q =
      ∑ x ∈ HighSurplus.highVertices G q, Statistics.degreeSurplus G q x := by
  classical
  unfold Statistics.totalSurplus HighSurplus.highVertices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hd : q+2 ≤ G.degree x
  · simp [hd]
  · simp only [hd,ite_false]
    unfold Statistics.degreeSurplus
    omega

omit [DecidableEq V] in
 theorem high_card_le_surplus (G : SimpleGraph V) (q : ℕ) :
    (HighSurplus.highVertices G q).card ≤ Statistics.totalSurplus G q := by
  rw [surplus_eq_high_sum]
  have hs : (∑ x ∈ HighSurplus.highVertices G q, (1 : ℕ)) ≤
      ∑ x ∈ HighSurplus.highVertices G q, Statistics.degreeSurplus G q x := by
    apply Finset.sum_le_sum
    intro x hx
    have hd := (Finset.mem_filter.mp hx).2
    unfold Statistics.degreeSurplus
    omega
  simpa using hs

omit [DecidableEq V] in
 theorem deficiency_eq_deficient_sum (G : SimpleGraph V) (q : ℕ) :
    Statistics.totalDeficiency G q =
      ∑ x ∈ deficientVertices G q, Statistics.degreeDeficiency G q x := by
  classical
  unfold Statistics.totalDeficiency deficientVertices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs with h <;> omega

omit [DecidableEq V] in
 theorem deficient_card_le_total (G : SimpleGraph V) (q : ℕ) :
    (deficientVertices G q).card ≤ Statistics.totalDeficiency G q := by
  rw [deficiency_eq_deficient_sum]
  have hs : (∑ x ∈ deficientVertices G q, (1 : ℕ)) ≤
      ∑ x ∈ deficientVertices G q, Statistics.degreeDeficiency G q x := by
    apply Finset.sum_le_sum
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  simpa using hs

/-- Summing every actual high row, before controlling their deficient neighbors. -/
theorem all_high_rows (G : SimpleGraph V) (q : ℕ)
    (hN : Fintype.card V = q^2+q+1) :
    (q : ℝ)*Statistics.totalSurplus G q ≤
      4*(Counting.cycleCount G : ℝ) +
        ∑ x ∈ HighSurplus.highVertices G q,
          (Statistics.deficiencyOn G q (G.neighborFinset x) : ℝ) := by
  classical
  have hpoint (x : V) (hx : x ∈ HighSurplus.highVertices G q) :
      (q : ℝ)*Statistics.degreeSurplus G q x ≤
        (Statistics.vertexCycleStatistic G x : ℝ) +
          Statistics.deficiencyOn G q (G.neighborFinset x) := by
    have hd := (Finset.mem_filter.mp hx).2
    have hd' : q+1 ≤ G.degree x := by omega
    have hr : (Statistics.degreeSurplus G q x : ℝ) = (G.degree x : ℝ)-q-1 := by
      unfold Statistics.degreeSurplus
      rw [Nat.cast_sub hd']
      push_cast
      ring
    rw [hr]
    have hb := Statistics.vertex_cycle_deficiency_lower G q hN x
    have hz : (0 : ℝ) ≤ Statistics.zeroCodegreeCount G x := Nat.cast_nonneg _
    nlinarith
  have hs := Finset.sum_le_sum hpoint
  have hsur : (∑ x ∈ HighSurplus.highVertices G q, (Statistics.degreeSurplus G q x : ℝ)) =
      Statistics.totalSurplus G q := by
    exact_mod_cast (surplus_eq_high_sum G q).symm
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  rw [hsur] at hs
  have hc := HighSurplus.restricted_cycle_sum G (HighSurplus.highVertices G q)
  have hcr : (∑ x ∈ HighSurplus.highVertices G q, (Statistics.vertexCycleStatistic G x : ℝ)) ≤
      4*(Counting.cycleCount G : ℝ) := by exact_mod_cast hc
  linarith

 theorem neighbor_inter_card (G : SimpleGraph V) (x : V) (A : Finset V) :
    (G.neighborFinset x ∩ A).card = ∑ a ∈ A, if G.Adj x a then 1 else 0 := by
  classical
  rw [Finset.sum_boole]
  simp only [Nat.cast_id]
  congr 1
  ext a
  simp [and_comm]

 theorem neighbor_incidence_symm (G : SimpleGraph V) (A B : Finset V) :
    (∑ x ∈ A, (G.neighborFinset x ∩ B).card) =
      ∑ y ∈ B, (G.neighborFinset y ∩ A).card := by
  simp_rw [neighbor_inter_card]
  rw [Finset.sum_comm]
  simp_rw [SimpleGraph.adj_comm]

omit [DecidableEq V] in
 theorem deficient_degree_bound (G : SimpleGraph V) (q : ℕ) {x : V}
    (hx : x ∈ deficientVertices G q) : G.degree x ≤ q := by
  have hf := (Finset.mem_filter.mp hx).2
  unfold Statistics.degreeDeficiency at hf
  omega

 theorem deficient_neighbor_sum (G : SimpleGraph V) (q : ℕ) :
    (∑ x : V, (G.neighborFinset x ∩ deficientVertices G q).card) ≤
      q*(deficientVertices G q).card := by
  rw [neighbor_incidence_symm]
  simp only [Finset.inter_univ,G.card_neighborFinset_eq_degree]
  calc
    _ ≤ ∑ x ∈ deficientVertices G q, q :=
      Finset.sum_le_sum (fun x hx => deficient_degree_bound G q hx)
    _ = _ := by simp [Nat.mul_comm]

 theorem vertex_classification_budget (G : SimpleGraph V) (q : ℕ)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1) :
    Fintype.card V ≤ (HighSurplus.highVertices G q).card +
      (q+1)*(deficientVertices G q).card + 4*Counting.cycleCount G := by
  classical
  have hpoint (x : V) : (1 : ℕ) ≤
      (if x ∈ HighSurplus.highVertices G q then 1 else 0) +
      (if x ∈ deficientVertices G q then 1 else 0) +
      (G.neighborFinset x ∩ deficientVertices G q).card +
      Statistics.vertexCycleStatistic G x := by
    by_cases hh : x ∈ HighSurplus.highVertices G q
    · simp only [hh,ite_true]; omega
    by_cases hs : x ∈ deficientVertices G q
    · simp only [hs,ite_true]; omega
    simp only [hh,hs,ite_false,zero_add]
    by_cases hn : 0 < (G.neighborFinset x ∩ deficientVertices G q).card
    · omega
    have hx : q+1 ≤ G.degree x := by
      have hf : ¬0 < Statistics.degreeDeficiency G q x := by
        simpa [deficientVertices] using hs
      unfold Statistics.degreeDeficiency at hf
      omega
    have hneighbor : ∀ a, G.Adj x a → q+1 ≤ G.degree a := by
      intro a ha
      by_contra hd
      have had : a ∈ deficientVertices G q := by
        simp only [deficientVertices,Finset.mem_filter,Finset.mem_univ,true_and]
        unfold Statistics.degreeDeficiency
        omega
      have ham : a ∈ G.neighborFinset x ∩ deficientVertices G q := by simp [ha,had]
      have hp := Finset.card_pos.mpr ⟨a,ham⟩
      omega
    have hc := Statistics.cycle_statistic_pos_of_no_deficient_neighbor G q heven hN x hx hneighbor
    omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hpoint x)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Nat.smul_one_eq_cast,
    Finset.card_univ,Nat.cast_id,Finset.sum_boole] at hsum
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter] at hsum
  rw [Statistics.vertexCycleStatistic_sum_eq_four] at hsum
  have hn := deficient_neighbor_sum G q
  nlinarith

 theorem deficient_count_lower (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    (q : ℝ)-5*T ≤ (deficientVertices G q).card := by
  have hb := vertex_classification_budget G q heven hN
  rw [hN] at hb
  have hbr : (q : ℝ)^2+q+1 ≤ (HighSurplus.highVertices G q).card +
      ((q : ℝ)+1)*(deficientVertices G q).card + 4*(Counting.cycleCount G : ℝ) := by
    exact_mod_cast hb
  have hh := HighSurplus.high_count_small G q T hq hT hr hN hE hZ
  have hh' : ((HighSurplus.highVertices G q).card : ℝ) ≤ T*((q : ℝ)+1) := by
    exact (div_le_iff₀ (show (0 : ℝ) < (q : ℝ)+1 by linarith)).mp hh.2
  have hq0 : (0 : ℝ) < (q : ℝ)+1 := by linarith
  nlinarith

noncomputable def excessDeficiency (G : SimpleGraph V) (q : ℕ) : ℕ :=
  Statistics.totalDeficiency G q - (deficientVertices G q).card

 theorem deficiency_decompose (G : SimpleGraph V) (q : ℕ) (x : V) :
    Statistics.degreeDeficiency G q x =
      (if x ∈ deficientVertices G q then 1 else 0) +
        (Statistics.degreeDeficiency G q x-1) := by
  classical
  by_cases hx : x ∈ deficientVertices G q
  · have hp := (Finset.mem_filter.mp hx).2
    simp only [hx,ite_true]
    omega
  · have hz : Statistics.degreeDeficiency G q x = 0 := by
      have := hx
      simp only [deficientVertices,Finset.mem_filter,Finset.mem_univ,true_and] at this
      omega
    simp [hx,hz]

 theorem deficiencyOn_decompose (G : SimpleGraph V) (q : ℕ) (U : Finset V) :
    Statistics.deficiencyOn G q U = (U ∩ deficientVertices G q).card +
      ∑ x ∈ U, (Statistics.degreeDeficiency G q x-1) := by
  classical
  unfold Statistics.deficiencyOn
  have hs := Finset.sum_congr (s₁ := U) rfl (fun x _ => deficiency_decompose G q x)
  simp only [Finset.sum_add_distrib,Finset.sum_boole,Nat.cast_id] at hs
  have hi : U.filter (fun x => x ∈ deficientVertices G q) = U ∩ deficientVertices G q := by
    ext x
    simp
  rwa [hi] at hs

 theorem excessDeficiency_eq_sum (G : SimpleGraph V) (q : ℕ) :
    excessDeficiency G q = ∑ x : V, (Statistics.degreeDeficiency G q x-1) := by
  have hd := deficiencyOn_decompose G q (Finset.univ : Finset V)
  simp only [Finset.univ_inter] at hd
  change Statistics.totalDeficiency G q = (deficientVertices G q).card +
    (∑ x : V, (Statistics.degreeDeficiency G q x-1)) at hd
  unfold excessDeficiency
  omega

 theorem deficiencyOn_le_support_add_excess (G : SimpleGraph V) (q : ℕ) (U : Finset V) :
    Statistics.deficiencyOn G q U ≤ (U ∩ deficientVertices G q).card + excessDeficiency G q := by
  rw [deficiencyOn_decompose,excessDeficiency_eq_sum]
  exact Nat.add_le_add_left
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U) (fun x _ _ => Nat.zero_le _)) _

 theorem excessDeficiency_bound (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    (excessDeficiency G q : ℝ) ≤ Statistics.totalSurplus G q + 5*T := by
  have hs := deficient_count_lower G q T hq hT hr heven hN hE hZ
  have hq1 : 1 ≤ q := by
    have : (1 : ℝ) ≤ q := by linarith
    exact_mod_cast this
  have hb := Statistics.totalDeficiency_eq G q hq1 hN hE
  have hc := deficient_card_le_total G q
  have he : excessDeficiency G q + (deficientVertices G q).card = Statistics.totalDeficiency G q :=
    Nat.sub_add_cancel hc
  have her : (excessDeficiency G q : ℝ) + (deficientVertices G q).card = Statistics.totalDeficiency G q := by
    exact_mod_cast he
  have hbr : (Statistics.totalDeficiency G q : ℝ) = (q : ℝ)-1+Statistics.totalSurplus G q := by
    have hn : Statistics.totalDeficiency G q+1=q+Statistics.totalSurplus G q := by omega
    have hr : (Statistics.totalDeficiency G q : ℝ)+1=(q : ℝ)+Statistics.totalSurplus G q := by
      exact_mod_cast hn
    linarith
  linarith

 theorem subset_pair_codegree_grouping (G : SimpleGraph V) (U : Finset V) :
    (∑ p ∈ Statistics.subsetPairs U, Statistics.pairCodegree G p) =
      ∑ x : V, ((G.neighborFinset x ∩ U).card).choose 2 := by
  classical
  have hpair := Statistics.two_mul_subsetPairs_sum U (Statistics.pairCodegree G)
  have hoff : U.offDiag = (U ×ˢ U).filter (fun p : V × V => p.1 ≠ p.2) := by
    ext p
    simp [and_assoc]
  rw [hoff,Finset.sum_filter,Finset.sum_product] at hpair
  have hordered : (∑ p ∈ U, ∑ y ∈ U,
      if p ≠ y then Statistics.pairCodegree G (Sym2.mk.uncurry (p,y)) else 0) =
      ∑ x ∈ U, ∑ y ∈ U.erase x, Statistics.codegree G x y := by
    apply Finset.sum_congr rfl
    intro x hx
    have he : U.erase x = U.filter (fun y => x ≠ y) := by
      ext y
      simp [ne_comm,and_comm]
    rw [he,Finset.sum_filter]
    simp only [Function.uncurry_apply_pair,Statistics.pairCodegree_mk]
  rw [hordered,Statistics.subset_ordered_twoPath_count] at hpair
  have htwo : (∑ x : V, (G.neighborFinset x ∩ U).card *
      ((G.neighborFinset x ∩ U).card-1)) =
      2*∑ x : V, ((G.neighborFinset x ∩ U).card).choose 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => (Statistics.two_mul_choose_two _).symm)
  rw [htwo] at hpair
  omega

 theorem neighbor_union_bound (G : SimpleGraph V) (H S : Finset V) :
    (∑ x ∈ H, (G.neighborFinset x ∩ S).card) ≤ S.card +
      ∑ p ∈ Statistics.subsetPairs H, Statistics.pairCodegree G p := by
  rw [neighbor_incidence_symm,subset_pair_codegree_grouping]
  have hpoint (x : V) : (G.neighborFinset x ∩ H).card ≤
      1+((G.neighborFinset x ∩ H).card).choose 2 := by
    have hh := Statistics.choose_two_lower (G.neighborFinset x ∩ H).card
    omega
  have hs := Finset.sum_le_sum (s := S) (fun x _ => hpoint x)
  have hb : (∑ x ∈ S, ((G.neighborFinset x ∩ H).card).choose 2) ≤
      ∑ x : V, ((G.neighborFinset x ∩ H).card).choose 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun x _ _ => Nat.zero_le _)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Nat.smul_one_eq_cast,Nat.cast_id] at hs
  omega

 theorem all_high_rows_with_overlaps (G : SimpleGraph V) (q : ℕ)
    (hN : Fintype.card V = q^2+q+1) :
    (q : ℝ)*Statistics.totalSurplus G q ≤
      4*(Counting.cycleCount G : ℝ) + (deficientVertices G q).card +
        (∑ p ∈ Statistics.subsetPairs (HighSurplus.highVertices G q),
          Statistics.pairCodegree G p : ℕ) +
        (HighSurplus.highVertices G q).card*(excessDeficiency G q : ℝ) := by
  classical
  have hs : (∑ x ∈ HighSurplus.highVertices G q,
      Statistics.deficiencyOn G q (G.neighborFinset x)) ≤
      (∑ x ∈ HighSurplus.highVertices G q,
        (G.neighborFinset x ∩ deficientVertices G q).card) +
        (HighSurplus.highVertices G q).card*excessDeficiency G q := by
    have hh := Finset.sum_le_sum (s := HighSurplus.highVertices G q)
      (fun x _ => deficiencyOn_le_support_add_excess G q (G.neighborFinset x))
    simpa only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Nat.cast_id] using hh
  have hu := neighbor_union_bound G (HighSurplus.highVertices G q) (deficientVertices G q)
  have hn : (∑ x ∈ HighSurplus.highVertices G q,
      Statistics.deficiencyOn G q (G.neighborFinset x)) ≤
      (deficientVertices G q).card +
        (∑ p ∈ Statistics.subsetPairs (HighSurplus.highVertices G q), Statistics.pairCodegree G p) +
        (HighSurplus.highVertices G q).card*excessDeficiency G q := by omega
  have hr : (∑ x ∈ HighSurplus.highVertices G q,
      (Statistics.deficiencyOn G q (G.neighborFinset x) : ℝ)) ≤
      (deficientVertices G q).card +
        (∑ p ∈ Statistics.subsetPairs (HighSurplus.highVertices G q), Statistics.pairCodegree G p : ℕ) +
        (HighSurplus.highVertices G q).card*(excessDeficiency G q : ℝ) := by exact_mod_cast hn
  have hb := all_high_rows G q hN
  linarith

 theorem choose_overlap_sqrt_bound (h Z : ℕ) {q T : ℝ}
    (hTq : 0 ≤ T*q) (hZ : (Z : ℝ) ≤ T*q) :
    (h.choose 2 : ℝ)+2*Real.sqrt ((h.choose 2 : ℝ)*Z) ≤
      (h : ℝ)^2/2+Real.sqrt 2*h*Real.sqrt (T*q) := by
  have hK : (h.choose 2 : ℝ) ≤ (h : ℝ)^2/2 := by
    rw [Nat.cast_choose_two]
    nlinarith [Nat.cast_nonneg (α := ℝ) h]
  have hZ0 : (0 : ℝ) ≤ Z := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ h.choose 2 := Nat.cast_nonneg _
  have hm1 := mul_le_mul_of_nonneg_right hK hZ0
  have hm2 := mul_le_mul_of_nonneg_left hZ (show (0 : ℝ) ≤ (h : ℝ)^2/2 by positivity)
  have hprod : (h.choose 2 : ℝ)*Z ≤ (h : ℝ)^2/2*(T*q) := hm1.trans hm2
  have hleft := Real.sq_sqrt (mul_nonneg hK0 hZ0)
  have hleft0 := Real.sqrt_nonneg ((h.choose 2 : ℝ)*Z)
  have hright0 : 0 ≤ Real.sqrt 2*(h : ℝ)*Real.sqrt (T*q) := by positivity
  have hright : (Real.sqrt 2*(h : ℝ)*Real.sqrt (T*q))^2 = 2*(h : ℝ)^2*(T*q) := by
    calc
      _ = (Real.sqrt 2)^2*(h : ℝ)^2*(Real.sqrt (T*q))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),Real.sq_sqrt hTq]
  have hcross : 2*Real.sqrt ((h.choose 2 : ℝ)*Z) ≤
      Real.sqrt 2*(h : ℝ)*Real.sqrt (T*q) := by nlinarith
  linarith

/-- Source §4 equation (12), derived on the actual graph and fixed high set. -/
theorem all_high_scalar_bound (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    ((q : ℝ)-(HighSurplus.highVertices G q).card-1)*Statistics.totalSurplus G q ≤
      4*T*q+q+((HighSurplus.highVertices G q).card : ℝ)^2/2 +
        Real.sqrt 2*(HighSurplus.highVertices G q).card*Real.sqrt (T*q) +
        5*(HighSurplus.highVertices G q).card*T := by
  have hall := all_high_rows_with_overlaps G q hN
  simp only [Nat.cast_sum] at hall
  have hov := Statistics.subset_codegree_overlap G (HighSurplus.highVertices G q)
  have hTq : (0 : ℝ) ≤ T*q := mul_nonneg (by linarith) (by linarith)
  have hsqrt := choose_overlap_sqrt_bound (HighSurplus.highVertices G q).card
    (Counting.cycleCount G) hTq (le_of_lt hZ)
  have hq1 : 1 ≤ q := by
    have : (1 : ℝ) ≤ q := by linarith
    exact_mod_cast this
  have hb := Statistics.totalDeficiency_eq G q hq1 hN hE
  have hc := deficient_card_le_total G q
  have hcs : ((deficientVertices G q).card : ℝ) ≤
      (q : ℝ)-1+Statistics.totalSurplus G q := by
    have hcn : (deficientVertices G q).card+1 ≤ q+Statistics.totalSurplus G q := by omega
    have hcr : ((deficientVertices G q).card : ℝ)+1 ≤ (q : ℝ)+Statistics.totalSurplus G q := by
      exact_mod_cast hcn
    linarith
  have hex := excessDeficiency_bound G q T hq hT hr heven hN hE hZ
  have hmul := mul_le_mul_of_nonneg_left hex
    (Nat.cast_nonneg (α := ℝ) (HighSurplus.highVertices G q).card)
  nlinarith

/-- Source §4's total degree-surplus localization, with no assumed row bound. -/
theorem totalSurplus_bound (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    (Statistics.totalSurplus G q : ℝ) ≤ 20*T := by
  have hh := HighSurplus.high_count_bound G q T hq hT hr hN hE hZ
  have hs := all_high_scalar_bound G q T hq hT hr heven hN hE hZ
  exact Parameters.high_sum_bound hq hT hr (Nat.cast_nonneg _) hh.2 hs

 theorem deficiency_le_excess_add_one (G : SimpleGraph V) (q : ℕ) (x : V) :
    Statistics.degreeDeficiency G q x ≤ excessDeficiency G q+1 := by
  have hpoint : Statistics.degreeDeficiency G q x-1 ≤
      ∑ y : V, (Statistics.degreeDeficiency G q y-1) :=
    Finset.single_le_sum (f := fun y => Statistics.degreeDeficiency G q y-1) (fun y _ => Nat.zero_le _) (Finset.mem_univ x)
  rw [← excessDeficiency_eq_sum] at hpoint
  omega

noncomputable def deepDeficient (G : SimpleGraph V) (q : ℕ) : Finset V :=
  Finset.univ.filter fun x => 2 ≤ Statistics.degreeDeficiency G q x

 theorem deepDeficient_card_le_excess (G : SimpleGraph V) (q : ℕ) :
    (deepDeficient G q).card ≤ excessDeficiency G q := by
  rw [excessDeficiency_eq_sum]
  have hs : (∑ x ∈ deepDeficient G q, (1 : ℕ)) ≤
      ∑ x ∈ deepDeficient G q, (Statistics.degreeDeficiency G q x-1) := by
    apply Finset.sum_le_sum
    intro x hx
    have hd := (Finset.mem_filter.mp hx).2
    omega
  have hb : (∑ x ∈ deepDeficient G q, (Statistics.degreeDeficiency G q x-1)) ≤
      ∑ x : V, (Statistics.degreeDeficiency G q x-1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => Nat.zero_le _)
  simpa using hs.trans hb

/-- All degree-deficiency consequences in source §4 equation (13). -/
theorem localized_deficit_bounds (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (hE : (G.edgeFinset.card : ℝ) = (q : ℝ)*((q : ℝ)+1)^2/2+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    ((HighSurplus.highVertices G q).card : ℝ) ≤ 20*T ∧
      (Statistics.totalDeficiency G q : ℝ) ≤ (q : ℝ)-1+20*T ∧
      (excessDeficiency G q : ℝ) ≤ 25*T ∧
      (∀ x, (Statistics.degreeDeficiency G q x : ℝ) ≤ 26*T) ∧
      ((deepDeficient G q).card : ℝ) ≤ 25*T := by
  have hp := totalSurplus_bound G q T hq hT hr heven hN hE hZ
  have hhc := high_card_le_surplus G q
  have hhcr : ((HighSurplus.highVertices G q).card : ℝ) ≤ Statistics.totalSurplus G q := by
    exact_mod_cast hhc
  have hq1 : 1 ≤ q := by
    have : (1 : ℝ) ≤ q := by linarith
    exact_mod_cast this
  have hbal := Statistics.totalDeficiency_eq G q hq1 hN hE
  have hbaln : Statistics.totalDeficiency G q+1=q+Statistics.totalSurplus G q := by omega
  have hbalr : (Statistics.totalDeficiency G q : ℝ)+1=(q : ℝ)+Statistics.totalSurplus G q := by
    exact_mod_cast hbaln
  have he := excessDeficiency_bound G q T hq hT hr heven hN hE hZ
  have hex : (excessDeficiency G q : ℝ) ≤ 25*T := by linarith
  refine ⟨by linarith,by linarith,hex,?_,?_⟩
  · intro x
    have hf := deficiency_le_excess_add_one G q x
    have hfr : (Statistics.degreeDeficiency G q x : ℝ) ≤ (excessDeficiency G q : ℝ)+1 := by
      exact_mod_cast hf
    linarith
  · have hd := deepDeficient_card_le_excess G q
    have hdr : ((deepDeficient G q).card : ℝ) ≤ excessDeficiency G q := by exact_mod_cast hd
    linarith

end Erdos60.SurplusRows
