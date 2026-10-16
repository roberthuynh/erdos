import NeighborhoodUnion
import DeficientNeighborParity
import Parameters
import Mathlib.Data.Nat.Choose.Cast

namespace Erdos60.Statistics
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A zero-cycle nondeficient vertex has an actual deficient neighbor. -/
theorem zero_cycle_has_deficient_neighbor (G : SimpleGraph V) (q : ℕ)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (S : Finset V) (hS : ∀ x, x ∈ S ↔ G.degree x < q+1)
    (x : V) (hx : x ∉ S) (hz : vertexCycleStatistic G x = 0) :
    ∃ s ∈ S, G.Adj x s := by
  by_contra hn
  have hdeg : q+1 ≤ G.degree x := by have := (hS x).not.mp hx; omega
  have hnb : ∀ s, G.Adj x s → q+1 ≤ G.degree s := by
    intro s hs
    by_contra hd
    exact hn ⟨s,(hS s).mpr (by omega),hs⟩
  have := cycle_statistic_pos_of_no_deficient_neighbor G q heven hN x hdeg hnb
  omega

/-- Clean vertices in a punctured neighborhood have distinct deficient
neighbors outside the root neighborhood; this is an actual injection argument. -/
theorem clean_punctured_neighbors_bound (G : SimpleGraph V) (q : ℕ)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (S : Finset V) (hS : ∀ x, x ∈ S ↔ G.degree x < q+1)
    (v i : V) (hvi : G.Adj v i) (hi : i ∉ S) :
    (((G.neighborFinset i).erase v).filter fun x =>
      x ∉ S ∧ vertexCycleStatistic G x = 0).card ≤ (S \ G.neighborFinset v).card := by
  classical
  let C := ((G.neighborFinset i).erase v).filter fun x =>
      x ∉ S ∧ vertexCycleStatistic G x = 0
  have hw : ∀ x ∈ C, ∃ s ∈ S \ G.neighborFinset v, G.Adj x s := by
    intro x hx
    obtain ⟨hxN,hxS,hxz⟩ := Finset.mem_filter.mp hx
    have hxv := (Finset.mem_erase.mp hxN).1
    have hxi : G.Adj x i := by
      have := (Finset.mem_erase.mp hxN).2
      simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.adj_comm] using this
    obtain ⟨s,hs,hxs⟩ := zero_cycle_has_deficient_neighbor G q heven hN S hS x hxS hxz
    have hsn : s ∉ G.neighborFinset v := by
      intro hvs
      have hvs' : G.Adj v s := by simpa using hvs
      have his := common_neighbor_unique_of_cycle_statistic_zero G hxz hxv hxi hvi hxs hvs'
      exact hi (his ▸ hs)
    exact ⟨s,Finset.mem_sdiff.mpr ⟨hs,hsn⟩,hxs⟩
  choose f hf using hw
  let F : ↥C → ↥(S \ G.neighborFinset v) := fun x => ⟨f x.val x.property,(hf x.val x.property).1⟩
  have hinj : Function.Injective F := by
    intro x y heq
    apply Subtype.ext
    by_contra hxy
    have hx := Finset.mem_filter.mp x.property
    have hy := Finset.mem_filter.mp y.property
    have hxi : G.Adj x.val i := by
      have := (Finset.mem_erase.mp hx.1).2
      simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.adj_comm] using this
    have hyi : G.Adj y.val i := by
      have := (Finset.mem_erase.mp hy.1).2
      simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.adj_comm] using this
    have hfs : f x.val x.property = f y.val y.property := congrArg Subtype.val heq
    have his := common_neighbor_unique_of_cycle_statistic_zero G hx.2.2 hxy hxi hyi
      (hf x.val x.property).2 (hfs ▸ (hf y.val y.property).2)
    have hs := (Finset.mem_sdiff.mp (hf x.val x.property).1).1
    exact hi (his ▸ hs)
  have hc := Fintype.card_le_of_injective F hinj
  simpa only [Fintype.card_coe] using hc

noncomputable def positiveCycleVertices (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter fun x => 0 < vertexCycleStatistic G x

theorem positiveCycleVertices_card (G : SimpleGraph V) :
    (positiveCycleVertices G).card ≤ 4 * Counting.cycleCount G := by
  rw [← vertexCycleStatistic_sum_eq_four]
  have h : (∑ x ∈ positiveCycleVertices G, (1 : ℕ)) ≤
      ∑ x ∈ positiveCycleVertices G, vertexCycleStatistic G x := by
    apply Finset.sum_le_sum
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  calc
    _ = ∑ x ∈ positiveCycleVertices G, (1 : ℕ) := by simp
    _ ≤ _ := h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x hx hnot => Nat.zero_le _)

/-- Actual clean-neighborhood upper bound underlying source equation (15). -/
theorem clean_neighbor_union_budget (G : SimpleGraph V) (q : ℕ)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (S : Finset V) (hS : ∀ x, x ∈ S ↔ G.degree x < q+1) (v : V) :
    q * (G.neighborFinset v \ S).card ≤
      (G.neighborFinset v \ S).card * (S \ G.neighborFinset v).card + S.card +
        4 * Counting.cycleCount G + vertexCycleStatistic G v := by
  classical
  let I := G.neighborFinset v \ S
  let C := fun i => ((G.neighborFinset i).erase v).filter fun x =>
    x ∉ S ∧ vertexCycleStatistic G x = 0
  have hCcount : ∀ i ∈ I, (C i).card ≤ (S \ G.neighborFinset v).card := by
    intro i hi
    obtain ⟨hiv,hiS⟩ := Finset.mem_sdiff.mp hi
    have hvi : G.Adj v i := by simpa using hiv
    exact clean_punctured_neighbors_bound G q heven hN S hS v i hvi hiS
  have hcover : puncturedNeighborUnion G v I ⊆
      (I.biUnion C ∪ S) ∪ positiveCycleVertices G := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := Finset.mem_biUnion.mp hx
    by_cases hxS : x ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hxS)
    · by_cases hz : vertexCycleStatistic G x = 0
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hxi,hxS,hz⟩⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩)
  have hU : (puncturedNeighborUnion G v I).card ≤
      I.card * (S \ G.neighborFinset v).card + S.card + 4 * Counting.cycleCount G := by
    calc
      _ ≤ ((I.biUnion C ∪ S) ∪ positiveCycleVertices G).card := Finset.card_le_card hcover
      _ ≤ (I.biUnion C ∪ S).card + (positiveCycleVertices G).card := Finset.card_union_le _ _
      _ ≤ (I.biUnion C).card + S.card + 4 * Counting.cycleCount G := by
        have := Finset.card_union_le (I.biUnion C) S
        have := positiveCycleVertices_card G
        omega
      _ ≤ _ := by
        have hbi : (I.biUnion C).card ≤ I.card * (S \ G.neighborFinset v).card := by
          calc
            _ ≤ ∑ i ∈ I, (C i).card := Finset.card_biUnion_le
            _ ≤ ∑ i ∈ I, (S \ G.neighborFinset v).card := Finset.sum_le_sum hCcount
            _ = _ := by simp
        omega
  have hl := nondeficient_neighbor_union G q v I (Finset.sdiff_subset)
    (fun i hi => by have hn := (hS i).not.mp (Finset.mem_sdiff.mp hi).2; omega)
  change q * I.card ≤ I.card * (S \ G.neighborFinset v).card + S.card +
    4 * Counting.cycleCount G + vertexCycleStatistic G v
  omega

theorem local_cycle_le_total (G : SimpleGraph V) (v : V) :
    vertexCycleStatistic G v ≤ Counting.cycleCount G := by
  rw [vertexCycleStatistic_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Source equation (15) derived from actual clean-neighborhood injections. -/
theorem deficient_neighbor_product_bound (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (S : Finset V) (hS : ∀ x, x ∈ S ↔ G.degree x < q+1)
    (hsize : (S.card : ℝ) ≤ q+20*T)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) (v : V) :
    ((G.neighborFinset v \ S).card : ℝ) *
      (((G.neighborFinset v ∩ S).card : ℝ)-20*T) ≤ 12*T*q := by
  have hb := clean_neighbor_union_budget G q heven hN S hS v
  have hc := local_cycle_le_total G v
  have hsplit : (S \ G.neighborFinset v).card + (G.neighborFinset v ∩ S).card = S.card := by
    have hh := Finset.card_sdiff_add_card_inter S (G.neighborFinset v)
    rw [Finset.inter_comm] at hh
    exact hh
  have hr : (q : ℝ) * ((G.neighborFinset v \ S).card : ℝ) ≤
      ((G.neighborFinset v \ S).card : ℝ) * (S \ G.neighborFinset v).card + S.card +
        4*(Counting.cycleCount G : ℝ) + vertexCycleStatistic G v := by exact_mod_cast hb
  have hcr : (vertexCycleStatistic G v : ℝ) ≤ Counting.cycleCount G := by exact_mod_cast hc
  have hsplitr : ((S \ G.neighborFinset v).card : ℝ) +
      (G.neighborFinset v ∩ S).card = S.card := by exact_mod_cast hsplit
  have hmul := mul_nonneg (Nat.cast_nonneg (α := ℝ) (G.neighborFinset v \ S).card)
    (sub_nonneg.mpr hsize)
  have hT0 : 0 ≤ T := by linarith
  have hq0 : (20 : ℝ) ≤ q := by linarith
  nlinarith [mul_nonneg (show 0 ≤ T-1 by linarith) (show 0 ≤ (q : ℝ) by positivity),
    mul_nonneg hT0 (show 0 ≤ (q : ℝ)-20 by linarith)]

/-- Actual deficient-neighborhood dichotomy under the explicit degree/deficit
consequences supplied by SurplusRows; equation (15) is proved, not a premise. -/
theorem deficient_neighbor_dichotomy (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hrange : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card V = q^2+q+1)
    (S : Finset V) (hS : ∀ x, x ∈ S ↔ G.degree x < q+1)
    (hsize : (S.card : ℝ) ≤ q+20*T)
    (hmin : ∀ x, (q : ℝ)-26*T ≤ G.degree x)
    (hZ : (Counting.cycleCount G : ℝ) < T*q) (v : V) :
    ((G.neighborFinset v ∩ S).card : ℝ) < 50*T ∨
      (q : ℝ)-76*T < (G.neighborFinset v ∩ S).card := by
  by_contra hn
  push Not at hn
  obtain ⟨hb,hb'⟩ := hn
  have hp := deficient_neighbor_product_bound G q T hq hT heven hN S hS hsize hZ v
  have hsplit : (G.neighborFinset v \ S).card + (G.neighborFinset v ∩ S).card = G.degree v := by
    rw [Finset.card_sdiff_add_card_inter,G.card_neighborFinset_eq_degree]
  have hs : ((G.neighborFinset v \ S).card : ℝ) +
      (G.neighborFinset v ∩ S).card = G.degree v := by exact_mod_cast hsplit
  have hminv := hmin v
  have hparam := (Parameters.neighborhood_parameters hq hT hrange hb hb').1
  have hmul := mul_nonneg
    (show 0 ≤ ((G.neighborFinset v \ S).card : ℝ)-
      ((q : ℝ)-26*T-(G.neighborFinset v ∩ S).card) by linarith)
    (show 0 ≤ ((G.neighborFinset v ∩ S).card : ℝ)-20*T by linarith)
  nlinarith

/-- Two vertices of the large-neighborhood type would already force more
actual cycles than the host budget allows. -/
theorem large_deficient_neighbor_unique (G : SimpleGraph V) (q : ℕ) (T : ℝ)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hrange : T ≤ (q : ℝ)/10^8)
    (S : Finset V) (hsize : (S.card : ℝ) ≤ q+20*T)
    (hZ : (Counting.cycleCount G : ℝ) < T*q)
    (u v : V)
    (hu : (q : ℝ)-76*T < (G.neighborFinset u ∩ S).card)
    (hv : (q : ℝ)-76*T < (G.neighborFinset v ∩ S).card) : u = v := by
  by_contra huv
  let A := G.neighborFinset u ∩ S
  let B := G.neighborFinset v ∩ S
  have hcard := Finset.card_union_add_card_inter A B
  have hUnion : (A ∪ B).card ≤ S.card := by
    apply Finset.card_le_card
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp hx).2
    · exact (Finset.mem_inter.mp hx).2
  have hInter : (A ∩ B).card ≤ codegree G u v := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxA,hxB⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxA).1,(Finset.mem_inter.mp hxB).1⟩
  have hcs : (G.neighborFinset u ∩ S).card + (G.neighborFinset v ∩ S).card ≤
      S.card + codegree G u v := by change A.card+B.card ≤ _; omega
  have hcsr : ((G.neighborFinset u ∩ S).card : ℝ) +
      (G.neighborFinset v ∩ S).card ≤ S.card + codegree G u v := by exact_mod_cast hcs
  have hcod : (q : ℝ)-172*T < codegree G u v := by linarith
  have hweight : (codegree G u v).choose 2 ≤ Counting.cycleCount G := by
    have hc := Finset.single_le_sum (f := fun y => (codegree G u y).choose 2)
      (fun y hy => Nat.zero_le _) (by simp [Ne.symm huv] : v ∈ Finset.univ.erase u)
    exact hc.trans (local_cycle_le_total G u)
  have hwreal : (codegree G u v : ℝ)*((codegree G u v : ℝ)-1)/2 ≤
      Counting.cycleCount G := by
    have : ((codegree G u v).choose 2 : ℝ) ≤ Counting.cycleCount G := by exact_mod_cast hweight
    rwa [Nat.cast_choose_two] at this
  have h50 : 50*T ≤ (q : ℝ)-76*T := by linarith
  have hparam := (Parameters.neighborhood_parameters hq hT hrange (le_refl (50*T)) h50).2
  have ha : (1 : ℝ) ≤ q-172*T := by linarith
  have hmul := mul_nonneg
    (show 0 ≤ (codegree G u v : ℝ)-((q : ℝ)-172*T) by linarith)
    (show 0 ≤ (codegree G u v : ℝ)+((q : ℝ)-172*T)-1 by linarith)
  nlinarith

end Erdos60.Statistics
