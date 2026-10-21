import GraphStatistics

/-! Actual subset two-path inequality, source LOCALIZATION-ARGUMENT.md §1
(equation (3)). `subset_ordered_twoPath_count` proves the grouping from actual
neighbor sets. `subset_path_bound` then applies n ≤ choose(n,2)+1 and the proved
ordinary-unlabelled cycle normalization, with no grouping or count premise.
The equivalent real inequality is 2 Z ≥ sum_w choose(|N(w)∩A|,2)−choose(|A|,2).
This is a localization helper, not the #60 headline theorem. -/

namespace Erdos60.Statistics
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ,Nat.choose_one_right,Nat.succ_sub_one]
    by_cases hn : n = 0
    · subst n; simp
    · have hh : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)
      nlinarith

theorem codegree_eq_full_sum (G : SimpleGraph V) (x y : V) :
    codegree G x y = ∑ w : V, if G.Adj x w ∧ G.Adj y w then 1 else 0 := by
  classical
  rw [Finset.sum_boole]
  unfold codegree
  congr 1
  ext w
  simp

/-- Actual subset two-path grouping, before applying any scalar estimate. -/
theorem subset_ordered_twoPath_count (G : SimpleGraph V) (A : Finset V) :
    (∑ x ∈ A, ∑ y ∈ A.erase x, codegree G x y) =
      ∑ w : V, (G.neighborFinset w ∩ A).card * ((G.neighborFinset w ∩ A).card - 1) := by
  classical
  simp_rw [codegree_eq_full_sum]
  simp_rw [Finset.sum_comm (s := A.erase _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  let B := G.neighborFinset w ∩ A
  have hi : ∀ x ∈ A,
      (∑ y ∈ A.erase x, if G.Adj x w ∧ G.Adj y w then 1 else 0) =
        if G.Adj x w then B.card - 1 else 0 := by
    intro x hx
    by_cases hxw : G.Adj x w
    · have hxB : x ∈ B := by simp [B,hx,hxw.symm]
      have hfilter : {y ∈ A.erase x | G.Adj y w} = B.erase x := by
        ext y
        simp [B,SimpleGraph.adj_comm,and_comm,and_assoc]
      simp only [hxw,true_and,Finset.sum_boole,Nat.cast_id,ite_true]
      rw [hfilter,Finset.card_erase_of_mem hxB]
    · simp [hxw]
  simp_rw [Finset.sum_congr rfl hi]
  have hAB : A.filter (fun x => G.Adj x w) = B := by
    ext x
    simp [B,SimpleGraph.adj_comm,and_comm]
  rw [← Finset.sum_filter, hAB]
  simp [B]

/-- Source equation (3), actual graph form with no assumed grouping identity. -/
theorem subset_path_bound (G : SimpleGraph V) (A : Finset V) :
    (∑ w : V, ((G.neighborFinset w ∩ A).card).choose 2) ≤
      2 * Erdos60.Counting.cycleCount G + A.card.choose 2 := by
  classical
  have hgroup := subset_ordered_twoPath_count G A
  have hdouble : (∑ x ∈ A, ∑ y ∈ A.erase x, codegree G x y) =
      2 * ∑ w : V, ((G.neighborFinset w ∩ A).card).choose 2 := by
    rw [hgroup,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    exact (two_mul_choose_two _).symm
  have hscalar : (∑ x ∈ A, ∑ y ∈ A.erase x, codegree G x y) ≤
      (∑ x ∈ A, ∑ y ∈ A.erase x, (codegree G x y).choose 2) + A.card * (A.card - 1) := by
    have hh' : (∑ x ∈ A, ∑ y ∈ A.erase x, codegree G x y) ≤
        ∑ x ∈ A, ∑ y ∈ A.erase x, ((codegree G x y).choose 2 + 1) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      have := choose_two_lower (codegree G x y)
      omega
    have hcards : (∑ x ∈ A, (A.erase x).card) = A.card * (A.card - 1) := by
      calc
        _ = ∑ x ∈ A, (A.card - 1) := Finset.sum_congr rfl
          (fun x hx => Finset.card_erase_of_mem hx)
        _ = _ := by simp
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Nat.smul_one_eq_cast,
      Nat.cast_id,hcards] using hh'
  have hweights : (∑ x ∈ A, ∑ y ∈ A.erase x, (codegree G x y).choose 2) ≤
      4 * Erdos60.Counting.cycleCount G := by
    rw [← vertexCycleStatistic_sum_eq_four]
    calc
      _ ≤ ∑ x ∈ A, vertexCycleStatistic G x := by
        apply Finset.sum_le_sum
        intro x hx
        unfold vertexCycleStatistic
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.erase_subset_erase x (Finset.subset_univ A)
        · intro i hi hnot; exact Nat.zero_le _
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        (fun i hi hnot => Nat.zero_le _)
  rw [hdouble,← two_mul_choose_two A.card] at hscalar
  omega

end Erdos60.Statistics
