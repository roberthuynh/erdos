import Mathlib

/-! A finite original-neighbor matching from actual incidence degree bounds. -/
namespace Erdos585.Attempt6
open scoped BigOperators

variable {I A : Type*} [Fintype I] [DecidableEq I] [DecidableEq A]

theorem finite_incidence_double_count (N : I → Finset A) (S : Finset I) :
    (∑ i ∈ S, (N i).card) =
      ∑ a ∈ S.biUnion N, (S.filter (fun i => a ∈ N i)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_filter]
  have h : (S.biUnion N).filter (fun a => a ∈ N i) = N i := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · exact fun z => z.2
    · exact fun ha => ⟨⟨i, hi, ha⟩, ha⟩
  rw [h]

theorem exists_injective_neighbor_of_degree_bounds (N : I → Finset A) (d : ℕ)
    (hd : 0 < d) (hleft : ∀ i, d ≤ (N i).card)
    (hright : ∀ a, (Finset.univ.filter (fun i => a ∈ N i)).card ≤ d) :
    ∃ f : I → A, Function.Injective f ∧ ∀ i, f i ∈ N i := by
  classical
  apply HallMarriageTheorem.hall_hard_inductive
  intro S
  have count_bound : d * S.card ≤ d * (S.biUnion N).card := by
    calc
      d * S.card = ∑ _i ∈ S, d := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ S, (N i).card := Finset.sum_le_sum (fun i _ => hleft i)
      _ = ∑ a ∈ S.biUnion N, (S.filter (fun i => a ∈ N i)).card :=
        finite_incidence_double_count N S
      _ ≤ ∑ _a ∈ S.biUnion N, d := by
        apply Finset.sum_le_sum
        intro a _
        exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))).trans
          (hright a)
      _ = d * (S.biUnion N).card := by simp [Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_left count_bound hd

theorem repeated_incidence_count (N : I → Finset A) (q : ℕ) (a : A) :
    (Finset.univ.filter (fun ij : I × Fin q => a ∈ N ij.1)).card =
      q * (Finset.univ.filter (fun i => a ∈ N i)).card := by
  classical
  have heq : (Finset.univ.filter (fun ij : I × Fin q => a ∈ N ij.1)) =
      (Finset.univ.filter (fun i => a ∈ N i)) ×ˢ (Finset.univ : Finset (Fin q)) := by
    ext ij
    simp
  rw [heq, Finset.card_product]
  simp [Nat.mul_comm]

/-- Each terminal receives q distinct original neighbors, disjoint across all copies. -/
theorem exists_private_neighbors (N : I → Finset A) (q d : ℕ)
    (hd : 0 < d) (hleft : ∀ i, d ≤ (N i).card)
    (hright : ∀ a, q * (Finset.univ.filter (fun i => a ∈ N i)).card ≤ d) :
    ∃ f : I × Fin q → A, Function.Injective f ∧ ∀ ij, f ij ∈ N ij.1 := by
  classical
  apply exists_injective_neighbor_of_degree_bounds (fun ij : I × Fin q => N ij.1) d hd
  · exact fun ij => hleft ij.1
  · intro a
    rw [repeated_incidence_count]
    exact hright a

/-- Terminals may repeat: the right-hand load counts occurrences, not distinct vertices. -/
theorem exists_private_graph_leaves (G : SimpleGraph A) [DecidableRel G.Adj]
    (terminal : I → A)
    (W : Finset A) (q d : ℕ) (hd : 0 < d)
    (hleft : ∀ i, d ≤ (W.filter (G.Adj (terminal i))).card)
    (hright : ∀ a ∈ W,
      q * (Finset.univ.filter (fun i => G.Adj (terminal i) a)).card ≤ d) :
    ∃ f : I × Fin q → A, Function.Injective f ∧
      ∀ ij, f ij ∈ W ∧ G.Adj (terminal ij.1) (f ij) := by
  classical
  obtain ⟨f, hf, hn⟩ := exists_private_neighbors
    (fun i => W.filter (G.Adj (terminal i))) q d hd hleft (by
      intro a
      by_cases ha : a ∈ W
      · simpa [ha] using hright a ha
      · simp [ha])
  exact ⟨f, hf, fun ij => Finset.mem_filter.mp (hn ij)⟩

end Erdos585.Attempt6
