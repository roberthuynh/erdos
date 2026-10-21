import Mathlib

/-! Actual original-edge deletion charged at local reservoir degrees.
This counting step does not assert routing or random reservoir existence. -/
namespace Erdos585.Attempt6

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

def incidentDeletion (S : Finset V) : Finset (Sym2 V) :=
  S.biUnion (fun v => H.incidenceFinset v)

theorem incidentDeletion_subset_edges (S : Finset V) :
    incidentDeletion H S ⊆ H.edgeFinset := by
  intro e he
  obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp he
  exact H.incidenceFinset_subset v hv

theorem incidentDeletion_card_le_sum (S : Finset V) :
    (incidentDeletion H S).card ≤ ∑ v ∈ S, H.degree v := by
  unfold incidentDeletion
  simpa only [SimpleGraph.card_incidenceFinset_eq_degree] using
    (Finset.card_biUnion_le :
      (S.biUnion (fun v => H.incidenceFinset v)).card ≤ ∑ v ∈ S, (H.incidenceFinset v).card)

theorem incidentDeletion_card_le_local (S : Finset V) (M : ℕ)
    (hM : ∀ v ∈ S, H.degree v ≤ M) :
    (incidentDeletion H S).card ≤ M * S.card := by
  calc
    (incidentDeletion H S).card ≤ ∑ v ∈ S, H.degree v :=
      incidentDeletion_card_le_sum H S
    _ ≤ ∑ _v ∈ S, M := Finset.sum_le_sum hM
    _ = M * S.card := by simp [Nat.mul_comm]

theorem incidentDeletion_card_le_real (S : Finset V) (M : ℝ)
    (hM : ∀ v ∈ S, (H.degree v : ℝ) ≤ M) :
    ((incidentDeletion H S).card : ℝ) ≤ M * (S.card : ℝ) := by
  have h := incidentDeletion_card_le_sum H S
  calc
    ((incidentDeletion H S).card : ℝ) ≤ ∑ v ∈ S, (H.degree v : ℝ) := by
      exact_mod_cast h
    _ ≤ ∑ _v ∈ S, M := Finset.sum_le_sum hM
    _ = M * (S.card : ℝ) := by simp [mul_comm]

theorem no_adj_after_incidentDeletion (S : Finset V) {v w : V} (hv : v ∈ S) :
    ¬ (H.deleteEdges (incidentDeletion H S : Set (Sym2 V))).Adj v w := by
  intro h
  have hh := SimpleGraph.deleteEdges_adj.mp h
  apply hh.2
  exact Finset.mem_biUnion.mpr ⟨v, hv, by
    simpa only [SimpleGraph.mem_incidenceFinset, SimpleGraph.mem_incidenceSet] using hh.1⟩

end Erdos585.Attempt6
