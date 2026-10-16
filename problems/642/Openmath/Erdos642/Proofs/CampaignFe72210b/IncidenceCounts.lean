import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-! Literal ordered incidence counts for the finite forest argument. -/
namespace Erdos642.CampaignFe72210b
namespace IncidenceCounts
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def count (A B : Finset V) : ℕ := ∑ a ∈ A, (B.filter (G.Adj a)).card

omit [Fintype V] [DecidableEq V] in
theorem count_swap (A B : Finset V) : count G A B = count G B A := by
  unfold count
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  simp only [G.adj_comm]

theorem restricted_degree_le (B : Finset V) (a : V) :
    (B.filter (G.Adj a)).card ≤ G.degree a := by
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro b hb
  exact (G.mem_neighborFinset a b).mpr (Finset.mem_filter.mp hb).2

theorem count_le_sum_degree (A B : Finset V) :
    count G A B ≤ ∑ a ∈ A, G.degree a := by
  exact Finset.sum_le_sum fun a _ => restricted_degree_le G B a

theorem count_le_card_mul (A B : Finset V) (D : ℕ)
    (hD : ∀ b ∈ B, G.degree b ≤ D) : count G A B ≤ B.card * D := by
  rw [count_swap]
  calc
    count G B A ≤ ∑ b ∈ B, G.degree b := count_le_sum_degree G B A
    _ ≤ ∑ _b ∈ B, D := Finset.sum_le_sum hD
    _ = B.card * D := by simp

omit [Fintype V] [DecidableEq V] in
theorem card_mul_le_count (A B : Finset V) (d : ℕ)
    (hd : ∀ a ∈ A, d ≤ (B.filter (G.Adj a)).card) :
    A.card * d ≤ count G A B := by
  calc
    A.card * d = ∑ _a ∈ A, d := by simp
    _ ≤ count G A B := Finset.sum_le_sum hd

end IncidenceCounts
end Erdos642.CampaignFe72210b
