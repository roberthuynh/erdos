import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestEdges
import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestOccupationAlgebra
import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphPath

/-! Actual zero/one occupation counts and literal selected edges under self-avoidance. -/
namespace Erdos642.CampaignFe72210b
open Erdos642.FiniteMarkov Erdos642.FiniteMarkov.PathAvoidance
open Erdos642.OccupationTail Erdos642.OccupationAlgebra
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem nodeList_eq_observations {n : ℕ} (x : V) (p : Path V n) :
    nodeList x p = x :: PathCoordinates.future p := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨y, p⟩
    change x :: nodeList y p = x :: y :: PathCoordinates.future p
    rw [ih]

theorem singleton_occupation_of_actualSA {n : ℕ} (x : V) (p : Path V n)
    (h : actualSA x p) (v : V) :
    occupation {v} x p = if v ∈ visited x p then 1 else 0 := by
  rw [occupation_singleton_eq_count]
  by_cases hv : v ∈ x :: PathCoordinates.future p
  · have hc := List.count_eq_one_of_mem h hv
    simp only [hc, Nat.cast_one, mem_visited, hv, if_true]
  · have hc := List.count_eq_zero.mpr hv
    simp only [hc, Nat.cast_zero, mem_visited, hv, if_false]

namespace ForestBundle
variable {G : SimpleGraph V} {A B : Finset V} {q m b : ℕ}
variable (F : ForestBundle G A B q m b)

theorem occupationWeightedCount_eq_selectedEdges {n k : ℕ}
    (x : V) (p : Path V n) (y : V) (r : Path V k)
    (hp : actualSA x p) (hr : actualSA y r) :
    F.occupationWeightedCount x p y r =
      ((F.selectedEdges (visited x p) (visited y r)).card : ℝ) := by
  unfold occupationWeightedCount
  simp_rw [singleton_occupation_of_actualSA x p hp, singleton_occupation_of_actualSA y r hr]
  exact F.indicator_weightedCount_eq_card _ _

theorem occupationWeightedCount_le_supportEdges {n k : ℕ} {u v : V}
    (x : V) (p : Path V n) (y : V) (r : Path V k)
    (hp : actualSA x p) (hr : actualSA y r) (w : G.Walk u v)
    (hL : ∀ z ∈ visited x p, z ∈ w.support)
    (hR : ∀ z ∈ visited y r, z ∈ w.support) :
    F.occupationWeightedCount x p y r ≤ ((supportEdges w).card : ℝ) := by
  rw [F.occupationWeightedCount_eq_selectedEdges x p y r hp hr]
  exact_mod_cast Finset.card_le_card (F.selectedEdges_subset_support w _ _ hL hR)

end ForestBundle
end Erdos642.CampaignFe72210b
