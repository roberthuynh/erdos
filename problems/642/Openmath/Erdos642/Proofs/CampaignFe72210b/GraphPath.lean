import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphMarkov

/-! Actual graph walks reconstructed from positive finite path weights. -/
namespace Erdos642.CampaignFe72210b
open SimpleGraph
open Erdos642.FiniteMarkov

universe u
variable {V : Type u} [Fintype V]

/-- All observed vertices, in chronological order, including the initial state. -/
def nodeList : {n : ℕ} → V → Path V n → List V
  | 0, x, _ => [x]
  | _ + 1, x, (y, p) => x :: nodeList y p

omit [Fintype V] in
theorem nodeList_length {n : ℕ} (x : V) (p : Path V n) :
    (nodeList x p).length = n + 1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change (nodeList p.1 p.2).length + 1 = n + 1 + 1
    rw [ih]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem adj_of_graphTransition_pos (x y : V) (h : 0 < graphTransition G x y) :
    G.Adj x y := by
  by_contra hn
  simp [graphTransition, SimpleGraph.adjMatrix_apply, hn] at h

variable (hdeg : ∀ x : V, 0 < G.degree x)

private theorem positive_factors {n : ℕ} (x y : V) (p : Path V n)
    (h : 0 < (graphChain G hdeg).weight (n := n + 1) x (y, p)) :
    0 < graphTransition G x y ∧ 0 < (graphChain G hdeg).weight y p := by
  change 0 < graphTransition G x y * (graphChain G hdeg).weight y p at h
  rcases mul_pos_iff.mp h with hpos | hneg
  · exact hpos
  · have hn := graphTransition_nonneg G x y
    linarith [hneg.1]

/-- The actual walk certified by positivity of the genuine graph path law. -/
noncomputable def positiveWalk : {n : ℕ} → (x : V) → (p : Path V n) →
    0 < (graphChain G hdeg).weight x p →
      G.Walk x ((graphChain G hdeg).endpoint x p)
  | 0, _, _, _ => .nil
  | _ + 1, x, (y, p), h =>
    .cons (adj_of_graphTransition_pos G x y (positive_factors G hdeg x y p h).1)
      (positiveWalk y p (positive_factors G hdeg x y p h).2)

theorem positiveWalk_length {n : ℕ} (x : V) (p : Path V n)
    (h : 0 < (graphChain G hdeg).weight x p) :
    (positiveWalk G hdeg x p h).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change (positiveWalk G hdeg p.1 p.2 _).length + 1 = n + 1
    rw [ih]

theorem positiveWalk_support {n : ℕ} (x : V) (p : Path V n)
    (h : 0 < (graphChain G hdeg).weight x p) :
    (positiveWalk G hdeg x p h).support = nodeList x p := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change x :: (positiveWalk G hdeg p.1 p.2 _).support = x :: nodeList p.1 p.2
    rw [ih]

theorem positiveWalk_isPath {n : ℕ} (x : V) (p : Path V n)
    (h : 0 < (graphChain G hdeg).weight x p) (hn : (nodeList x p).Nodup) :
    (positiveWalk G hdeg x p h).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [positiveWalk_support]
  exact hn

end Erdos642.CampaignFe72210b
