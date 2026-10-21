import Openmath.Proofs.PathCycleCompletion
import Openmath.Proofs.ConditionalCompletionCount

/-!
# Pairing isolated vertices on a fixed vertex set

Original path vertices stay fixed. A permutation moves only right isolated
vertices. Conjugating the canonical path successor supplies a spanning cycle
whose joining units have exactly the endpoint rule used by the counting theorem.
-/

namespace Erdos585.FixedVertexCompletion

open Equiv SimpleGraph
open Erdos585.PathCycleCompletion
open scoped BigOperators

variable {P S : Type*}

/-- The new one-edge paths have extra length zero. -/
def extended (extra : P → ℕ) : P ⊕ S → ℕ := Sum.elim extra (fun _ => 0)

abbrev ActualVertex (extra : P → ℕ) := Vertex (extended (S := S) extra)

/-- Move right isolated vertices, fixing all original path vertices and left vertices. -/
def relabelFn (extra : P → ℕ) (σ : Perm S) : ActualVertex (S := S) extra → ActualVertex (S := S) extra
  | ⟨Sum.inl p, k⟩ => ⟨Sum.inl p, k⟩
  | ⟨Sum.inr s, k⟩ => if k.val = 0 then ⟨Sum.inr s, k⟩ else ⟨Sum.inr (σ s), k⟩

def relabel (extra : P → ℕ) (σ : Perm S) : Perm (ActualVertex (S := S) extra) where
  toFun := relabelFn extra σ
  invFun := relabelFn extra σ.symm
  left_inv := by
    rintro ⟨p | s, k⟩
    · rfl
    · by_cases hk : k.val = 0
      · simp only [relabelFn, hk, if_pos]
      · simp only [relabelFn, hk, if_false]
        exact congrArg (fun a : S => (⟨Sum.inr a, k⟩ : ActualVertex (S := S) extra))
          (σ.symm_apply_apply s)
  right_inv := by
    rintro ⟨p | s, k⟩
    · rfl
    · by_cases hk : k.val = 0
      · simp only [relabelFn, hk, if_pos]
      · simp only [relabelFn, hk, if_false]
        exact congrArg (fun a : S => (⟨Sum.inr a, k⟩ : ActualVertex (S := S) extra))
          (σ.apply_symm_apply s)

/-- The actual matching between the two fixed endpoint label sets. -/
def endpointMap (σ : Perm S) : Perm (P ⊕ S) := (Equiv.refl P).sumCongr σ

@[simp] theorem relabel_head (extra : P → ℕ) (σ : Perm S) (i : P ⊕ S) :
    relabel extra σ (head (extended extra) i) = head (extended extra) i := by
  cases i <;> rfl

@[simp] theorem relabel_tail (extra : P → ℕ) (σ : Perm S) (i : P ⊕ S) :
    relabel extra σ (tail (extended extra) i) =
      tail (extended extra) (endpointMap σ i) := by
  cases i <;> simp [relabel, relabelFn, tail, extended, endpointMap] <;> rfl

@[simp] theorem relabel_color (extra : P → ℕ) (σ : Perm S) (v : ActualVertex (S := S) extra) :
    pathColor (extended extra) (relabel extra σ v) = pathColor (extended extra) v := by
  obtain ⟨p | s, k⟩ := v
  · rfl
  · change pathColor (extended extra) (relabelFn extra σ ⟨Sum.inr s, k⟩) = _
    dsimp only [relabelFn]
    split <;> rfl

@[simp] theorem relabel_symm_color (extra : P → ℕ) (σ : Perm S) (v : ActualVertex (S := S) extra) :
    pathColor (extended extra) ((relabel extra σ).symm v) = pathColor (extended extra) v := by
  have hh := relabel_color extra σ ((relabel extra σ).symm v)
  simpa using hh.symm

/-- Inverse cyclic order makes the physical joining edge head(u)--tail(M(τ(u))). -/
def actualSuccessor (extra : P → ℕ) (σ : Perm S) (τ : Perm (P ⊕ S)) :
    Perm (ActualVertex (S := S) extra) :=
  (relabel extra σ).permCongr (successor (extended extra) τ.symm)

def actualGraph (extra : P → ℕ) (σ : Perm S) (τ : Perm (P ⊕ S)) :
    SimpleGraph (ActualVertex (S := S) extra) := cycleGraph (actualSuccessor extra σ τ)

theorem adj_relabel (extra : P → ℕ) (σ : Perm S) (τ : Perm (P ⊕ S))
    (v w : ActualVertex (S := S) extra) :
    (actualGraph extra σ τ).Adj (relabel extra σ v) (relabel extra σ w) ↔
      (completionGraph (extended extra) τ.symm).Adj v w := by
  simp [actualGraph, actualSuccessor, completionGraph, cycleGraph]

theorem actualSuccessor_isCycleOn [Finite P] [Finite S]
    (extra : P → ℕ) (σ : Perm S) (τ : Perm (P ⊕ S))
    (hτ : τ.IsCycleOn Set.univ) : (actualSuccessor extra σ τ).IsCycleOn Set.univ := by
  apply Erdos585.PathContraction.isCycleOn_relabel
  apply successor_isCycleOn
  exact hτ.inv

theorem extended_even (extra : P → ℕ) (heven : ∀ p, extra p % 2 = 0) :
    ∀ i : P ⊕ S, extended extra i % 2 = 0 := by
  intro i
  cases i with
  | inl p => exact heven p
  | inr s => rfl

theorem actualSuccessor_changes_color (extra : P → ℕ) (σ : Perm S) (τ : Perm (P ⊕ S))
    (heven : ∀ p, extra p % 2 = 0) (v : ActualVertex (S := S) extra) :
    pathColor (extended extra) (actualSuccessor extra σ τ v) ≠ pathColor (extended extra) v := by
  have hh := successor_changes_color (extended extra) τ.symm (extended_even extra heven)
    ((relabel extra σ).symm v)
  simpa only [actualSuccessor, Equiv.permCongr_apply, relabel_color,
    relabel_symm_color] using hh

theorem actualGraph_isBipartite (extra : P → ℕ) (σ : Perm S) (τ : Perm (P ⊕ S))
    (heven : ∀ p, extra p % 2 = 0) : (actualGraph extra σ τ).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (pathColor (extended extra)) ?_⟩
  intro v w h
  obtain ⟨_, h | h⟩ := h
  · subst w
    exact (actualSuccessor_changes_color extra σ τ heven v).symm
  · subst v
    exact actualSuccessor_changes_color extra σ τ heven w

theorem relabeled_internal (extra : P → ℕ) (σ : Perm S) (τ : Perm (P ⊕ S))
    (i : P ⊕ S) (k : ℕ) (hk : k < extended extra i + 1) :
    (actualGraph extra σ τ).Adj
      (relabel extra σ ⟨i, ⟨k, by omega⟩⟩)
      (relabel extra σ ⟨i, ⟨k + 1, by omega⟩⟩) := by
  apply (adj_relabel extra σ τ _ _).mpr
  refine ⟨?_, Or.inl (successor_internal (extended extra) τ.symm i k hk)⟩
  intro h
  have hh := congrArg (fun v : ActualVertex (S := S) extra => v.2.val) h
  simp only at hh
  omega

theorem original_edge (extra : P → ℕ) (σ : Perm S) (τ : Perm (P ⊕ S))
    (p : P) (k : ℕ) (hk : k < extra p + 1) :
    (actualGraph extra σ τ).Adj
      ⟨Sum.inl p, ⟨k, by change k < extra p + 2; omega⟩⟩
      ⟨Sum.inl p, ⟨k + 1, by change k + 1 < extra p + 2; omega⟩⟩ := by
  exact relabeled_internal extra σ τ (Sum.inl p) k hk

theorem pairing_edge (extra : P → ℕ) (σ : Perm S) (τ : Perm (P ⊕ S)) (s : S) :
    (actualGraph extra σ τ).Adj
      (head (extended extra) (Sum.inr s)) (tail (extended extra) (Sum.inr (σ s))) := by
  have hh := relabeled_internal extra σ τ (Sum.inr s) 0 (by simp [extended])
  change (actualGraph extra σ τ).Adj
    (relabel extra σ (head (extended extra) (Sum.inr s)))
    (relabel extra σ (tail (extended extra) (Sum.inr s))) at hh
  rw [relabel_head, relabel_tail] at hh
  exact hh

theorem joining_edge (extra : P → ℕ) (σ : Perm S) (τ : Perm (P ⊕ S)) (u : P ⊕ S) :
    (actualGraph extra σ τ).Adj (head (extended extra) u)
      (tail (extended extra) (endpointMap σ (τ u))) := by
  have hh : (completionGraph (extended extra) τ.symm).Adj
      (tail (extended extra) (τ u)) (head (extended extra) u) := by
    refine ⟨?_, Or.inl ?_⟩
    · intro h
      have he := congrArg (fun v : ActualVertex (S := S) extra => v.2.val) h
      simp only [tail, head, Fin.val_last, Fin.val_zero] at he
      omega
    · simpa using successor_tail (extended extra) τ.symm (τ u)
  have hh' := (adj_relabel extra σ τ _ _).mpr hh
  simpa only [relabel_head, relabel_tail] using hh'.symm

/-- A labeled generated joining unit, not arbitrary adjacency in the union graph. -/
def JoiningUnit (σ : Perm S) (τ : Perm (P ⊕ S)) (u v : P ⊕ S) : Prop :=
  endpointMap σ (τ u) = v

theorem joiningUnit_is_edge (extra : P → ℕ) (σ : Perm S) (τ : Perm (P ⊕ S))
    (u v : P ⊕ S) (h : JoiningUnit σ τ u v) :
    (actualGraph extra σ τ).Adj (head (extended extra) u) (tail (extended extra) v) := by
  rw [← h]
  exact joining_edge extra σ τ u

/-- At least two path components give enough distinct actual vertices for a simple cycle. -/
theorem actualVertex_card [Fintype P] [Fintype S] [Nontrivial (P ⊕ S)]
    (extra : P → ℕ) : 3 ≤ Fintype.card (ActualVertex (S := S) extra) := by
  apply Nat.succ_le_of_lt
  rw [Fintype.two_lt_card_iff]
  obtain ⟨i, j, hij⟩ := exists_pair_ne (P ⊕ S)
  refine ⟨head (extended extra) i, tail (extended extra) i, head (extended extra) j, ?_, ?_, ?_⟩
  · intro h
    have hh := congrArg (fun v : ActualVertex (S := S) extra => v.2.val) h
    simp only [head, tail, Fin.val_zero, Fin.val_last] at hh
    omega
  · exact fun h => hij (congrArg Sigma.fst h)
  · exact fun h => hij (congrArg Sigma.fst h)

/-- On fixed actual vertices, one spanning simple cycle retains every original
path edge, chosen pairing edge, and generated joining edge. -/
theorem fixed_vertex_completion [Fintype P] [Fintype S] [Nontrivial (P ⊕ S)]
    (extra : P → ℕ) (σ : Perm S) (τ : Perm (P ⊕ S))
    (hτ : τ.IsCycleOn Set.univ) (heven : ∀ p, extra p % 2 = 0)
    (x : ActualVertex (S := S) extra) :
    (actualGraph extra σ τ).IsBipartite ∧
    ∃ w : (actualGraph extra σ τ).Walk x x, w.IsCycle ∧ (∀ v, v ∈ w.support) ∧
      (∀ p k (hk : k < extra p + 1), w.toSubgraph.Adj
        ⟨Sum.inl p, ⟨k, by change k < extra p + 2; omega⟩⟩
        ⟨Sum.inl p, ⟨k + 1, by change k + 1 < extra p + 2; omega⟩⟩) ∧
      (∀ s, w.toSubgraph.Adj (head (extended extra) (Sum.inr s))
        (tail (extended extra) (Sum.inr (σ s)))) ∧
      (∀ u v, JoiningUnit σ τ u v → w.toSubgraph.Adj
        (head (extended extra) u) (tail (extended extra) v)) := by
  obtain ⟨w, hw, hs, he⟩ := cycleGraph_spanning_cycle (actualSuccessor extra σ τ)
    (actualSuccessor_isCycleOn extra σ τ hτ) (actualVertex_card extra) x
  exact ⟨actualGraph_isBipartite extra σ τ heven, w, hw, hs,
    fun p k hk => he _ _ (original_edge extra σ τ p k hk),
    fun s => he _ _ (pairing_edge extra σ τ s),
    fun u v h => he _ _ (joiningUnit_is_edge extra σ τ u v h)⟩

/-- The joint estimate for the generated physical units, with the endpoint map
constructed from the isolated pairing rather than supplied as a hypothesis. -/
theorem uniform_generated_units_le {J : Type*} [Fintype J]
    {P S : J → Type*} [∀ i, Fintype (P i)] [∀ i, Fintype (S i)]
    [∀ i, DecidableEq (P i)] [∀ i, DecidableEq (S i)]
    (r : ∀ i, Finset (S i × S i))
    (t : ∀ i, Finset ((P i ⊕ S i) × (P i ⊕ S i)))
    (b : ℕ) (s c : J → ℕ) (hb : 4 ≤ b) (hc : ∀ i, 1 ≤ c i)
    (hS : ∀ i, Fintype.card (S i) = s i * b)
    (hI : ∀ i, Fintype.card (P i ⊕ S i) = c i * b)
    (hunits : 2 * (∑ i, ((r i).card + (t i).card)) ≤ b) :
    (Nat.card {z : ∀ i, Erdos585.ConditionalCompletionCount.ColorSample (S i) (P i ⊕ S i) //
      ∀ i, (∀ a ∈ r i, (z i).1 a.1 = a.2) ∧
        ∀ a ∈ t i, JoiningUnit (z i).1 (z i).2.1 a.1 a.2} : ℚ) /
      (Nat.card (∀ i, Erdos585.ConditionalCompletionCount.ColorSample (S i) (P i ⊕ S i)) : ℚ) ≤
    ∏ i, ((2 / (s i : ℚ)) / (b : ℚ)) ^ (r i).card *
      ((2 / (c i : ℚ)) / (b : ℚ)) ^ (t i).card := by
  exact Erdos585.ConditionalCompletionCount.uniformEndpointColorsProbability_le_blockWeights
    r t (fun _ σ => endpointMap σ) b s c hb hc hS hI hunits

end Erdos585.FixedVertexCompletion
