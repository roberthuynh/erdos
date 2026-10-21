import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Bipartite

   
                                                 

                                                                          
                                                                            
                                                                           
                                                                            
                                                                        
  

namespace Erdos585.PathCycleCompletion

open Equiv SimpleGraph

variable {I : Type*}

abbrev Vertex (extra : I → ℕ) := Σ i, Fin (extra i + 2)

def head (extra : I → ℕ) (i : I) : Vertex extra := ⟨i, 0⟩

def tail (extra : I → ℕ) (i : I) : Vertex extra := ⟨i, Fin.last (extra i + 1)⟩

def moveHeadFn (extra : I → ℕ) (τ : Perm I) (v : Vertex extra) : Vertex extra :=
  if v.2 = 0 then head extra (τ v.1) else v

theorem moveHeadFn_head (extra : I → ℕ) (τ : Perm I) (i : I) :
    moveHeadFn extra τ (head extra i) = head extra (τ i) := rfl

theorem moveHeadFn_nonzero (extra : I → ℕ) (τ : Perm I) (v : Vertex extra)
    (hv : v.2 ≠ 0) : moveHeadFn extra τ v = v := if_neg hv

/-- Permute the first vertices, fixing every other vertex. -/
def moveHeads (extra : I → ℕ) (τ : Perm I) : Perm (Vertex extra) where
  toFun := moveHeadFn extra τ
  invFun := moveHeadFn extra τ.symm
  left_inv := by
    rintro ⟨i, k⟩
    by_cases hk : k = 0
    · subst k
      change moveHeadFn extra τ.symm (moveHeadFn extra τ (head extra i)) = _
      rw [moveHeadFn_head, moveHeadFn_head, Equiv.symm_apply_apply]
      rfl
    · rw [moveHeadFn_nonzero extra τ _ hk, moveHeadFn_nonzero extra τ.symm _ hk]
  right_inv := by
    rintro ⟨i, k⟩
    by_cases hk : k = 0
    · subst k
      change moveHeadFn extra τ (moveHeadFn extra τ.symm (head extra i)) = _
      rw [moveHeadFn_head, moveHeadFn_head, Equiv.apply_symm_apply]
      rfl
    · rw [moveHeadFn_nonzero extra τ.symm _ hk, moveHeadFn_nonzero extra τ _ hk]

/-- Walk forward along each path, then jump to the next path in `τ`. -/
def successor (extra : I → ℕ) (τ : Perm I) : Perm (Vertex extra) :=
  moveHeads extra τ * Equiv.sigmaCongrRight (fun i => finRotate (extra i + 2))

theorem successor_internal (extra : I → ℕ) (τ : Perm I) (i : I)
    (k : ℕ) (hk : k < extra i + 1) :
    successor extra τ ⟨i, ⟨k, by omega⟩⟩ = ⟨i, ⟨k + 1, by omega⟩⟩ := by
  change moveHeads extra τ ⟨i, finRotate (extra i + 2) ⟨k, by omega⟩⟩ = _
  rw [finRotate_of_lt hk]
  change moveHeadFn extra τ ⟨i, ⟨k + 1, by omega⟩⟩ = ⟨i, ⟨k + 1, by omega⟩⟩
  apply moveHeadFn_nonzero extra τ
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_zero] at hh
  omega

theorem successor_tail (extra : I → ℕ) (τ : Perm I) (i : I) :
    successor extra τ (tail extra i) = head extra (τ i) := by
  change moveHeads extra τ ⟨i, finRotate (extra i + 2) (Fin.last (extra i + 1))⟩ = _
  rw [finRotate_last]
  exact moveHeadFn_head extra τ i

/-- Every original vertex is in the successor orbit of its own path's first vertex. -/
theorem sameCycle_within (extra : I → ℕ) (τ : Perm I) (i : I)
    (k : Fin (extra i + 2)) :
    (successor extra τ).SameCycle (head extra i) ⟨i, k⟩ := by
  obtain ⟨k, hk⟩ := k
  induction k with
  | zero => exact Equiv.Perm.SameCycle.rfl
  | succ k ih =>
    have hh := (ih (by omega)).apply_right
    simpa only [successor_internal extra τ i k (by omega)] using hh

/-- Consecutive paths in the prescribed cyclic order belong to the same orbit. -/
theorem sameCycle_next_head (extra : I → ℕ) (τ : Perm I) (i : I) :
    (successor extra τ).SameCycle (head extra i) (head extra (τ i)) := by
  have hh := (sameCycle_within extra τ i (Fin.last (extra i + 1))).apply_right
  change (successor extra τ).SameCycle (head extra i) (successor extra τ (tail extra i)) at hh
  rwa [successor_tail] at hh

/-- A single cyclic endpoint permutation yields one orbit on all actual path vertices. -/
theorem successor_isCycleOn [Finite I] (extra : I → ℕ) (τ : Perm I)
    (hτ : τ.IsCycleOn Set.univ) :
    (successor extra τ).IsCycleOn Set.univ := by
  refine ⟨(successor extra τ).bijective.bijOn_univ, ?_⟩
  rintro ⟨i, k⟩ _ ⟨j, l⟩ _
  obtain ⟨n, hn⟩ := hτ.exists_pow_eq' Set.finite_univ (Set.mem_univ i) (Set.mem_univ j)
  have hpow : ∀ n : ℕ, (successor extra τ).SameCycle
      (head extra i) (head extra ((τ ^ n) i)) := by
    intro n
    induction n with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ n ih =>
      simpa only [pow_succ', Equiv.Perm.mul_apply] using
        ih.trans (sameCycle_next_head extra τ ((τ ^ n) i))
  have hj : (successor extra τ).SameCycle (head extra i) (head extra j) := by
    simpa only [hn] using hpow n
  exact (sameCycle_within extra τ i k).symm.trans
    (hj.trans (sameCycle_within extra τ j l))

section CycleGraph

variable {V : Type*}

/-- The undirected edges of a permutation, with loops removed. -/
def cycleGraph (σ : Perm V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (σ x = y ∨ σ y = x)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem cycleGraph_spanning_cycle [Fintype V] (σ : Perm V)
    (hσ : σ.IsCycleOn Set.univ) (hcard : 3 ≤ Fintype.card V) (x : V) :
    ∃ p : (cycleGraph σ).Walk x x, p.IsCycle ∧
      (∀ v, v ∈ p.support) ∧
      (∀ v w, (cycleGraph σ).Adj v w → p.toSubgraph.Adj v w) := by
  classical
  have hf : σ.IsCycleOn (↑(Finset.univ : Finset V) : Set V) := by simpa using hσ
  have hfix : ∀ v, σ v ≠ v := by
    intro v hv
    have hd := (hf.pow_apply_eq (Finset.mem_univ v) (n := 1)).mp (by simpa using hv)
    have := Nat.le_of_dvd (by decide : 0 < 1) hd
    simp only [Finset.card_univ] at this
    omega
  have htwo : ∀ v, σ v ≠ σ.symm v := by
    intro v hv
    have hp : (σ ^ 2) v = v := by
      simpa only [pow_two, Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using congrArg σ hv
    have hd := (hf.pow_apply_eq (Finset.mem_univ v)).mp hp
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    simp only [Finset.card_univ] at this
    omega
  have hadj : ∀ v, (cycleGraph σ).Adj v (σ v) :=
    fun v => ⟨(hfix v).symm, Or.inl rfl⟩
  have hn : ∀ v, (cycleGraph σ).neighborSet v = {σ v, σ.symm v} := by
    intro v
    ext w
    change (v ≠ w ∧ (σ v = w ∨ σ w = v)) ↔ w = σ v ∨ w = σ.symm v
    constructor
    · rintro ⟨_, h | h⟩
      · exact Or.inl h.symm
      · exact Or.inr (σ.eq_symm_apply.mpr h)
    · rintro (rfl | rfl)
      · exact hadj v
      · exact ⟨by intro h; exact hfix v (by simpa only [← h] using σ.apply_symm_apply v),
          Or.inr (σ.apply_symm_apply v)⟩
  have hcyc : (cycleGraph σ).IsCycles := by
    intro v _
    rw [hn]
    exact Set.ncard_pair (htwo v)
  have hall : ∀ v, (cycleGraph σ).Reachable x v := by
    intro v
    obtain ⟨n, rfl⟩ := hσ.exists_pow_eq' Set.finite_univ (Set.mem_univ x) (Set.mem_univ v)
    induction n with
    | zero => exact SimpleGraph.Reachable.rfl
    | succ n ih =>
      simpa only [pow_succ', Equiv.Perm.mul_apply] using
        ih.trans (hadj ((σ ^ n) x)).reachable
  let c := (cycleGraph σ).connectedComponentMk x
  have hc : ∀ v, v ∈ c.supp := fun v => ConnectedComponent.sound (hall v).symm
  obtain ⟨p, hp, hs⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (hc x) ⟨σ x, hadj x⟩
  have hv : ∀ v, v ∈ p.toSubgraph.verts := by intro v; rw [hs]; exact hc v
  exact ⟨p, hp, fun v => p.mem_verts_toSubgraph.mp (hv v),
    fun v w h => (hp.adj_toSubgraph_iff_of_isCycles hcyc (hv v) w).mpr h⟩

end CycleGraph

/-- The actual completion graph. Its edges are exactly the path edges and cyclic joins. -/
def completionGraph (extra : I → ℕ) (τ : Perm I) : SimpleGraph (Vertex extra) :=
  cycleGraph (successor extra τ)

/-- Joining at least two nontrivial disjoint paths in one cyclic order gives a
spanning simple cycle containing every original path edge. -/
theorem completion_spanning_cycle [Finite I] [Nontrivial I]
    (extra : I → ℕ) (τ : Perm I) (hτ : τ.IsCycleOn Set.univ) (x : Vertex extra) :
    ∃ p : (completionGraph extra τ).Walk x x, p.IsCycle ∧
      (∀ v, v ∈ p.support) ∧
      (∀ i k (hk : k < extra i + 1),
        p.toSubgraph.Adj ⟨i, ⟨k, by omega⟩⟩ ⟨i, ⟨k + 1, by omega⟩⟩) := by
  classical
  let _ := Fintype.ofFinite I
  have hcard : 3 ≤ Fintype.card (Vertex extra) := by
    apply Nat.succ_le_of_lt
    rw [Fintype.two_lt_card_iff]
    obtain ⟨i, j, hij⟩ := exists_pair_ne I
    refine ⟨head extra i, tail extra i, head extra j, ?_, ?_, ?_⟩
    · intro h
      have hh := congrArg (fun v : Vertex extra => v.2.val) h
      simp only [head, tail, Fin.val_zero, Fin.val_last] at hh
      omega
    · exact fun h => hij (congrArg Sigma.fst h)
    · exact fun h => hij (congrArg Sigma.fst h)
  obtain ⟨p, hp, hs, he⟩ := cycleGraph_spanning_cycle
    (successor extra τ) (successor_isCycleOn extra τ hτ) hcard x
  refine ⟨p, hp, hs, ?_⟩
  intro i k hk
  apply he
  refine ⟨?_, Or.inl (successor_internal extra τ i k hk)⟩
  intro h
  have hh := congrArg (fun v : Vertex extra => v.2.val) h
  simp only at hh
  omega

/-- The fixed alternating shore label along each prescribed path. -/
def pathColor (extra : I → ℕ) (v : Vertex extra) : Fin 2 :=
  ⟨v.2.val % 2, Nat.mod_lt _ (by decide)⟩

theorem successor_changes_color (extra : I → ℕ) (τ : Perm I)
    (heven : ∀ i, extra i % 2 = 0) (v : Vertex extra) :
    pathColor extra (successor extra τ v) ≠ pathColor extra v := by
  obtain ⟨i, k, hk⟩ := v
  by_cases hlast : k < extra i + 1
  · rw [successor_internal extra τ i k hlast]
    intro h
    have hh := congrArg Fin.val h
    change (k + 1) % 2 = k % 2 at hh
    omega
  · have hk' : k = extra i + 1 := by omega
    subst k
    change pathColor extra (successor extra τ (tail extra i)) ≠ _
    rw [successor_tail]
    intro h
    have hh := congrArg Fin.val h
    change 0 % 2 = (extra i + 1) % 2 at hh
    have hi := heven i
    omega

/-- Odd prescribed path lengths make every cyclic join cross the fixed shores. -/
theorem completion_isBipartite (extra : I → ℕ) (τ : Perm I)
    (heven : ∀ i, extra i % 2 = 0) : (completionGraph extra τ).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (pathColor extra) ?_⟩
  intro v w h
  obtain ⟨_, h | h⟩ := h
  · subst w
    exact (successor_changes_color extra τ heven v).symm
  · subst v
    exact successor_changes_color extra τ heven w

                                                                             
                                                                              
theorem odd_path_completion [Finite I] [Nontrivial I]
    (extra : I → ℕ) (τ : Perm I) (hτ : τ.IsCycleOn Set.univ)
    (heven : ∀ i, extra i % 2 = 0) (x : Vertex extra) :
    (completionGraph extra τ).IsBipartite ∧
    ∃ p : (completionGraph extra τ).Walk x x, p.IsCycle ∧
      (∀ v, v ∈ p.support) ∧
      (∀ i k (hk : k < extra i + 1),
        p.toSubgraph.Adj ⟨i, ⟨k, by omega⟩⟩ ⟨i, ⟨k + 1, by omega⟩⟩) :=
  ⟨completion_isBipartite extra τ heven, completion_spanning_cycle extra τ hτ x⟩

end Erdos585.PathCycleCompletion
