import Openmath.Proofs.FixedVertexCompletion
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Odd-path completion on the original host

The encoding bijection is constructed from disjoint actual graph paths and
isolated vertices covering the host. All colors may use the same host and shores.
No spanning cycle or encoding equivalence is supplied as an input hypothesis.
-/

namespace Erdos585.CommonHostCompletion

open Equiv SimpleGraph
open Erdos585.PathCycleCompletion Erdos585.FixedVertexCompletion

variable {V P S : Type*}

/-- An explicit supplied path forest, with every original edge accounted for. -/
structure PathData (G : SimpleGraph V) (χ : V → Fin 2) (P S : Type*) where
  extra : P → ℕ
  even : ∀ p, extra p % 2 = 0
  start : P → V
  finish : P → V
  walk : ∀ p, G.Walk (start p) (finish p)
  isPath : ∀ p, (walk p).IsPath
  length : ∀ p, (walk p).length = extra p + 1
  disjoint : ∀ p q, p ≠ q → ∀ v, v ∈ (walk p).support → v ∉ (walk q).support
  isolated : S × Fin 2 → V
  isolated_injective : Function.Injective isolated
  outside : ∀ s ε p, isolated (s, ε) ∉ (walk p).support
  covers : ∀ v, (∃ p, v ∈ (walk p).support) ∨ ∃ s ε, isolated (s, ε) = v
  edge_coverage : ∀ {v w}, G.Adj v w → ∃ p k, k < (walk p).length ∧
    ((v = (walk p).getVert k ∧ w = (walk p).getVert (k + 1)) ∨
     (w = (walk p).getVert k ∧ v = (walk p).getVert (k + 1)))
  proper : ∀ {v w}, G.Adj v w → χ v ≠ χ w
  start_color : ∀ p, χ (start p) = 0
  isolated_color : ∀ s ε, χ (isolated (s, ε)) = ε

variable {G : SimpleGraph V} {χ : V → Fin 2}

namespace PathData

variable (D : PathData G χ P S)

def decode : ActualVertex (S := S) D.extra → V
  | ⟨Sum.inl p, k⟩ => (D.walk p).getVert k.val
  | ⟨Sum.inr s, k⟩ => D.isolated (s, k)

theorem decode_injective : Function.Injective D.decode := by
  rintro ⟨p | s, k⟩ ⟨q | t, l⟩ h
  · change (D.walk p).getVert k.val = (D.walk q).getVert l.val at h
    by_cases hpq : p = q
    · subst q
      have hk : k.val = l.val := (D.isPath p).getVert_injOn
        (by change k.val ≤ (D.walk p).length; rw [D.length]; have := k.isLt; change k.val < D.extra p + 2 at this; omega)
        (by change l.val ≤ (D.walk p).length; rw [D.length]; have := l.isLt; change l.val < D.extra p + 2 at this; omega) h
      have hkl : k = l := Fin.ext hk
      subst l
      rfl
    · exact False.elim (D.disjoint p q hpq _ ((D.walk p).getVert_mem_support k.val)
        (by rw [h]; exact (D.walk q).getVert_mem_support l.val))
  · change (D.walk p).getVert k.val = D.isolated (t, l) at h
    exact False.elim (D.outside t l p (by rw [← h]; exact (D.walk p).getVert_mem_support k.val))
  · change D.isolated (s, k) = (D.walk q).getVert l.val at h
    exact False.elim (D.outside s k q (by rw [h]; exact (D.walk q).getVert_mem_support l.val))
  · change D.isolated (s, k) = D.isolated (t, l) at h
    have hh := D.isolated_injective h
    have hst : s = t := congrArg Prod.fst hh
    subst t
    have hkl : k = l := congrArg Prod.snd hh
    subst l
    rfl

theorem decode_surjective : Function.Surjective D.decode := by
  intro v
  rcases D.covers v with ⟨p, hp⟩ | ⟨s, ε, h⟩
  · obtain ⟨k, hk, hle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hp
    refine ⟨⟨Sum.inl p, ⟨k, ?_⟩⟩, hk⟩
    change k < D.extra p + 2
    rw [D.length] at hle
    omega
  · exact ⟨⟨Sum.inr s, ε⟩, h⟩

/-- The original-host encoding is constructed from the input paths. -/
noncomputable def toEquiv : ActualVertex (S := S) D.extra ≃ V :=
  Equiv.ofBijective D.decode ⟨D.decode_injective, D.decode_surjective⟩

theorem toEquiv_apply (v : ActualVertex (S := S) D.extra) : D.toEquiv v = D.decode v := rfl

                                                                                     
theorem walk_color (p : P) (k : ℕ) (hk : k ≤ (D.walk p).length) :
    χ ((D.walk p).getVert k) = ⟨k % 2, Nat.mod_lt _ (by decide)⟩ := by
  induction k with
  | zero => simpa using D.start_color p
  | succ k ih =>
    have hprev := ih (by omega)
    have hneq := D.proper ((D.walk p).adj_getVert_succ (by omega : k < (D.walk p).length))
    have hv : (χ ((D.walk p).getVert k)).val ≠ (χ ((D.walk p).getVert (k + 1))).val :=
      fun h => hneq (Fin.ext h)
    have hval := congrArg Fin.val hprev
    have hn := (χ ((D.walk p).getVert (k + 1))).isLt
    apply Fin.ext
    change (χ ((D.walk p).getVert (k + 1))).val = (k + 1) % 2
    change (χ ((D.walk p).getVert k)).val = k % 2 at hval
    omega

theorem toEquiv_color (v : ActualVertex (S := S) D.extra) :
    χ (D.toEquiv v) = pathColor (extended D.extra) v := by
  obtain ⟨p | s, k⟩ := v
  · exact D.walk_color p k.val (by
      rw [D.length]
      have := k.isLt
      change k.val < D.extra p + 2 at this
      omega)
  · change Fin 2 at k
    change χ (D.isolated (s, k)) = ⟨k.val % 2, _⟩
    rw [D.isolated_color]
    apply Fin.ext
    exact (Nat.mod_eq_of_lt k.isLt).symm

@[simp] theorem toEquiv_symm_color (v : V) :
    pathColor (extended D.extra) (D.toEquiv.symm v) = χ v := by
  have hh := D.toEquiv_color (D.toEquiv.symm v)
  simpa only [Equiv.apply_symm_apply] using hh.symm

noncomputable def hostSuccessor (σ : Perm S) (τ : Perm (P ⊕ S)) : Perm V :=
  D.toEquiv.permCongr (actualSuccessor D.extra σ τ)

noncomputable def hostGraph (σ : Perm S) (τ : Perm (P ⊕ S)) : SimpleGraph V :=
  cycleGraph (D.hostSuccessor σ τ)

theorem host_adj_decode (σ : Perm S) (τ : Perm (P ⊕ S))
    (v w : ActualVertex (S := S) D.extra) :
    (D.hostGraph σ τ).Adj (D.toEquiv v) (D.toEquiv w) ↔
      (actualGraph D.extra σ τ).Adj v w := by
  simp [hostGraph, hostSuccessor, actualGraph, cycleGraph, Equiv.permCongr_apply]

/-- The transported successor changes the one common original shore map. -/
theorem hostSuccessor_changes_color (σ : Perm S) (τ : Perm (P ⊕ S)) (v : V) :
    χ (D.hostSuccessor σ τ v) ≠ χ v := by
  have hh := actualSuccessor_changes_color D.extra σ τ D.even (D.toEquiv.symm v)
  simpa only [hostSuccessor, Equiv.permCongr_apply, toEquiv_color, toEquiv_symm_color] using hh

theorem hostGraph_isBipartite (σ : Perm S) (τ : Perm (P ⊕ S)) :
    (D.hostGraph σ τ).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk χ ?_⟩
  intro v w h
  obtain ⟨_, h | h⟩ := h
  · subst w
    exact (D.hostSuccessor_changes_color σ τ v).symm
  · subst v
    exact D.hostSuccessor_changes_color σ τ w

theorem original_le_host (σ : Perm S) (τ : Perm (P ⊕ S)) : G ≤ D.hostGraph σ τ := by
  intro v w hvw
  obtain ⟨p, k, hk, h | h⟩ := D.edge_coverage hvw
  all_goals
    have hk' : k < D.extra p + 1 := by simpa only [D.length] using hk
    have he := (D.host_adj_decode σ τ _ _).mpr (original_edge D.extra σ τ p k hk')
  · rcases h with ⟨rfl, rfl⟩
    exact he
  · rcases h with ⟨rfl, rfl⟩
    exact he.symm

theorem host_pairing_edge (σ : Perm S) (τ : Perm (P ⊕ S)) (s : S) :
    (D.hostGraph σ τ).Adj (D.isolated (s, 0)) (D.isolated (σ s, 1)) := by
  exact (D.host_adj_decode σ τ _ _).mpr (pairing_edge D.extra σ τ s)

theorem host_joining_edge (σ : Perm S) (τ : Perm (P ⊕ S))
    (u v : P ⊕ S) (h : JoiningUnit σ τ u v) :
    (D.hostGraph σ τ).Adj (D.toEquiv (head (extended D.extra) u))
      (D.toEquiv (tail (extended D.extra) v)) :=
  (D.host_adj_decode σ τ _ _).mpr (joiningUnit_is_edge D.extra σ τ u v h)

/-- Complete the supplied original graph paths on their original common host. -/
theorem forest_completion [Fintype V] [Fintype P] [Fintype S] [Nontrivial (P ⊕ S)]
    (σ : Perm S) (τ : Perm (P ⊕ S)) (hτ : τ.IsCycleOn Set.univ) (x : V) :
    (D.hostGraph σ τ).IsBipartite ∧
    ∃ w : (D.hostGraph σ τ).Walk x x, w.IsCycle ∧ (∀ v, v ∈ w.support) ∧
      (∀ v z, G.Adj v z → w.toSubgraph.Adj v z) ∧
      (∀ s, w.toSubgraph.Adj (D.isolated (s, 0)) (D.isolated (σ s, 1))) ∧
      (∀ u v, JoiningUnit σ τ u v → w.toSubgraph.Adj
        (D.toEquiv (head (extended D.extra) u)) (D.toEquiv (tail (extended D.extra) v))) := by
  have hcycle : (D.hostSuccessor σ τ).IsCycleOn Set.univ :=
    Erdos585.PathContraction.isCycleOn_relabel D.toEquiv _
      (actualSuccessor_isCycleOn D.extra σ τ hτ)
  have hcard : 3 ≤ Fintype.card V := by
    rw [← Fintype.card_congr D.toEquiv]
    exact actualVertex_card D.extra
  obtain ⟨w, hw, hs, he⟩ := cycleGraph_spanning_cycle (D.hostSuccessor σ τ) hcycle hcard x
  exact ⟨D.hostGraph_isBipartite σ τ, w, hw, hs,
    fun v z h => he _ _ (D.original_le_host σ τ h),
    fun s => he _ _ (D.host_pairing_edge σ τ s),
    fun u v h => he _ _ (D.host_joining_edge σ τ u v h)⟩

end PathData

end Erdos585.CommonHostCompletion
