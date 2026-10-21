import Erdos1017.Basic

/-! Aggregate a finite weighted family of actual cliques into an exact partition.
The family may repeat the same clique. Edge loads are preserved separately. -/
namespace Erdos1017
open scoped BigOperators
variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

noncomputable def aggregateMass (C : Ω → Finset V) (w : Ω → ℝ) (s : Finset V) : ℝ :=
  ∑ x, if C x = s then w x else 0

omit [Fintype V] in
theorem aggregateMass_nonneg (C : Ω → Finset V) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (s : Finset V) : 0 ≤ aggregateMass C w s := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact hw x
  · exact le_rfl

/-- Any observable of the actual vertex set has the same weighted sum after aggregation. -/
theorem aggregate_observable (C : Ω → Finset V) (w : Ω → ℝ) (f : Finset V → ℝ) :
    (∑ s, aggregateMass C w s * f s) = ∑ x, w x * f (C x) := by
  simp only [aggregateMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [ite_mul, zero_mul]
  simp

noncomputable def partitionOfCliqueLaw (G : SimpleGraph V)
    (C : Ω → Finset V) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : ∀ x, w x ≠ 0 → G.IsClique (C x : Set V) ∧ 2 ≤ (C x).card)
    (he : ∀ u v, G.Adj u v →
      ∑ x, (if u ∈ C x ∧ v ∈ C x then w x else 0) = 1) : FractionalPartition G where
  mass := aggregateMass C w
  nonneg := aggregateMass_nonneg C w hw
  supported s h := by
    obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    by_cases hc : C x = s
    · have hwx : w x ≠ 0 := by simpa [hc] using hx
      simpa [hc] using hs x hwx
    · simp [hc] at hx
  edge_load u v huv := by
    have hobs := aggregate_observable C w (fun s => if u ∈ s ∧ v ∈ s then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero] at hobs
    exact hobs.trans (he u v huv)

theorem partitionOfCliqueLaw_cost (G : SimpleGraph V)
    (C : Ω → Finset V) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : ∀ x, w x ≠ 0 → G.IsClique (C x : Set V) ∧ 2 ≤ (C x).card)
    (he : ∀ u v, G.Adj u v →
      ∑ x, (if u ∈ C x ∧ v ∈ C x then w x else 0) = 1) :
    (partitionOfCliqueLaw G C w hw hs he).cost = ∑ x, w x := by
  simpa [FractionalPartition.cost, partitionOfCliqueLaw] using
    aggregate_observable C w (fun _ => 1)

/-- Delete outcomes with fewer than two vertices; such outcomes carry no graph edge. -/
noncomputable def pruneMass (C : Ω → Finset V) (w : Ω → ℝ) (x : Ω) : ℝ :=
  if 2 ≤ (C x).card then w x else 0

omit [Fintype V] in
theorem two_le_card_of_edge {G : SimpleGraph V} {u v : V} (h : G.Adj u v)
    {s : Finset V} (hu : u ∈ s) (hv : v ∈ s) : 2 ≤ s.card := by
  have hsub : ({u,v} : Finset V) ⊆ s := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hu
    · exact hv
  have hcard := Finset.card_le_card hsub
  simpa [h.ne] using hcard

omit [Fintype Ω] in
theorem pruneMass_edge {G : SimpleGraph V} (C : Ω → Finset V) (w : Ω → ℝ)
    {u v : V} (h : G.Adj u v) (x : Ω) :
    (if u ∈ C x ∧ v ∈ C x then pruneMass C w x else 0) =
    (if u ∈ C x ∧ v ∈ C x then w x else 0) := by
  by_cases hm : u ∈ C x ∧ v ∈ C x
  · simp [hm, pruneMass, two_le_card_of_edge h hm.1 hm.2]
  · simp [hm]

/-- A finite law supported on cliques may include empty and singleton outcomes. -/
noncomputable def partitionOfCliqueLawPruned (G : SimpleGraph V)
    (C : Ω → Finset V) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hc : ∀ x, G.IsClique (C x : Set V))
    (he : ∀ u v, G.Adj u v →
      ∑ x, (if u ∈ C x ∧ v ∈ C x then w x else 0) = 1) : FractionalPartition G :=
  partitionOfCliqueLaw G C (pruneMass C w)
    (fun x => by dsimp [pruneMass]; split_ifs; exact hw x; exact le_rfl)
    (fun x hx => by
      refine ⟨hc x, ?_⟩
      by_contra h
      simp [pruneMass, h] at hx)
    (fun u v huv => by simp_rw [pruneMass_edge C w huv]; exact he u v huv)

theorem partitionOfCliqueLawPruned_cost (G : SimpleGraph V)
    (C : Ω → Finset V) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hc : ∀ x, G.IsClique (C x : Set V))
    (he : ∀ u v, G.Adj u v →
      ∑ x, (if u ∈ C x ∧ v ∈ C x then w x else 0) = 1) :
    (partitionOfCliqueLawPruned G C w hw hc he).cost =
      ∑ x, if 2 ≤ (C x).card then w x else 0 := by
  exact partitionOfCliqueLaw_cost _ _ _ _ _ _

end Erdos1017
