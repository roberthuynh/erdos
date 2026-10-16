import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic

/-! Actual shore signs of a bipartite graph, including finite degree balance. -/

namespace Erdos642.CampaignFe72210b

variable {V : Type*}

/-- The actual real shore sign, positive on the designated first shore. -/
noncomputable def bipartiteSign (s : Set V) (x : V) : ℝ := by
  classical
  exact if x ∈ s then 1 else -1

theorem bipartiteSign_sq (s : Set V) (x : V) : bipartiteSign s x ^ 2 = 1 := by
  classical
  by_cases hx : x ∈ s <;> simp [bipartiteSign, hx]

/-- Each actual edge reverses the constructed sign. Positive degree is not
needed for an edgewise statement. -/
theorem bipartiteSign_flip (G : SimpleGraph V) {s t : Set V}
    (h : G.IsBipartiteWith s t) (x y : V) (hxy : G.Adj x y) :
    bipartiteSign s y = -bipartiteSign s x := by
  classical
  rcases h.mem_of_adj hxy with ⟨hxs, hyt⟩ | ⟨hxt, hys⟩
  · have hyns : y ∉ s := h.disjoint.notMem_of_mem_right hyt
    simp [bipartiteSign, hxs, hyns]
  · have hxns : x ∉ s := h.disjoint.notMem_of_mem_right hxt
    simp [bipartiteSign, hxns, hys]

/-- A bipartite graph supplies a genuine real sign function, rather than a
sign-flip property inserted as a new graph hypothesis. -/
theorem exists_bipartite_sign (G : SimpleGraph V) (h : G.IsBipartite) :
    ∃ σ : V → ℝ, (∀ x, σ x ^ 2 = 1) ∧
      (∀ x y, G.Adj x y → σ y = -σ x) := by
  obtain ⟨s, t, hb⟩ := h.exists_isBipartiteWith
  exact ⟨bipartiteSign s, bipartiteSign_sq s, bipartiteSign_flip G hb⟩

section Finite

variable [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Positive degree removes the isolated vertices that a bipartition witness
is otherwise allowed to omit from both shores. -/
theorem bipartiteWith_covers {s t : Set V} (h : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) (x : V) : x ∈ s ∨ x ∈ t := by
  obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x).mp (hdeg x)
  rcases h.mem_of_adj hxy with hs | ht
  · exact Or.inl hs.1
  · exact Or.inr ht.1

/-- The actual shore sign has zero degree-weighted sum. -/
theorem bipartiteSign_degree_sum {s t : Set V} (h : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) :
    (∑ x : V, bipartiteSign s x * (G.degree x : ℝ)) = 0 := by
  classical
  have hb : G.IsBipartiteWith (s.toFinset : Set V) (t.toFinset : Set V) := by
    simpa using h
  have hbalance : (∑ x ∈ s.toFinset, (G.degree x : ℝ)) =
      ∑ x ∈ t.toFinset, (G.degree x : ℝ) := by
    exact_mod_cast (SimpleGraph.isBipartiteWith_sum_degrees_eq hb)
  have hsfilter : s.toFinset = Finset.univ.filter (fun x : V => x ∈ s) := by
    ext x
    simp
  have htfilter : t.toFinset = Finset.univ.filter (fun x : V => x ∈ t) := by
    ext x
    simp
  simp only [hsfilter, htfilter, Finset.sum_filter] at hbalance
  calc
    (∑ x : V, bipartiteSign s x * (G.degree x : ℝ)) =
        (∑ x : V, if x ∈ s then (G.degree x : ℝ) else 0) -
          ∑ x : V, if x ∈ t then (G.degree x : ℝ) else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rcases bipartiteWith_covers G h hdeg x with hx | hx
      · have hxnt : x ∉ t := h.disjoint.notMem_of_mem_left hx
        simp [bipartiteSign, hx, hxnt]
      · have hxns : x ∉ s := h.disjoint.notMem_of_mem_right hx
        simp [bipartiteSign, hx, hxns]
    _ = 0 := sub_eq_zero.mpr hbalance

end Finite

end Erdos642.CampaignFe72210b
