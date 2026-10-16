import Openmath.Proofs.PaperSupport.Cascade29.Types

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Cascade29
variable {V : Type} [DecidableEq V] [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Proved graph properties, kept separate from graph-valued construction data. -/
structure Good (A B : Finset V) : Prop where
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  bipartite : G.IsBipartiteWith ↑A ↑B
  degrees : ∀ v, 6 ≤ G.degree v ∧ G.degree v ≤ 12
  density : G.edgeFinset.card + 29 = 6 * Fintype.card V
  no7 : BqCircularLowerFamily.NoRegular 7 G

theorem Good.swap {A B : Finset V} (h : Good G A B) : Good G B A where
  disjoint := h.disjoint.symm
  cover := by rw [union_comm, h.cover]
  bipartite := h.bipartite.symm
  degrees := h.degrees
  density := h.density
  no7 := h.no7

theorem extend_good {A B : Finset V} (h : Good G A B) (N : Finset V)
    (hNB : N ⊆ B) (hN : N.card = 6)
    (hload : ∀ v ∈ N, G.degree v < 12) :
    Good (BqCircularLowerFamily.extendGraph G N)
      (insert none (A.image some)) (B.image some) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hxA hxB
    cases x with
    | none => simp at hxB
    | some v => exact Finset.disjoint_left.mp h.disjoint (by simpa using hxA) (by simpa using hxB)
  · ext x
    cases x with
    | none => simp
    | some v =>
      have hv : v ∈ A ∪ B := by rw [h.cover]; exact mem_univ _
      simpa using hv
  · refine ⟨?_, ?_⟩
    · rw [disjoint_coe]
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      cases x with
      | none => simp at hxB
      | some v => exact Finset.disjoint_left.mp h.disjoint (by simpa using hxA) (by simpa using hxB)
    · intro x y hxy
      cases x with
      | none =>
        cases y with
        | none => exact hxy.elim
        | some v => exact Or.inl ⟨by simp, by simpa using hNB hxy⟩
      | some v =>
        cases y with
        | none => exact Or.inr ⟨by simpa using hNB hxy, by simp⟩
        | some w => simpa using h.bipartite.mem_of_adj hxy
  · intro x
    cases x with
    | none => simp [hN]
    | some v =>
      rw [BqCircularLowerFamily.degree_some]
      have hd := h.degrees v
      by_cases hv : v ∈ N
      · have hl := hload v hv
        simp [hv]
        omega
      · simp [hv]
        omega
  · rw [BqCircularLowerFamily.edges_extend, hN, Fintype.card_option]
    have := h.density
    omega
  · exact BqCircularLowerFamily.noRegular_extend G N 7 (by omega) hN h.no7

def DataGood (D : GraphData) : Prop := Good D.graph D.left D.right

structure Normal (D : GraphData) : Prop where
  good : DataGood D
  unique_last : ∃ z : D.Carrier, D.graph.degree z = 6 ∧
    (∀ v, v ≠ z → 7 ≤ D.graph.degree v) ∧
    D.labels.label z + 1 = Fintype.card D.Carrier ∧
    ((D.left.card = D.right.card ∧ z ∈ D.left) ∨
      (D.right.card = D.left.card + 1 ∧ z ∈ D.right))

end Erdos585.Cascade29
