import Openmath.Proofs.PaperSupport.Cascade29.Invariants
import Openmath.Proofs.PaperSupport.Cascade29.Schedule

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Cascade29
variable {V : Type} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B : Finset V}

/-- Actual opposite-shore slots total at least 29, using the actual bipartite edge sum. -/
theorem opposite_twenty_nine (h : Good G A B) (hab : A.card ≤ B.card) :
    29 ≤ ∑ v ∈ B, (12-G.degree v) := by
  have hcard : A.card+B.card = Fintype.card V := by
    rw [← card_union_of_disjoint h.disjoint, h.cover, card_univ]
  have hcapacity : (∑ v ∈ B, (12-G.degree v))+G.edgeFinset.card = 12*B.card := by
    calc
      _ = (∑ v ∈ B, (12-G.degree v)) + ∑ v ∈ B, G.degree v := by
        rw [SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' h.bipartite]
      _ = ∑ _v ∈ B, 12 := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro v _
        exact Nat.sub_add_cancel (h.degrees v).2
      _ = 12*B.card := by simp [mul_comm]
  have hd := h.density
  rw [← hcard] at hd
  omega

/-- ONE degree-six vertex plus at most four eligible others supplies at most 26 slots. -/
theorem unique_six_capacity (h : Good G A B) (hab : A.card ≤ B.card)
    (z : V) (hzB : z ∈ B) (hz : G.degree z = 6)
    (hothers : ∀ v, v ≠ z → 7 ≤ G.degree v) :
    6 ≤ (B.filter fun v => G.degree v < 12).card := by
  let E := B.filter fun v => G.degree v < 12
  have hzE : z ∈ E := mem_filter.mpr ⟨hzB, by omega⟩
  have hslots : (∑ v ∈ B, (12-G.degree v)) = ∑ v ∈ E, (12-G.degree v) := by
    symm
    apply sum_subset (filter_subset _ _)
    intro v hvB hvE
    have hnot : ¬ G.degree v < 12 := by
      intro hv
      exact hvE (mem_filter.mpr ⟨hvB, hv⟩)
    have hd := (h.degrees v).2
    have heq : G.degree v = 12 := by omega
    simp [heq]
  have hupper : (∑ v ∈ E, (12-G.degree v)) ≤ 6+5*(E.erase z).card := by
    rw [← sum_erase_add _ _ hzE]
    have hother : (∑ v ∈ E.erase z, (12-G.degree v)) ≤ 5*(E.erase z).card := by
      calc
        _ ≤ ∑ _v ∈ E.erase z, 5 := by
          apply sum_le_sum
          intro v hv
          have hvz : v ≠ z := (mem_erase.mp hv).1
          have := hothers v hvz
          omega
        _ = 5*(E.erase z).card := by simp [mul_comm]
    rw [hz]
    omega
  have htwenty_nine := opposite_twenty_nine h hab
  rw [hslots] at htwenty_nine
  have hcard : (E.erase z).card+1=E.card := card_erase_add_one hzE
  change 6 ≤ E.card
  omega

/-- Normal invariant identifies the actual receiving and opposite shores. -/
theorem normal_opposite (D : GraphData) (h : Normal D) :
    ∃ z : D.Carrier, D.graph.degree z = 6 ∧
      (∀ v, v ≠ z → 7 ≤ D.graph.degree v) ∧ z ∈ opposite D ∧
      6 ≤ (eligible D).card ∧ sixes D = {z} := by
  obtain ⟨z, hz, hothers, hlast, hshape⟩ := h.unique_last
  have hzOpp : z ∈ opposite D := by
    rcases hshape with ⟨heq, hzL⟩ | ⟨heq, hzR⟩
    · simp [opposite, heq, hzL]
    · have hlt : D.left.card < D.right.card := by omega
      simp [opposite, hlt, hzR]
  have hcard : 6 ≤ (eligible D).card := by
    unfold eligible opposite
    split_ifs with hlt
    · exact unique_six_capacity h.good (by omega) z (by simpa [opposite, hlt] using hzOpp) hz hothers
    · exact unique_six_capacity h.good.swap (by omega) z (by simpa [opposite, hlt] using hzOpp) hz hothers
  have hsix : sixes D = {z} := by
    ext v
    simp only [sixes, mem_filter, mem_singleton]
    constructor
    · rintro ⟨hvOpp, hv6⟩
      by_contra hv
      have := hothers v hv
      omega
    · rintro rfl
      exact ⟨hzOpp, hz⟩
  exact ⟨z, hz, hothers, hzOpp, hcard, hsix⟩

theorem normalNeighbors_properties (D : GraphData) (h : Normal D) :
    (normalNeighbors D).card = 6 ∧ normalNeighbors D ⊆ opposite D ∧
      (∀ v ∈ normalNeighbors D, D.graph.degree v < 12) ∧
      sixes D ⊆ normalNeighbors D := by
  obtain ⟨z, hz, hothers, hzOpp, hcard, hsix⟩ := normal_opposite D h
  have hzE : z ∈ eligible D := mem_filter.mpr ⟨hzOpp, by omega⟩
  have hSc : (sixes D).card = 1 := by rw [hsix]; simp
  have hSE : sixes D ⊆ eligible D := by rw [hsix]; simpa
  have hrest : 5 ≤ (eligible D \ sixes D).card := by
    have := card_sdiff_add_card_eq_card hSE
    omega
  have hleast : (BqCircularLowerFamily.leastNeighbors (6-(sixes D).card)
      (eligible D \ sixes D) D.labels.label).card = 5 := by
    rw [hSc]
    exact BqCircularLowerFamily.leastNeighbors_card 5 _ _ D.labels.injective hrest
  have hleastsub : BqCircularLowerFamily.leastNeighbors (6-(sixes D).card)
      (eligible D \ sixes D) D.labels.label ⊆ eligible D \ sixes D := filter_subset _ _
  have hdis : Disjoint (sixes D)
      (BqCircularLowerFamily.leastNeighbors (6-(sixes D).card)
        (eligible D \ sixes D) D.labels.label) := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvL
    exact (mem_sdiff.mp (hleastsub hvL)).2 hvS
  have hNE : normalNeighbors D ⊆ eligible D := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact hSE hv
    · exact (mem_sdiff.mp (hleastsub hv)).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [normalNeighbors, card_union_of_disjoint hdis, hleast, hSc]
  · exact hNE.trans (filter_subset _ _)
  · intro v hv
    exact (mem_filter.mp (hNE hv)).2
  · exact subset_union_left

end Erdos585.Cascade29
