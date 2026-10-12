import Openmath.Proofs.PaperSupport.Cascade29.Capacity
import Openmath.Proofs.PaperSupport.Cascade29.DataExtend

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Cascade29

theorem normal_step (D : GraphData) (h : Normal D) (hn : 25 ≤ Fintype.card D.Carrier) :
    Normal (step D) := by
  obtain ⟨hN, hsub, hload, hS⟩ := normalNeighbors_properties D h
  obtain ⟨z, hz, hothers, hlast, hshape⟩ := h.unique_last
  have hzS : z ∈ sixes D := by
    obtain ⟨w, hw, hwothers, hwOpp, hwcard, hwS⟩ := normal_opposite D h
    have hzw : z = w := by
      by_contra hzw
      have := hwothers z hzw
      omega
    simpa [hwS, hzw]
  have hzN : z ∈ normalNeighbors D := hS hzS
  unfold step nextLeft nextNeighbors
  rcases hshape with ⟨heq, hzL⟩ | ⟨heq, hzR⟩
  · have hlt : ¬ D.left.card < D.right.card := by omega
    simp only [hlt, decide_false]
    exact normal_add_right D h.good _ hN (by simpa [opposite, hlt] using hsub)
      hload z hz hzN hothers heq
  · have hlt : D.left.card < D.right.card := by omega
    simp only [hlt, decide_true]
    exact normal_add_left D h.good _ hN (by simpa [opposite, hlt] using hsub)
      hload z hz hzN hothers heq

/-- Original labels of the non-six selected vertices precede every omitted eligible other. -/
theorem normal_least_others (D : GraphData) (h : Normal D)
    (v w : D.Carrier) (hv : v ∈ normalNeighbors D) (hvS : v ∉ sixes D)
    (hw : w ∈ eligible D \ sixes D) (hwn : w ∉ normalNeighbors D) :
    D.labels.label v ≤ D.labels.label w := by
  have hvL : v ∈ BqCircularLowerFamily.leastNeighbors (6-(sixes D).card)
      (eligible D \ sixes D) D.labels.label := (mem_union.mp hv).resolve_left hvS
  have hwL : w ∉ BqCircularLowerFamily.leastNeighbors (6-(sixes D).card)
      (eligible D \ sixes D) D.labels.label := by
    intro hwL
    exact hwn (mem_union.mpr (Or.inr hwL))
  exact BqCircularLowerFamily.leastNeighbors_le_omitted _ _ _ v w hvL hw hwL

end Erdos585.Cascade29
