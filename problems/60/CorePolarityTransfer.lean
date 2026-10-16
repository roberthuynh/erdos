import ActualCore
import OutsideMissing
import EmbeddedCoreCompletion

/-! The original-host core contracts imply the first-excess edit bound once
an actual embedding of the retained good rows is supplied. This module does
not assert that such an embedding exists. -/
namespace Erdos60.Localization
open scoped Classical
variable {P L : Type*} [Membership P L] [Fintype P] 
  [Fintype L] [Configuration.ProjectivePlane P L]

theorem ActualCoreData.polarity_edit_bound
    {G : SimpleGraph P} {q : ℕ} {T : ℝ} (C : ActualCoreData G q T)
    (π : Geometry.Polarity (P := P) (L := L))
    (ho : Configuration.ProjectivePlane.order P L = q)
    (hcontain : C.retained ≤ π.graph)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hZ : (Counting.cycleCount G : ℝ) < T*q) :
    ((G.edgeFinset \ π.graph.edgeFinset).card : ℝ) < 2*T := by
  have hc : ∀ v ∉ C.core, ∀ w, G.Adj v w → π.graph.Adj v w := by
    intro v hv w hvw
    exact hcontain ((C.outsideAdj v w hv).mpr hvw)
  have hm : ∀ v ∉ C.core, q ≤ G.degree v := by
    intro v hv
    obtain ⟨hd,hor⟩ := C.outsideDegree v hv
    omega
  have hd : ((Finset.univ.filter (fun v : P => G.degree v ≤ q)).card : ℝ) ≤
      (q : ℝ)-1+20*T := by
    simpa only [Core.deficientVertices] using C.originalDeficient
  apply π.first_excess_edit_bound G C.core T
  all_goals first | exact hc | exact C.size | simpa only [ho] using heven |
    simpa only [ho] using hm | simpa only [ho] using hd |
    simpa only [ho] using hq | exact hT | simpa only [ho] using hr |
    simpa only [ho] using hZ

theorem ActualCoreData.embedded_rows_give_nearby_polarity
    {G : SimpleGraph P} {q : ℕ} {T : ℝ} (C : ActualCoreData G q T)
    (hq : (10 : ℝ)^16 ≤ q) (hT : 1 ≤ T) (hr : T ≤ (q : ℝ)/10^8)
    (heven : Even q) (hN : Fintype.card P = q^2+q+1)
    (hZ : (Counting.cycleCount G : ℝ) < T*q)
    (ho : Configuration.ProjectivePlane.order P L = q)
    (row : P → L)
    (hrow : ∀ a ∈ Completion.goodFullVertices C.retained q
        (Finset.univ.filter (fun v : P => C.retained.degree v ≤ q)),
      ∀ x, x ∈ row a ↔ C.retained.Adj a x) :
    ∃ π : Geometry.Polarity (P := P) (L := L),
      C.retained ≤ π.graph ∧ ((G.edgeFinset \ π.graph.edgeFinset).card : ℝ) < 2*T := by
  have hs : 1000*(Finset.univ.filter (fun v : P => C.retained.degree v ≤ q)).card ≤
      1001*q := by
    simpa only [Core.deficientVertices] using C.completionDeficient
  obtain ⟨π,hπ⟩ := Completion.embedded_good_rows_complete_graph C.retained
    C.noFourCycle q heven C.orderLarge hN C.completionMinimum C.cap hs C.completionDeep
    ho row hrow
  exact ⟨π,hπ,C.polarity_edit_bound π ho hπ hq hT hr heven hZ⟩

#print axioms ActualCoreData.polarity_edit_bound
#print axioms ActualCoreData.embedded_rows_give_nearby_polarity
end Erdos60.Localization
