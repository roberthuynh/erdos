import FirstExcessSelection
import NearEquality

namespace Erdos60.Geometry
open scoped Classical
variable {P L : Type*} [Membership P L] [Fintype P] [DecidableEq P]
  [Configuration.ProjectivePlane P L] [Finite L]

omit [Finite L] in
/-- Lift the actual first-excess edit bound to the original surplus host. -/
theorem Polarity.surplus_edit_radius
    (π : Polarity (P := P) (L := L)) (G H : SimpleGraph P) (t : ℕ)
    (ht : 1 ≤ t)
    (hq : (10 : ℝ)^16 ≤ Configuration.ProjectivePlane.order P L)
    (hr : (t : ℝ) ≤ (Configuration.ProjectivePlane.order P L : ℝ)/10^8)
    (hHG : H ≤ G)
    (hG : G.edgeFinset.card = Configuration.ProjectivePlane.order P L *
      (Configuration.ProjectivePlane.order P L+1)^2/2+t)
    (hH : H.edgeFinset.card = Configuration.ProjectivePlane.order P L *
      (Configuration.ProjectivePlane.order P L+1)^2/2+1)
    (hj : ((H.edgeFinset \ π.graph.edgeFinset).card : ℝ) < 2*t) :
    (G.edgeFinset \ π.graph.edgeFinset).card < Configuration.ProjectivePlane.order P L-1 := by
  have hl := Transfer.lift_added_edge_count G H π.graph _ t hHG hG hH
  have hjn : (H.edgeFinset \ π.graph.edgeFinset).card < 2*t := by exact_mod_cast hj
  have hqr : 3*(t : ℝ)+2 < (Configuration.ProjectivePlane.order P L : ℝ) := by linarith
  have hqn : 3*t+2 < Configuration.ProjectivePlane.order P L := by exact_mod_cast hqr
  omega

/-- Even-order polarity edge bound discharges the deficit input of transfer. -/
theorem Polarity.nearby_lower_bound
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (t : ℕ)
    (heven : Even (Configuration.ProjectivePlane.order P L))
    (hG : G.edgeFinset.card = Configuration.ProjectivePlane.order P L *
      (Configuration.ProjectivePlane.order P L+1)^2/2+t)
    (hs : (G.edgeFinset \ π.graph.edgeFinset).card ≤ Configuration.ProjectivePlane.order P L-1) :
    t*(Configuration.ProjectivePlane.order P L-1) ≤ Counting.cycleCount G := by
  let M := Configuration.ProjectivePlane.order P L *
      (Configuration.ProjectivePlane.order P L+1)^2/2
  have hc : π.graph.edgeFinset.card ≤ M := π.edge_count_upper heven
  exact π.graph_transfer G M t (M-π.graph.edgeFinset.card) hG (by omega) hs

#print axioms Polarity.surplus_edit_radius
#print axioms Polarity.nearby_lower_bound
end Erdos60.Geometry
