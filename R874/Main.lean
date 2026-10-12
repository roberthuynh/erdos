import R866.Main
import R874.Numeric
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.R874
universe u

/-- A literal real superlinear deficit forces an actual nonempty regular
selected-edge subgraph of the original finite bipartite graph. -/
theorem superlinear_forcing (q : ℕ) (hq : 2^40 ≤ q)
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hbip : G.IsBipartite)
    (hn : 2*q ≤ Fintype.card V) (hcap : G.maxDegree ≤ 2*q-2)
    (he : ((q:ℝ)-1)*Fintype.card V-(G.edgeSet.ncard:ℝ) ≤
      Real.rpow (q:ℝ) (5/4:ℝ)/512) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  obtain ⟨hh,hcut,hdef⟩ := numeric q hq
  apply R866.every_h_forcing (height q) q hh hcut G hbip hn hcap
  exact_mod_cast he.trans hdef

#print axioms superlinear_forcing
end Erdos585.R874
