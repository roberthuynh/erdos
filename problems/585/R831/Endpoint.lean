import R831.Assembly
import R801.Main
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.H5BareR831
universe u
variable {V : Type u} [Fintype V]

/-- The literal core supplier is proved by the actual R801 factor theorem. -/
theorem core_factor_supplier (q : ℕ) : CoreFactorSupplier.{u} q := by
  intro W inst K L R F host
  exact AllHBalancedSelectorR801.balanced_core_factor host

/-- Bare original h5 endpoint with no additional mathematical premise.
Every factor uses actual original edges.  -/
theorem bare_h5 (q : ℕ) (hq : 36864 ≤ q) (G : SimpleGraph V)
    (bipartite : G.IsBipartite) (cap : G.maxDegree ≤ 2*q-2)
    (order : 2*q ≤ Fintype.card V)
    (edges : (q-1)*Fintype.card V-(5*q-58) ≤ G.edgeSet.ncard) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  exact bare_h5_of_core_factor q hq (core_factor_supplier q) G bipartite cap order edges

/-- Literal n-vertex caller. No critical graph, floor, core, pins, cuts, or supplier is assumed. -/
theorem bare_h5_original_caller (q n : ℕ) (large : 36864 ≤ q)
    (G : SimpleGraph V) (card : Fintype.card V=n)
    (bipartite : G.IsBipartite) (cap : ∀ v : V, G.degree v ≤ 2*q-2)
    (order : 2*q ≤ n) (edges : (q-1)*n-(5*q-58) ≤ G.edgeSet.ncard) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  exact bare_h5_raw_of_core_factor q n large (core_factor_supplier q) G card bipartite cap order edges

#check bare_h5_original_caller
#print axioms core_factor_supplier
#print axioms bare_h5
#print axioms bare_h5_original_caller
end Erdos585.H5BareR831
