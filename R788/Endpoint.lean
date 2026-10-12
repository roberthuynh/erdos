import R788.Assembly
import R783.Main
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.H4BareR788
universe u
variable {V : Type u} [Fintype V]

/-- The R783 factor theorem supplies the literal core factor. -/
theorem core_factor_supplier (q : ℕ) : CoreFactorSupplier.{u} q := by
  intro W inst K L R F host
  exact GeneralSelectorR783.balanced_core_factor host (Or.inr rfl)

/-- Unconditional bare original h4 endpoint. Every factor uses actual original edges. -/
theorem bare_h4 (q : ℕ) (hq : 25600 ≤ q) (G : SimpleGraph V)
    (bipartite : G.IsBipartite) (cap : G.maxDegree ≤ 2*q-2)
    (order : 2*q ≤ Fintype.card V)
    (edges : (q-1)*Fintype.card V-(4*q-44) ≤ G.edgeSet.ncard) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  exact bare_h4_of_core_factor q hq (core_factor_supplier q) G bipartite cap order edges

/-- Literal n-vertex caller. No critical graph, floor, core, pins, cuts, or supplier is assumed. -/
theorem bare_h4_original_caller (q n : ℕ) (large : 25600 ≤ q)
    (G : SimpleGraph V) (card : Fintype.card V=n)
    (bipartite : G.IsBipartite) (cap : ∀ v : V, G.degree v ≤ 2*q-2)
    (order : 2*q ≤ n) (edges : (q-1)*n-(4*q-44) ≤ G.edgeSet.ncard) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  exact bare_h4_raw_of_core_factor q n large (core_factor_supplier q) G card bipartite cap order edges

#print axioms core_factor_supplier
#print axioms bare_h4
#print axioms bare_h4_original_caller
end Erdos585.H4BareR788
