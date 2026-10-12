import Openmath.Proofs.PaperSupport.BqMain
import Openmath.Proofs.PaperSupport.BqOrderFeasible

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Erdos585.BqMinimumSupport
universe u
open scoped Classical in
def MinimumSupportEndpoint : Prop :=
  ∀ (q : ℕ), 5 ≤ q → ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    G.IsBipartite → G.maxDegree ≤ 2 * q - 2 → 2 ≤ Fintype.card V →
    (q - 1) * Fintype.card V - q ≤ G.edgeSet.ncard →
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧
      4 * q - 6 ≤ H.verts.ncard
end Erdos585.BqMinimumSupport
