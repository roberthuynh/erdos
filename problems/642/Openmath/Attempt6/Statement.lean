import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exact target only. No proof of `OriginalBound6001` is asserted here. -/
namespace Erdos585.Attempt6

/-- Original simple-graph cycles, pairwise edge-disjoint, with identical actual supports. -/
def HasCommonSupportCycles {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (base : Fin k → V) (cycle : ∀ i, G.Walk (base i) (base i)),
    (∀ i, (cycle i).IsCycle) ∧
    (∀ i j, {v | v ∈ (cycle i).support} = {v | v ∈ (cycle j).support}) ∧
    (∀ i j, i ≠ j → List.Disjoint (cycle i).edges (cycle j).edges)

/-- Base-two logarithm, as in the accepted written proof. -/
noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- Exact requested theorem, including fixed k, arbitrary original graph, n>=2,
positive threshold coefficient, and the integer exponent 6001.
This is a proposition definition, not a theorem or formal verification result. -/
def OriginalBound6001 : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ c : ℝ, 0 < c ∧
    ∀ n : ℕ, 2 ≤ n → ∀ G : SimpleGraph (Fin n),
      c * (n : ℝ) * (logTwo (n : ℝ)) ^ 6001 ≤ (G.edgeSet.ncard : ℝ) →
      HasCommonSupportCycles G k

end Erdos585.Attempt6
