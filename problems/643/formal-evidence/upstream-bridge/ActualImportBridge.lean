import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
import Openmath.Erdos643R3.FCBridge

set_option autoImplicit false

namespace Erdos643R3.ActualImportBridge

theorem repeated_iff_forbidden {V : Type*} [DecidableEq V]
    (H : Finset (Finset V)) :
    H.HasRepeatedDisjointUnion ↔ Erdos643.HypergraphBasics.Forbidden H := by
  change Erdos643R3.FCBridge.FC.HasRepeatedDisjointUnion H ↔
    Erdos643.HypergraphBasics.Forbidden H
  exact Erdos643R3.FCBridge.hasRepeatedDisjointUnion_iff_forbidden H

theorem uniform_three_iff {V : Type*} [DecidableEq V]
    (H : Finset (Finset V)) :
    H.IsUniform 3 ↔ Erdos643R3.Identity.Uniform H := by
  exact Erdos643R3.FCBridge.isUniform_three_iff H

theorem ex3_le_24_23 (n : ℕ) :
    23 * Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) ≤
      24 * n.choose 2 := by
  change 23 * Erdos643R3.FCBridge.FC.extremalNumber n 3
    (fun H => ¬ Erdos643R3.FCBridge.FC.HasRepeatedDisjointUnion H) ≤
      24 * n.choose 2
  exact Erdos643R3.FCBridge.ex3_le_24_23 n

theorem f_le_24_23_real (n : ℕ) :
    ((Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) + 1 : ℕ) : ℝ) ≤
      24 / 23 * (n.choose (3 - 1) : ℝ) + 1 := by
  change ((Erdos643R3.FCBridge.FC.extremalNumber n 3
    (fun H => ¬ Erdos643R3.FCBridge.FC.HasRepeatedDisjointUnion H) + 1 : ℕ) : ℝ) ≤
      24 / 23 * (n.choose (3 - 1) : ℝ) + 1
  exact Erdos643R3.FCBridge.f_le_24_23_real n

end Erdos643R3.ActualImportBridge
