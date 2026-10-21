import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
import Openmath.Erdos643R3.CoefficientOne

/-!
# Actual upstream extremal-number bridge for the coefficient-one target

This imports the pinned upstream `Hypergraph.extremalNumber`,
`Finset.IsUniform`, and `Finset.HasRepeatedDisjointUnion` definitions.
The upper bounds below are conditional on `CoefficientOneAt (Fin n)`;
this module does not prove that proposition.
-/

set_option autoImplicit false

namespace Erdos643R3
namespace CoefficientOneUpstream

open Finset

/-- The upstream repeated-disjoint-union predicate is the local four-distinct-edge predicate. -/
theorem repeated_iff_forbidden {V : Type*} [DecidableEq V]
    (H : Finset (Finset V)) :
    H.HasRepeatedDisjointUnion ↔ Erdos643.HypergraphBasics.Forbidden H := by
  constructor
  · rintro ⟨A, hA, B, hB, C, hC, D, hD, hAB, hCD, hu, h1, h2, h3, h4, h5, h6⟩
    exact ⟨A, hA, B, hB, C, hC, D, hD, ⟨h1, h3, h4, h5, h6, h2⟩, hAB, hCD, hu⟩
  · rintro ⟨A, hA, B, hB, C, hC, D, hD, ⟨h1, h3, h4, h5, h6, h2⟩, hAB, hCD, hu⟩
    exact ⟨A, hA, B, hB, C, hC, D, hD, hAB, hCD, hu, h1, h2, h3, h4, h5, h6⟩

/-- A uniformity bridge for the genuine upstream predicate. -/
theorem uniform_three_iff {V : Type*} [DecidableEq V]
    (H : Finset (Finset V)) : H.IsUniform 3 ↔ Identity.Uniform H := Iff.rfl

/-- The genuine upstream extremal number is bounded when the local exact theorem is supplied. -/
theorem extremal_three_le_choose_two (n : ℕ)
    (hmain : CoefficientOne.CoefficientOneAt (Fin n)) :
    Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) ≤
      n.choose 2 := by
  unfold Hypergraph.extremalNumber
  refine Finset.sup_induction (p := fun m => m ≤ n.choose 2) (by simp)
    (fun a ha b hb => by omega) ?_
  intro H hmem
  simp only [Finset.mem_filter, Finset.mem_powerset] at hmem
  have hu : Identity.Uniform H := by
    intro e he
    exact (Finset.mem_powersetCard.mp (hmem.1 he)).2
  have hav : ¬ Erdos643.HypergraphBasics.Forbidden H := by
    intro hf
    exact hmem.2 ((repeated_iff_forbidden H).mpr hf)
  have h := hmain H hu hav
  simpa only [Fintype.card_fin] using h

/-- The forcing threshold `f(n;3) = ex_3(n) + 1` has coefficient one. -/
theorem forcing_three_le_choose_two_add_one (n : ℕ)
    (hmain : CoefficientOne.CoefficientOneAt (Fin n)) :
    Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) + 1 ≤
      n.choose 2 + 1 := by
  have h := extremal_three_le_choose_two n hmain
  omega

end CoefficientOneUpstream
end Erdos643R3
