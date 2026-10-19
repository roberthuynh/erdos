import Openmath.Erdos643R3.AnchorComplete
import Openmath.Erdos643R3.CoefficientOneAssembly
import Openmath.Erdos643R3.CoefficientOneUpstream
import Openmath.Erdos643R3.StarAsymptotic
import Openmath.Erdos643R3.StarMatching
import Openmath.Erdos643R3.DesignConstruction

/-!
# Unconditional coefficient-one theorem and upstream consequences

The anchor theorem closes the one mathematical hypothesis of the conditional
G1/redistribution assembly. The imported upstream extremal number and forcing
function then receive their finite upper bounds. The star supplies the lower
bound and the asymptotic equivalence follows by squeezing.
-/

set_option autoImplicit false

namespace Erdos643R3.CoefficientOneFinal
open scoped Asymptotics Topology

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- Exact finite coefficient-one bound for every avoiding 3-uniform host. -/
theorem coefficient_one : CoefficientOne.CoefficientOneAt V := by
  apply CoefficientOneAssembly.coefficient_one_of_G3hPrimeAt V
  intro H hH hav
  exact AnchorComplete.g3hPrime hH hav

/-- The recovered charge inequality gives the stronger manuscript potential bound. -/
theorem phi_nonpos (H : Finset (Finset V))
    (hH : Identity.Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    L1Top.Phi H ≤ 0 :=
  (CPrimeMain.endpoint_of_G3hPrime hH hav
    (AnchorComplete.g3hPrime hH hav)).1

/-- The manuscript's shadow-plus-co-link inequality before its cardinal corollary. -/
theorem shadow_colink_bound (H : Finset (Finset V))
    (hH : Identity.Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    2 * (H.card : ℚ) ≤
      ((Identity.shadow H).card : ℚ) + ((Identity.colink H).card : ℚ) := by
  have h := phi_nonpos V H hH hav
  unfold L1Top.Phi at h
  linarith

/-- Upper bound in the actual imported upstream extremal-number vocabulary. -/
theorem extremal_three_le_choose_two (n : ℕ) :
    Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) ≤
      n.choose 2 :=
  CoefficientOneUpstream.extremal_three_le_choose_two n (coefficient_one (Fin n))

/-- The exact forcing threshold ex₃(n)+1 has the coefficient-one upper bound. -/
theorem forcing_three_le_choose_two_add_one (n : ℕ) :
    Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) + 1 ≤
      n.choose 2 + 1 :=
  CoefficientOneUpstream.forcing_three_le_choose_two_add_one n (coefficient_one (Fin n))

/-- The full finite squeeze uses the unconditional star construction. -/
theorem extremal_three_bounds (n : ℕ) :
    (n-1).choose 2 ≤
      Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) ∧
    Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) ≤
      n.choose 2 :=
  ⟨StarAsymptotic.star_lower_bound n, extremal_three_le_choose_two n⟩

/-- The stronger finite star-plus-matching construction, for every n≥1. -/
theorem extremal_three_lower_matching (n : ℕ) (hn : 1 ≤ n) :
    (n-1).choose 2 + (n-1) / 3 ≤
      Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) :=
  StarMatching.lower_bound n hn

/-- Exact equality when an actual 2-(n,5,1) block design is supplied. -/
theorem extremal_eq_of_supplied_design (n : ℕ)
    (B : Finset (Finset (Fin n))) (hB : B.IsBlockDesign 2 5) :
    Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) =
      n.choose 2 :=
  Erdos643Design.extremal_eq_of_design n B hB (extremal_three_le_choose_two n)

/-- The true upstream extremal-number ratio tends to one. -/
theorem extremal_ratio_tendsto_one :
    Filter.Tendsto
      (fun n : ℕ => (Hypergraph.extremalNumber n 3
        (fun H => ¬ H.HasRepeatedDisjointUnion) : ℝ) / (n.choose 2 : ℝ))
      Filter.atTop (nhds 1) :=
  StarAsymptotic.ex3_ratio_tendsto_one extremal_three_le_choose_two

/-- The true forcing threshold has asymptotic coefficient one. -/
theorem forcing_isEquivalent :
    (fun n : ℕ => ((Hypergraph.extremalNumber n 3
      (fun H => ¬ H.HasRepeatedDisjointUnion)+1 : ℕ) : ℝ))
      ~[Filter.atTop] (fun n : ℕ => (n.choose (3-1) : ℝ)) :=
  StarAsymptotic.forcing_isEquivalent extremal_three_le_choose_two

end Erdos643R3.CoefficientOneFinal
