import Openmath.Erdos643R3.HypergraphBasics
import Openmath.Erdos643R3.L1Top

/-!
# Exact coefficient-one target and endpoint interface

`CoefficientOneAt V` is the unconditional finite target for uniform triple systems
that avoid four distinct edges forming two disjoint pairs with equal union.

`RecoveryAt V` and `PhiNonposAt V` are named sufficient hypotheses.
The results below establish conditional reductions from them.
-/

set_option autoImplicit false

namespace Erdos643R3
namespace CoefficientOne

open Finset

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- The original finite coefficient-one bound, with the literal forbidden family. -/
def CoefficientOneAt : Prop :=
  ∀ H : Finset (Finset V), Identity.Uniform H →
    ¬ Erdos643.HypergraphBasics.Forbidden H →
    H.card ≤ (Fintype.card V).choose 2

/-- A sufficient redistribution hypothesis on every avoiding uniform triple system. -/
def RecoveryAt : Prop :=
  ∀ H : Finset (Finset V), Identity.Uniform H →
    ¬ Erdos643.HypergraphBasics.Forbidden H →
    ∀ T ∈ H, L1Top.Deficient H T → 0 ≤ L1Top.final H T

/-- A sufficient potential hypothesis for the endpoint. -/
def PhiNonposAt : Prop :=
  ∀ H : Finset (Finset V), Identity.Uniform H →
    ¬ Erdos643.HypergraphBasics.Forbidden H → L1Top.Phi H ≤ 0

omit [Fintype V] [DecidableEq V] in
/-- The two modules use definitionally identical uniformity predicates. -/
theorem uniform_iff_basics (H : Finset (Finset V)) :
    Identity.Uniform H ↔ Erdos643.HypergraphBasics.Uniform H := Iff.rfl

omit [Fintype V] in
/-- Literal avoidance agrees with the four-distinct-edge forbidden predicate. -/
theorem literal_avoidance_iff_not_forbidden (H : Finset (Finset V))
    (hH : Identity.Uniform H) :
    Erdos643.HypergraphBasics.LiteralAvoids H ↔
      ¬ Erdos643.HypergraphBasics.Forbidden H :=
  Erdos643.HypergraphBasics.literalAvoids_iff_not_forbidden
    ((uniform_iff_basics V H).mp hH)

omit [DecidableEq V] in
/-- Every uniform triple system has at most `C(|V|,3)` edges. -/
theorem card_le_choose_three (H : Finset (Finset V)) (hH : Identity.Uniform H) :
    H.card ≤ (Fintype.card V).choose 3 := by
  have hsub : H ⊆ (univ : Finset V).powersetCard 3 := by
    intro T hT
    simp [mem_powersetCard, hH T hT]
  calc
    H.card ≤ ((univ : Finset V).powersetCard 3).card := card_le_card hsub
    _ = (Fintype.card V).choose 3 := by rw [card_powersetCard, card_univ]

/-- The target holds without avoidance for every host of at most five vertices. -/
theorem coefficient_one_small_hosts (hn : Fintype.card V ≤ 5) : CoefficientOneAt V := by
  intro H hH _
  have hcard := card_le_choose_three V H hH
  have hchoose : (Fintype.card V).choose 3 ≤ (Fintype.card V).choose 2 := by
    interval_cases h : Fintype.card V <;> decide
  omega

/-- Exact endpoint reduction from the sufficient global `Φ ≤ 0` hypothesis. -/
theorem coefficient_one_of_phi_nonpos (h : PhiNonposAt V) : CoefficientOneAt V := by
  intro H hH hav
  have hq := L1Top.endpoint_of_Phi_nonpos H (h H hH hav)
  exact_mod_cast hq

/-- Recovery on deficient triples implies the global `Φ ≤ 0` result. -/
theorem phi_nonpos_of_recovery (h : RecoveryAt V) : PhiNonposAt V := by
  intro H hH hav
  exact (L1Top.conditional_endpoint H hH (h H hH hav)).1

/-- The endpoint chain is proved conditionally, with the sufficient hypothesis explicit. -/
theorem coefficient_one_of_recovery (h : RecoveryAt V) : CoefficientOneAt V :=
  coefficient_one_of_phi_nonpos V (phi_nonpos_of_recovery V h)

end CoefficientOne
end Erdos643R3
