import FactorMatching.Extract
import FactorMatching.Lift

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open SimpleGraph

namespace Erdos585.FactorMatching

universe u
variable {V : Type u} [Fintype V]

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem finite_gadgetVertex (q : ℕ) (G : SimpleGraph V) : Finite (Vertex q G) := by
  classical
  infer_instance

theorem card_gadgetVertex (q : ℕ) (G : SimpleGraph V) :
    Nat.card (Vertex q G) = Nat.card V * q + Nat.card G.Dart := by
  classical
  simp only [Vertex, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin]

theorem factor_matching_iff (q : ℕ) (G : SimpleGraph V) (_hq : 0 < q) :
    SpanningFactor q G ↔ ∃ M : (gadget q G).Subgraph, M.IsPerfectMatching := by
  constructor
  · exact matching_of_factor
  · rintro ⟨M, hM⟩
    exact factor_of_matching M hM

theorem spanning_q_factor_iff_matching (q : ℕ) (G : SimpleGraph V) (hq : 0 < q) :
    (∃ H : G.Subgraph, H.IsSpanning ∧ H.coe.IsRegularOfDegree q) ↔
      ∃ M : (gadget q G).Subgraph, M.IsPerfectMatching :=
  factor_matching_iff q G hq

theorem matching_iff_original_univ_factor (q : ℕ) (G : SimpleGraph V) (hq : 0 < q) :
    (∃ M : (gadget q G).Subgraph, M.IsPerfectMatching) ↔
      ∃ H : G.Subgraph, H.verts = (↑(Finset.univ : Finset V) : Set V) ∧
        H.coe.IsRegularOfDegree q := by
  rw [← spanning_q_factor_iff_matching q G hq]
  simp only [Finset.coe_univ, Subgraph.isSpanning_iff]

theorem nonempty_original_factor_of_matching [Nonempty V] (q : ℕ) (G : SimpleGraph V)
    (hq : 0 < q) (h : ∃ M : (gadget q G).Subgraph, M.IsPerfectMatching) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  obtain ⟨H, hs, hr⟩ := (spanning_q_factor_iff_matching q G hq).mpr h
  obtain ⟨v⟩ := ‹Nonempty V›
  exact ⟨H, ⟨v, hs v⟩, hr⟩

theorem empty_original_factor_and_matching [IsEmpty V] (q : ℕ) (G : SimpleGraph V)
    (hq : 0 < q) : SpanningFactor q G ∧
      ∃ M : (gadget q G).Subgraph, M.IsPerfectMatching := by
  have hf : SpanningFactor q G := (sameCarrier_iff q G).mpr
    ⟨G, le_rfl, fun v => isEmptyElim v⟩
  exact ⟨hf, (factor_matching_iff q G hq).mp hf⟩

end Erdos585.FactorMatching

set_option pp.universes true in
#check @Erdos585.FactorMatching.spanning_q_factor_iff_matching
set_option pp.universes true in
#check @Erdos585.FactorMatching.matching_iff_original_univ_factor
#print axioms Erdos585.FactorMatching.spanning_q_factor_iff_matching
#print axioms Erdos585.FactorMatching.matching_iff_original_univ_factor
#print axioms Erdos585.FactorMatching.nonempty_original_factor_of_matching
#print axioms Erdos585.FactorMatching.empty_original_factor_and_matching
