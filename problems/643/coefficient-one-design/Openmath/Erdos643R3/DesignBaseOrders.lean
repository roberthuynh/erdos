import Openmath.Erdos643R3.DesignConstruction

/-! Explicit degenerate base designs; these assert no general residue-class existence. -/
namespace Erdos643Design
open Finset

theorem design_one : (∅ : Finset (Finset (Fin 1))).IsBlockDesign 2 5 := by
  refine ⟨by simp [Finset.IsUniform], ?_⟩
  intro S hS
  have hle : S.card ≤ 1 := by
    calc
      S.card ≤ (univ : Finset (Fin 1)).card := card_le_card (subset_univ S)
      _ = 1 := by simp
  omega

theorem design_five : ({univ} : Finset (Finset (Fin 5))).IsBlockDesign 2 5 := by
  refine ⟨?_, ?_⟩
  · intro e he
    have heq : e = univ := mem_singleton.mp he
    simp [heq]
  · intro S _
    refine ⟨univ, ⟨by simp, subset_univ S⟩, ?_⟩
    intro e he
    exact mem_singleton.mp he.1

theorem design_exists_one : ∃ B : Finset (Finset (Fin 1)), B.IsBlockDesign 2 5 :=
  ⟨∅, design_one⟩

theorem design_exists_five : ∃ B : Finset (Finset (Fin 5)), B.IsBlockDesign 2 5 :=
  ⟨{univ}, design_five⟩

theorem design_lower_bound_one :
    (1 : ℕ).choose 2 ≤ Hypergraph.extremalNumber 1 3 (fun H => ¬ H.HasRepeatedDisjointUnion) :=
  design_lower_bound 1 ∅ design_one

theorem design_lower_bound_five :
    (5 : ℕ).choose 2 ≤ Hypergraph.extremalNumber 5 3 (fun H => ¬ H.HasRepeatedDisjointUnion) :=
  design_lower_bound 5 {univ} design_five

end Erdos643Design
