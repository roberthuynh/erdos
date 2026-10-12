import Openmath.Proofs.PaperSupport.Cascade29.Seed
import Openmath.Proofs.PaperSupport.Cascade29.Capacity
import Openmath.Proofs.PaperSupport.Cascade29.DataExtend

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Cascade29

theorem seed_sixes_empty : sixes seedData = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hd := (mem_filter.mp hv).2
  change seedGraph.degree v = 6 at hd
  have hl := seed_seven v
  omega

/-- First birth has no six to promote; its actual eligible opposite shore suffices. -/
theorem seed_neighbors_properties :
    (normalNeighbors seedData).card = 6 ∧
      normalNeighbors seedData ⊆ seedRight ∧
      (∀ v ∈ normalNeighbors seedData, seedGraph.degree v < 12) := by
  have hshape : seedLeft.card < seedRight.card := by
    rw [seedLeft_card, seedRight_card]
    omega
  have hop : opposite seedData = seedRight := by simp [opposite, hshape]
  have hel : 6 ≤ (eligible seedData).card := by
    rw [eligible, hop]
    decide
  have hN : normalNeighbors seedData =
      BqCircularLowerFamily.leastNeighbors 6 (eligible seedData) seedLabels.label := by
    simp [normalNeighbors, seed_sixes_empty]
  rw [hN]
  have hsub : BqCircularLowerFamily.leastNeighbors 6 (eligible seedData) seedLabels.label ⊆
      eligible seedData := filter_subset _ _
  refine ⟨BqCircularLowerFamily.leastNeighbors_card 6 _ _ seedLabels.injective hel,
    ?_, ?_⟩
  · intro v hv
    have h := (mem_filter.mp (hsub hv)).1
    rwa [hop] at h
  · intro v hv
    exact (mem_filter.mp (hsub hv)).2

theorem first_normal : Normal (state 1) := by
  obtain ⟨hN,hsub,hload⟩ := seed_neighbors_properties
  have hleft : nextLeft seedData = true := by
    unfold nextLeft
    change decide (seedLeft.card < seedRight.card) = true
    rw [seedLeft_card, seedRight_card]
    decide
  change Normal (seedData.add (nextLeft seedData) (normalNeighbors seedData))
  rw [hleft]
  refine ⟨data_add_good seedData seed_good true _ hN hsub hload, ?_⟩
  refine ⟨none, ?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
  · exact (BqCircularLowerFamily.degree_none seedGraph _).trans hN
  · intro v hv
    cases v with
    | none => exact (hv rfl).elim
    | some v =>
      rw [BqCircularLowerFamily.degree_some]
      have hl : 7 ≤ seedData.graph.degree v := seed_seven v
      split_ifs <;> omega
  · change Fintype.card SeedVertex + 1 = Fintype.card (Option SeedVertex)
    rw [Fintype.card_option]
  · change (insert none (seedLeft.image some)).card = (seedRight.image some).card
    rw [card_insert_of_notMem (by simp),
      card_image_of_injective _ (Option.some_injective SeedVertex),
      card_image_of_injective _ (Option.some_injective SeedVertex),
      seedLeft_card,seedRight_card]
  · exact mem_insert_self _ _

end Erdos585.Cascade29
