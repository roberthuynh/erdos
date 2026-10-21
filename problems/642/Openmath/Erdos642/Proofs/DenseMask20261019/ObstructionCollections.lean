import Openmath.Erdos642.Proofs.DenseMask20261019.FixedObstruction
import Openmath.Erdos642.Proofs.DenseMask20261019.ComponentEntropy

namespace Erdos642.DenseMask20261019.ObstructionCollections
open SimpleGraph Finset
open Erdos642.CampaignFe72210b
open ComponentObstruction ComponentEntropy AvoidanceOrder FixedObstruction
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def componentCollection (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q B : Finset V) : Finset (mask G Q).ConnectedComponent := by
  classical
  exact B.image (mask G Q).connectedComponentMk

theorem collection_meets (G : SimpleGraph V) [DecidableRel G.Adj] (Q B : Finset V)
    (hBQ : B ⊆ Q) {c : (mask G Q).ConnectedComponent}
    (hc : c ∈ componentCollection G Q B) : ∃ v ∈ B, v ∈ Q ∧ v ∈ c.supp := by
  classical
  obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hc
  exact ⟨v, hv, hBQ hv, he⟩

theorem component_subset_seed (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q B : Finset V) (hBQ : B ⊆ Q) (hfix : componentUnion G Q B = B)
    {c : (mask G Q).ConnectedComponent} (hc : c ∈ componentCollection G Q B) :
    componentVertices G Q c ⊆ B := by
  obtain ⟨v, hvB, hvQ, hvc⟩ := collection_meets G Q B hBQ hc
  intro w hw
  obtain ⟨hwQ, hwc⟩ := (mem_componentVertices G Q c w).mp hw
  rw [← hfix]
  apply (mem_componentUnion G Q B w).mpr
  exact ⟨hwQ, v, Finset.mem_inter.mpr ⟨hvQ, hvB⟩,
    ConnectedComponent.exact (hvc.trans hwc.symm)⟩

theorem union_collection_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q B : Finset V) (hBQ : B ⊆ Q) (hfix : componentUnion G Q B = B) :
    unionVertices G Q (componentCollection G Q B) = B := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨c, hc, hv⟩ := Finset.mem_biUnion.mp hv
    exact component_subset_seed G Q B hBQ hfix hc hv
  · intro v hv
    apply Finset.mem_biUnion.mpr
    exact ⟨(mask G Q).connectedComponentMk v, Finset.mem_image.mpr ⟨v, hv, rfl⟩,
      (mem_componentVertices G Q _ v).mpr ⟨hBQ hv, rfl⟩⟩

theorem seed_subset_reached (G : SimpleGraph V) [DecidableRel G.Adj]
    (B M : Finset V) (hBM : B ⊆ M) : B ⊆ componentUnion G M B := by
  intro v hv
  exact (mem_componentUnion G M B v).mpr
    ⟨hBM hv, v, Finset.mem_inter.mpr ⟨hBM hv, hv⟩, Reachable.rfl⟩

/-- Extract the actual finite Q-component collection, preserving original union and reached vertices. -/
theorem obstruction_collection (G : SimpleGraph V) [DecidableRel G.Adj]
    (C rho beta k : ℝ) (Q M : Finset V) (hk : 0 ≤ k)
    (h : Obstruction G C rho beta k Q M) :
    ∃ F : Finset (mask G Q).ConnectedComponent,
      F ∈ collections G Q (orderLower C (rho/64)) k ∧
      unionVertices G Q F ⊆ Q ∧
      componentUnion G Q (unionVertices G Q F) = unionVertices G Q F ∧
      k/5 ≤ ((unionVertices G Q F).card : ℝ) ∧
      ((unionVertices G Q F).card : ℝ) ≤ 9*k/17 ∧
      ((componentUnion G M (unionVertices G Q F)).card : ℝ) ≤ 9*k/17 ∧
      componentUnion G M (unionVertices G Q F) ⊆ closedNeighborhood G (unionVertices G Q F) := by
  classical
  obtain ⟨hQM, hdegree, hcap, horder, B, hBQ, hfix, hlo, hreach, hclose⟩ := h
  let F := componentCollection G Q B
  have he : unionVertices G Q F = B := union_collection_eq G Q B hBQ hfix
  have hsub := seed_subset_reached G B M (hBQ.trans hQM)
  have hcard : (B.card : ℝ) ≤ 9*k/17 := by
    exact le_trans (by exact_mod_cast Finset.card_le_card hsub) hreach
  refine ⟨F, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_, ?_⟩
    · intro c hc
      obtain ⟨v, hvB, hvQ, hvc⟩ := collection_meets G Q B hBQ hc
      exact horder c ⟨v, hvQ, hvc⟩
    · rw [he]
      linarith
  · rw [he]
    exact ⟨hBQ, hfix, hlo, hcard, hreach, hclose⟩

/-- A positive obstruction contains an actual nonempty Q-component whose order is at most k. -/
theorem obstruction_order_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (C rho beta k : ℝ) (Q M : Finset V) (hk : 0 < k)
    (h : Obstruction G C rho beta k Q M) : orderLower C (rho/64) ≤ k := by
  classical
  obtain ⟨hQM, hdegree, hcap, horder, B, hBQ, hfix, hlo, hreach, hclose⟩ := h
  have hBpos : 0 < B.card := by
    have : (0 : ℝ) < B.card := by linarith
    exact_mod_cast this
  obtain ⟨v, hvB⟩ := Finset.card_pos.mp hBpos
  let c := (mask G Q).connectedComponentMk v
  have hc : c ∈ componentCollection G Q B := Finset.mem_image.mpr ⟨v, hvB, rfl⟩
  have hmin := horder c ⟨v, hBQ hvB, rfl⟩
  have hsub := component_subset_seed G Q B hBQ hfix hc
  have hBsub := seed_subset_reached G B M (hBQ.trans hQM)
  have hsize : ((componentVertices G Q c).card : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hsizeB : (B.card : ℝ) ≤ ((componentUnion G M B).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hBsub
  linarith

end Erdos642.DenseMask20261019.ObstructionCollections
