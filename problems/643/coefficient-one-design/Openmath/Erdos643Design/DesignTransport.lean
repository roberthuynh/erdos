import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
import Mathlib.Tactic

/-! Equivalence transport of actual finite block designs. -/
set_option autoImplicit false

namespace Erdos643Design.DesignTransport

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- Relabel each block by a bijection of the ground types. -/
def relabel (e : V ≃ W) (H : Finset (Finset V)) : Finset (Finset W) :=
  H.image (fun b => b.map e.toEmbedding)

omit [DecidableEq V] in
/-- Relabeling preserves the number of blocks as well as every block's size. -/
theorem relabel_card (e : V ≃ W) (H : Finset (Finset V)) :
    (relabel e H).card = H.card := by
  apply Finset.card_image_iff.mpr
  intro a _ b _ hab
  exact Finset.map_injective e.toEmbedding hab

omit [DecidableEq V] in
/-- A bijective relabeling preserves the actual upstream t-design property. -/
theorem isBlockDesign_relabel (e : V ≃ W) (H : Finset (Finset V)) (t k : ℕ)
    (hH : H.IsBlockDesign t k) : (relabel e H).IsBlockDesign t k := by
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    rw [Finset.card_map]
    exact hH.1 a ha
  · intro S hS
    have hT : (S.map e.symm.toEmbedding).card = t := by
      rw [Finset.card_map, hS]
    obtain ⟨b, hb, hu⟩ := hH.2 (S.map e.symm.toEmbedding) hT
    refine ⟨b.map e.toEmbedding, ⟨Finset.mem_image.mpr ⟨b,hb.1,rfl⟩, ?_⟩, ?_⟩
    · exact Finset.map_symm_subset.mp hb.2
    · intro c hc
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc.1
      have hdb : d = b := hu d ⟨hd, Finset.map_symm_subset.mpr hc.2⟩
      exact congrArg (fun a => a.map e.toEmbedding) hdb

/-- Relabel a finite ground type by its canonical finite cardinality. -/
noncomputable def toFin [Fintype V] (H : Finset (Finset V)) :
    Finset (Finset (Fin (Fintype.card V))) := relabel (Fintype.equivFin V) H

omit [DecidableEq V] [DecidableEq W] in
/-- A supplied finite design becomes a design on `Fin (card V)`. -/
theorem isBlockDesign_toFin [Fintype V] (H : Finset (Finset V)) (t k : ℕ)
    (hH : H.IsBlockDesign t k) : (toFin H).IsBlockDesign t k :=
  isBlockDesign_relabel (Fintype.equivFin V) H t k hH

end Erdos643Design.DesignTransport
