import Openmath.Erdos643Design.DesignPencil
import Openmath.Erdos643Design.UniformPartitionCoordinates
import Openmath.Erdos643Design.DesignTransport

/-! Normalization of an actual pencil into canonical shared-point coordinates.
The partition and its number of groups are derived from the supplied design. -/
set_option autoImplicit false

namespace Erdos643Design.NormalizedPencil
open Finset
variable {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G]

def groupBlock {m : ℕ} (i : Fin m) : Finset (Option (Fin m × Fin 4)) :=
  insert none (univ.image (fun a : Fin 4 => some (i,a)))

/-- The actual pencil supplies the partition certificate required by the coordinates theorem. -/
noncomputable def pencilPartition (D : Finset (Finset V))
    (hD : D.IsBlockDesign 2 5) (p : V) :
    UniformPartitionCoordinates.Partition (G := ↥(DesignPencil.groups D p)) p where
  group := fun i => i.val
  disjoint := by
    intro i j hij
    apply DesignPencil.groups_pairwise_disjoint D hD p i.property j.property
    intro heq
    exact hij (Subtype.ext heq)
  card := fun i => DesignPencil.group_card D hD p i.property
  cover := by
    calc
      _ = (DesignPencil.groups D p).biUnion id := by
        ext v
        simp
      _ = _ := DesignPencil.groups_union D hD p

/-- Relabel group indices while leaving the four internal coordinates fixed. -/
noncomputable def indexedCoordinates {p : V} (P : UniformPartitionCoordinates.Partition (G := G) p)
    {m : ℕ} (eG : G ≃ Fin m) : V ≃ Option (Fin m × Fin 4) :=
  P.coordinates.trans (Equiv.optionCongr (Equiv.prodCongr eG (Equiv.refl (Fin 4))))

@[simp] theorem indexedCoordinates_point {p : V}
    (P : UniformPartitionCoordinates.Partition (G := G) p) {m : ℕ} (eG : G ≃ Fin m) :
    indexedCoordinates P eG p = none := by
  simp [indexedCoordinates]

theorem indexedCoordinates_group {p : V}
    (P : UniformPartitionCoordinates.Partition (G := G) p) {m : ℕ} (eG : G ≃ Fin m)
    (v : V) (g : G) :
    v ∈ P.group g ↔ ∃ a : Fin 4, indexedCoordinates P eG v = some (eG g,a) := by
  rw [P.mem_group_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by simp [indexedCoordinates, ha]⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply (Equiv.optionCongr (Equiv.prodCongr eG (Equiv.refl (Fin 4)))).injective
    exact ha

/-- Every actual pencil block has exactly the corresponding canonical image. -/
theorem map_groupBlock {p : V}
    (P : UniformPartitionCoordinates.Partition (G := G) p) {m : ℕ} (eG : G ≃ Fin m)
    (g : G) :
    (insert p (P.group g)).map (indexedCoordinates P eG).toEmbedding = groupBlock (eG g) := by
  ext z
  have hp : (indexedCoordinates P eG).symm z = p ↔ z = none := by
    rw [Equiv.symm_apply_eq, indexedCoordinates_point]
  have hg : (indexedCoordinates P eG).symm z ∈ P.group g ↔
      ∃ a : Fin 4, z = some (eG g,a) := by
    rw [indexedCoordinates_group P eG]
    simp
  simp only [mem_map_equiv, mem_insert, hp, hg, groupBlock, mem_image, mem_univ, true_and]
  constructor
  · rintro (h | ⟨a,ha⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a,ha.symm⟩
  · rintro (h | ⟨a,ha⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a,ha.symm⟩

/-- A supplied finite design can be normalized at any point when its order is `4*m+1`. -/
theorem normalize_at_point (D : Finset (Finset V)) (hD : D.IsBlockDesign 2 5)
    (p : V) (m : ℕ) (hcard : Fintype.card V = 4 * m + 1) :
    ∃ e : V ≃ Option (Fin m × Fin 4), e p = none ∧
      (DesignTransport.relabel e D).IsBlockDesign 2 5 ∧
      ∀ i : Fin m, groupBlock i ∈ DesignTransport.relabel e D := by
  let P := pencilPartition D hD p
  let eG : ↥(DesignPencil.groups D p) ≃ Fin m :=
    Finset.equivFinOfCardEq (DesignPencil.groups_card_of_card D hD p m hcard)
  let e := indexedCoordinates P eG
  refine ⟨e, indexedCoordinates_point P eG,
    DesignTransport.isBlockDesign_relabel e D 2 5 hD, ?_⟩
  intro i
  let g := eG.symm i
  have hg : g.val ∈ DesignPencil.groups D p := g.property
  obtain ⟨b, hb, herase⟩ := mem_image.mp hg
  obtain ⟨hbD, hpb⟩ := mem_filter.mp hb
  have hblock : insert p (P.group g) = b := by
    change insert p g.val = b
    rw [← herase]
    exact insert_erase hpb
  have hmap : b.map e.toEmbedding = groupBlock i := by
    rw [← hblock]
    change (insert p (P.group g)).map (indexedCoordinates P eG).toEmbedding = _
    rw [map_groupBlock P eG g]
    simp [g]
  exact mem_image.mpr ⟨b,hbD,hmap⟩

/-- Canonical pencil normalization, including `m=0`, with point zero distinguished. -/
theorem normalized_pencil_exists (m : ℕ) (D : Finset (Finset (Fin (4 * m + 1))))
    (hD : D.IsBlockDesign 2 5) :
    ∃ (e : Fin (4 * m + 1) ≃ Option (Fin m × Fin 4))
      (H : Finset (Finset (Option (Fin m × Fin 4)))),
      e ⟨0, by omega⟩ = none ∧ H = DesignTransport.relabel e D ∧
      H.IsBlockDesign 2 5 ∧ ∀ i : Fin m, groupBlock i ∈ H := by
  obtain ⟨e, he, hdesign, hgroups⟩ := normalize_at_point D hD ⟨0, by omega⟩ m (by simp)
  exact ⟨e,DesignTransport.relabel e D,he,rfl,hdesign,hgroups⟩

end Erdos643Design.NormalizedPencil
