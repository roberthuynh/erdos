import GadgetNormalization.Point
import EvenFactor.Extremal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open SimpleGraph Finset Set
namespace Erdos585.GadgetNormalization
open EvenFactorCriterion
universe u w
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev remaining (X : Finset V) := ((⊤ : G.Subgraph).deleteVerts (X : Set V)).coe

@[simp] lemma remaining_mem (X : Finset V) (v : V) :
    v ∈ ((⊤ : G.Subgraph).deleteVerts (X : Set V)).verts ↔ v ∉ X := by
  simp [Subgraph.deleteVerts]

@[simp] lemma remaining_adj (X : Finset V)
    (a b : ((⊤ : G.Subgraph).deleteVerts (X : Set V)).verts) :
    (remaining G X).Adj a b ↔ G.Adj a.val b.val := by
  simp only [remaining, Subgraph.coe_adj, Subgraph.deleteVerts_adj, Subgraph.top_adj]
  have ha := (remaining_mem G X a.val).mp a.property
  have hb := (remaining_mem G X b.val).mp b.property
  simp [ha,hb]

def restoredVertex (X : Finset V) (z : V) :
    ((⊤ : G.Subgraph).deleteVerts (X.erase z : Set V)).verts :=
  ⟨z, (remaining_mem G (X.erase z) z).mpr (by simp)⟩

def erasePointIso (X : Finset V) (z : V) (hz : z ∈ X) :
    remaining G X ≃g punctured (remaining G (X.erase z)) (restoredVertex G X z) where
  toFun a := ⟨⟨a.val, (remaining_mem G (X.erase z) a.val).mpr
    (fun h => (remaining_mem G X a.val).mp a.property (mem_of_mem_erase h))⟩,
    fun h => (remaining_mem G X a.val).mp a.property (by
      have he : a.val = z := congrArg (fun v => v.val) h
      simpa [he] using hz)⟩
  invFun a := ⟨a.val.val, (remaining_mem G X a.val.val).mpr (by
    intro ha
    have hne : a.val.val ≠ z := by
      intro he
      exact a.property (Subtype.ext he)
    exact (remaining_mem G (X.erase z) a.val.val).mp a.val.property
      (mem_erase.mpr ⟨hne,ha⟩))⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv a := by apply Subtype.ext; apply Subtype.ext; rfl
  map_rel_iff' := by
    intro a b
    change (remaining G (X.erase z)).Adj _ _ ↔ (remaining G X).Adj a b
    simp only [remaining_adj]
    rfl

/-- Isomorphisms transport the actual component supports and their odd counts. -/
lemma iso_odd_ncard {W : Type w} [Finite W] (H : SimpleGraph W)
    (e : G ≃g H) : G.oddComponents.ncard = H.oddComponents.ncard := by
  let ec := e.connectedComponentEquiv
  apply Set.ncard_congr' (ec.subtypeEquiv ?_)
  intro c
  change Odd c.supp.ncard ↔ Odd (ec c).supp.ncard
  rw [Set.ncard_congr' (c.isoEquivSupp e)]

/-- This image is taken in the actual top-deleteVerts graph. -/
def touch (X : Finset V) (z : V) : Set (remaining G X).ConnectedComponent :=
  {c | ∃ a : ((⊤ : G.Subgraph).deleteVerts (X : Set V)).verts,
    G.Adj z a.val ∧ (remaining G X).connectedComponentMk a = c}

lemma touch_iso_image (X : Finset V) (z : V) (hz : z ∈ X) :
    (erasePointIso G X z hz).connectedComponentEquiv '' touch G X z =
      pointTouch (remaining G (X.erase z)) (restoredVertex G X z) := by
  ext c
  constructor
  · rintro ⟨d,⟨a,ha,he⟩,rfl⟩
    refine ⟨erasePointIso G X z hz a, ?_, ?_⟩
    · exact (remaining_adj G (X.erase z) _ _).mpr ha
    · change ConnectedComponent.map (erasePointIso G X z hz).toHom
        ((remaining G X).connectedComponentMk a) =
        ConnectedComponent.map (erasePointIso G X z hz).toHom d
      rw [he]
  · rintro ⟨a,ha,he⟩
    let b := (erasePointIso G X z hz).symm a
    refine ⟨(remaining G X).connectedComponentMk b, ?_, ?_⟩
    · refine ⟨b, ?_, rfl⟩
      exact (remaining_adj G (X.erase z) _ _).mp ha
    · change (punctured (remaining G (X.erase z)) (restoredVertex G X z)).connectedComponentMk
        ((erasePointIso G X z hz) b) = c
      simpa [b] using he

theorem restore_odd_bound (X : Finset V) (z : V) (hz : z ∈ X)
    (ht : (touch G X z).ncard ≤ 2) :
    oddRemaining G X ≤ oddRemaining G (X.erase z) + 1 := by
  have ht' : (pointTouch (remaining G (X.erase z)) (restoredVertex G X z)).ncard ≤ 2 := by
    rw [← touch_iso_image G X z hz,
      Set.ncard_image_of_injective _ (erasePointIso G X z hz).connectedComponentEquiv.injective]
    exact ht
  have hb := point_odd_bound (remaining G (X.erase z)) (restoredVertex G X z) ht'
  have he := iso_odd_ncard (remaining G X)
    (punctured (remaining G (X.erase z)) (restoredVertex G X z)) (erasePointIso G X z hz)
  change (remaining G X).oddComponents.ncard ≤ (remaining G (X.erase z)).oddComponents.ncard + 1
  rw [he]
  exact hb

theorem restore_deficiency (X : Finset V) (z : V) (hz : z ∈ X)
    (ht : (touch G X z).ncard ≤ 2) :
    gadgetDeficiency G X ≤ gadgetDeficiency G (X.erase z) := by
  have ho := restore_odd_bound G X z hz ht
  have hc := card_erase_add_one hz
  unfold gadgetDeficiency
  omega

theorem extremal_touch_gt_two (X : Finset V) (hX : ExtremalDeletion G X)
    (z : V) (hz : z ∈ X) : 2 < (touch G X z).ncard := by
  by_contra h
  have hh := restore_deficiency G X z hz (by omega)
  have hs := extremal_erase_strict G X hX z hz
  omega

end Erdos585.GadgetNormalization
