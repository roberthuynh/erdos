import GadgetNormalization.Restoration
import FactorMatching.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open SimpleGraph Finset Set
namespace Erdos585.GadgetNormalization
open EvenFactorCriterion FactorMatching
universe u
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]

lemma touch_le_one_of_unique_neighbor (X : Finset (Vertex q G)) (z : Vertex q G)
    (hu : ∀ a b : ((⊤ : (gadget q G).Subgraph).deleteVerts (X : Set (Vertex q G))).verts,
      (gadget q G).Adj z a.val → (gadget q G).Adj z b.val → a = b) :
    (touch (gadget q G) X z).ncard ≤ 1 := by
  apply (Set.ncard_le_one (Set.toFinite _)).mpr
  rintro c ⟨a,ha,rfl⟩ d ⟨b,hb,rfl⟩
  rw [hu a b ha hb]

lemma touch_le_two_of_component_or_vertex (X : Finset (Vertex q G)) (z w : Vertex q G)
    (c : (remaining (gadget q G) X).ConnectedComponent)
    (hu : ∀ a : ((⊤ : (gadget q G).Subgraph).deleteVerts (X : Set (Vertex q G))).verts,
      (gadget q G).Adj z a.val →
      (remaining (gadget q G) X).connectedComponentMk a = c ∨ a.val = w) :
    (touch (gadget q G) X z).ncard ≤ 2 := by
  by_cases hw : w ∈ X
  · have hsub : touch (gadget q G) X z ⊆ {c} := by
      rintro d ⟨a,ha,rfl⟩
      rcases hu a ha with h | h
      · exact h
      · exact False.elim ((remaining_mem (gadget q G) X a.val).mp a.property (h ▸ hw))
    exact (Set.ncard_le_ncard hsub).trans (by simp)
  · let b : ((⊤ : (gadget q G).Subgraph).deleteVerts (X : Set (Vertex q G))).verts :=
      ⟨w,(remaining_mem (gadget q G) X w).mpr hw⟩
    let d := (remaining (gadget q G) X).connectedComponentMk b
    have hsub : touch (gadget q G) X z ⊆ {c} ∪ {d} := by
      rintro e ⟨a,ha,rfl⟩
      rcases hu a ha with h | h
      · exact Or.inl h
      · exact Or.inr (congrArg (remaining (gadget q G) X).connectedComponentMk
          (show a = b from Subtype.ext h))
    exact (Set.ncard_le_ncard hsub).trans (by
      have hh := Set.ncard_union_le ({c} : Set (remaining (gadget q G) X).ConnectedComponent) {d}
      simpa using hh)

lemma slot_touch_le_one (X : Finset (Vertex q G)) (v : V) (i j : Fin q)
    (hj : Sum.inl (v,j) ∉ X) :
    (touch (gadget q G) X (Sum.inl (v,i))).ncard ≤ 1 := by
  let a : ((⊤ : (gadget q G).Subgraph).deleteVerts (X : Set (Vertex q G))).verts :=
    ⟨Sum.inl (v,j), (remaining_mem (gadget q G) X _).mpr hj⟩
  have hsub : touch (gadget q G) X (Sum.inl (v,i)) ⊆
      {(remaining (gadget q G) X).connectedComponentMk a} := by
    rintro c ⟨b,hb,rfl⟩
    have hab : (remaining (gadget q G) X).Adj b a := by
      apply (remaining_adj (gadget q G) X b a).mpr
      rcases b with ⟨b,hb'⟩
      cases b with
      | inl s => exact False.elim ((gadget_slot_slot q G (v,i) s) hb)
      | inr d => exact (gadget_stub_slot q G (v,j) d).mpr ((gadget_slot_stub q G (v,i) d).mp hb)
    exact ConnectedComponent.connectedComponentMk_eq_of_adj hab
  exact (Set.ncard_le_ncard hsub).trans (by simp)

lemma slot_uniform (X : Finset (Vertex q G)) (hX : ExtremalDeletion (gadget q G) X)
    (v : V) (i j : Fin q) : Sum.inl (v,i) ∈ X ↔ Sum.inl (v,j) ∈ X := by
  have h (i j : Fin q) : Sum.inl (v,i) ∈ X → Sum.inl (v,j) ∈ X := by
    intro hi
    by_contra hj
    have hs := slot_touch_le_one q G X v i j hj
    have he := extremal_touch_gt_two (gadget q G) X hX (Sum.inl (v,i)) hi
    omega
  exact ⟨h i j,h j i⟩

lemma stub_touch_le_one_of_slots_deleted (X : Finset (Vertex q G)) (d : G.Dart)
    (hs : ∀ i : Fin q, Sum.inl (d.fst,i) ∈ X) :
    (touch (gadget q G) X (Sum.inr d)).ncard ≤ 1 := by
  apply touch_le_one_of_unique_neighbor q G X (Sum.inr d)
  have hneighbor (a : ((⊤ : (gadget q G).Subgraph).deleteVerts (X : Set (Vertex q G))).verts)
      (ha : (gadget q G).Adj (Sum.inr d) a.val) : a.val = Sum.inr d.symm := by
    rcases a with ⟨a,hax⟩
    cases a with
    | inl s =>
      have he : d.fst = s.1 := (gadget_stub_slot q G s d).mp ha
      have hh : Sum.inl s ∈ X := by simpa [he] using hs s.2
      exact False.elim ((remaining_mem (gadget q G) X _).mp hax hh)
    | inr e => exact congrArg Sum.inr ((gadget_stub_stub q G d e).mp ha)
  intro a b ha hb
  exact Subtype.ext ((hneighbor a ha).trans (hneighbor b hb).symm)

lemma stub_not_deleted_of_slots_deleted (X : Finset (Vertex q G))
    (hX : ExtremalDeletion (gadget q G) X) (d : G.Dart)
    (hs : ∀ i : Fin q, Sum.inl (d.fst,i) ∈ X) : Sum.inr d ∉ X := by
  intro hd
  have ht := stub_touch_le_one_of_slots_deleted q G X d hs
  have he := extremal_touch_gt_two (gadget q G) X hX (Sum.inr d) hd
  omega

lemma stub_touch_le_two_of_remaining_local_stub (X : Finset (Vertex q G))
    (d e : G.Dart) (he : e.fst = d.fst) (heX : Sum.inr e ∉ X)
    (hs : ∀ i : Fin q, Sum.inl (d.fst,i) ∉ X) :
    (touch (gadget q G) X (Sum.inr d)).ncard ≤ 2 := by
  let a : ((⊤ : (gadget q G).Subgraph).deleteVerts (X : Set (Vertex q G))).verts :=
    ⟨Sum.inr e,(remaining_mem (gadget q G) X _).mpr heX⟩
  apply touch_le_two_of_component_or_vertex q G X (Sum.inr d) (Sum.inr d.symm)
    ((remaining (gadget q G) X).connectedComponentMk a)
  rintro ⟨b,hb⟩ hab
  cases b with
  | inl s =>
    left
    apply ConnectedComponent.connectedComponentMk_eq_of_adj
    apply (remaining_adj (gadget q G) X _ a).mpr
    exact (gadget_slot_stub q G s e).mpr
      (he.trans ((gadget_stub_slot q G s d).mp hab))
  | inr f => exact Or.inr (congrArg Sum.inr ((gadget_stub_stub q G d f).mp hab))

lemma stub_uniform (hq : 0 < q) (X : Finset (Vertex q G))
    (hX : ExtremalDeletion (gadget q G) X) (d e : G.Dart) (he : e.fst = d.fst) :
    Sum.inr d ∈ X ↔ Sum.inr e ∈ X := by
  have h (d e : G.Dart) (he : e.fst = d.fst) : Sum.inr d ∈ X → Sum.inr e ∈ X := by
    intro hd
    by_contra heX
    have hs : ∀ i : Fin q, Sum.inl (d.fst,i) ∉ X := by
      intro i hi
      have hall : ∀ j : Fin q, Sum.inl (d.fst,j) ∈ X :=
        fun j => (slot_uniform q G X hX d.fst i j).mp hi
      exact stub_not_deleted_of_slots_deleted q G X hX d hall hd
    have ht := stub_touch_le_two_of_remaining_local_stub q G X d e he heX hs
    have hh := extremal_touch_gt_two (gadget q G) X hX (Sum.inr d) hd
    omega
  exact ⟨h d e he,h e d he.symm⟩

end Erdos585.GadgetNormalization
