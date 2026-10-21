import Openmath.Erdos642.Proofs.DenseMask20261019.ObstructionCollections

namespace Erdos642.DenseMask20261019.DeletionComponents
open SimpleGraph Finset
open Erdos642.CampaignFe72210b
open ComponentObstruction ComponentEntropy ObstructionCollections
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def liveComponents (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :=
  componentCollection G W W

noncomputable def componentCount (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) : ℕ :=
  (liveComponents G W).card

theorem live_meets (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V)
    {c : (mask G W).ConnectedComponent} (hc : c ∈ liveComponents G W) :
    ∃ v ∈ W, v ∈ c.supp := by
  obtain ⟨v, hv, _, hvc⟩ := collection_meets G W W (Finset.Subset.refl _) hc
  exact ⟨v, hv, hvc⟩

theorem live_support_subset (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V)
    {c : (mask G W).ConnectedComponent} (hc : c ∈ liveComponents G W) :
    c.supp ⊆ (W : Set V) := by
  obtain ⟨v, hv, hvc⟩ := live_meets G W hc
  intro u hu
  exact reachable_mem_closed G W W W (Finset.Subset.refl _)
    (fun _ _ _ hy _ => hy) hv (ConnectedComponent.exact (hvc.trans hu.symm))

theorem live_union (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    unionVertices G W (liveComponents G W) = W := by
  apply union_collection_eq G W W (Finset.Subset.refl _)
  ext v
  rw [mem_componentUnion]
  constructor
  · exact fun h => h.1
  · intro hv
    exact ⟨hv, v, Finset.mem_inter.mpr ⟨hv, hv⟩, Reachable.rfl⟩

theorem live_card_partition (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    W.card = ∑ c ∈ liveComponents G W, (componentVertices G W c).card := by
  rw [← union_card, live_union]

theorem union_subset (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V)
    (F : Finset (mask G W).ConnectedComponent) : unionVertices G W F ⊆ W := by
  intro v hv
  obtain ⟨c, _, hv⟩ := Finset.mem_biUnion.mp hv
  exact ((mem_componentVertices G W c v).mp hv).1

theorem union_closed (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V)
    (F : Finset (mask G W).ConnectedComponent) :
    ∀ x ∈ unionVertices G W F, ∀ y ∈ W, G.Adj x y → y ∈ unionVertices G W F := by
  intro x hx y hy hxy
  obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨hxW, hxc⟩ := (mem_componentVertices G W c x).mp hxc
  exact Finset.mem_biUnion.mpr ⟨c, hc,
    (mem_componentVertices G W c y).mpr
      ⟨hy, c.mem_supp_of_adj_mem_supp hxc ⟨hxy, hxW, hy⟩⟩⟩

/-- Deleting vertices can lose at most one old live component per deleted vertex. -/
theorem componentCount_mono_delete (G : SimpleGraph V) [DecidableRel G.Adj]
    (A W : Finset V) (hWA : W ⊆ A) :
    componentCount G A ≤ componentCount G W + (A \ W).card := by
  classical
  let f : mask G W →g mask G A :=
    { toFun := id
      map_rel' := fun h => ⟨h.1, hWA h.2.1, hWA h.2.2⟩ }
  have hsub : liveComponents G A ⊆
      (liveComponents G W).image (ConnectedComponent.map f) ∪
        (A \ W).image (mask G A).connectedComponentMk := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    by_cases hvW : v ∈ W
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨(mask G W).connectedComponentMk v,
        Finset.mem_image.mpr ⟨v, hvW, rfl⟩, rfl⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvW⟩, rfl⟩)
  unfold componentCount
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)

private def inducedToMask (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    G.induce (W : Set V) →g mask G W where
  toFun := Subtype.val
  map_rel' h := ⟨h, Subtype.property _, Subtype.property _⟩

private theorem mask_reachable_induced (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) {x y : V} (hx : x ∈ W) (hy : y ∈ W)
    (hr : (mask G W).Reachable x y) :
    (G.induce (W : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  obtain ⟨p⟩ := hr
  have hs : ∀ z ∈ p.support, z ∈ W := by
    intro z hz
    exact reachable_mem_closed G W W W (Finset.Subset.refl _)
      (fun _ _ _ hw _ => hw) hx (p.takeUntil z hz).reachable
  let f : mask G W →g G := ⟨id, fun h => h.1⟩
  have hs' : ∀ z ∈ (p.map f).support, z ∈ (W : Set V) := by
    simpa [Walk.support_map, f] using hs
  exact ⟨(p.map f).induce (W : Set V) hs'⟩

private theorem induced_map_injective (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) : Function.Injective (ConnectedComponent.map (inducedToMask G W)) := by
  intro C D
  induction C using ConnectedComponent.ind with | _ x =>
    induction D using ConnectedComponent.ind with | _ y =>
      intro he
      exact ConnectedComponent.sound (mask_reachable_induced G W x.property y.property
        (ConnectedComponent.exact he))

noncomputable def inducedComponentEquiv (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) : (G.induce (W : Set V)).ConnectedComponent ≃ liveComponents G W := by
  classical
  let f : (G.induce (W : Set V)).ConnectedComponent → liveComponents G W := fun C =>
    ⟨ConnectedComponent.map (inducedToMask G W) C, by
      induction C using ConnectedComponent.ind with | _ v =>
        exact Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro C D he
    exact induced_map_injective G W (congrArg Subtype.val he)
  · intro c
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp c.property
    refine ⟨(G.induce (W : Set V)).connectedComponentMk ⟨v, hv⟩, ?_⟩
    exact Subtype.ext he

theorem componentCount_eq_induce (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    componentCount G W = Nat.card (G.induce (W : Set V)).ConnectedComponent := by
  have h := Nat.card_congr (inducedComponentEquiv G W)
  have hc : Nat.card ↥(liveComponents G W) = (liveComponents G W).card := by
    classical
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe _
  exact hc.symm.trans h.symm

/-- Ordinary toughness uses every actual original deletion and all remaining induced components. -/
def OrdinaryTough (G : SimpleGraph V) (eta : ℝ) : Prop :=
  ∀ Z : Set V, 2 ≤ Nat.card (G.induce Zᶜ).ConnectedComponent →
    eta * (Nat.card (G.induce Zᶜ).ConnectedComponent : ℝ) ≤ (Z.ncard : ℝ)

theorem ordinaryTough_iff_finset (G : SimpleGraph V) [DecidableRel G.Adj] (eta : ℝ) :
    OrdinaryTough G eta ↔ ∀ Z : Finset V, 2 ≤ componentCount G (Finset.univ \ Z) →
      eta * (componentCount G (Finset.univ \ Z) : ℝ) ≤ (Z.card : ℝ) := by
  classical
  have he (Z : Finset V) : ((Finset.univ \ Z : Finset V) : Set V) = (Z : Set V)ᶜ := by
    ext v; simp
  constructor
  · intro h Z hZ
    have hc := componentCount_eq_induce G (Finset.univ \ Z)
    rw [he] at hc
    simpa only [hc, Set.ncard_coe_finset] using h (Z : Set V) (by simpa [hc] using hZ)
  · intro h Z hZ
    have hc := componentCount_eq_induce G (Finset.univ \ Z.toFinset)
    have hz : (Z.toFinset : Set V) = Z := Set.coe_toFinset Z
    rw [he, hz] at hc
    have hh := h Z.toFinset (by simpa only [hc] using hZ)
    simpa only [hc, Set.toFinset_card, Set.fintypeCard_eq_ncard] using hh

end Erdos642.DenseMask20261019.DeletionComponents
