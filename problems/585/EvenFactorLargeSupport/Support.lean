import L34EvenTransfer.Main

/-! Actual original endpoint support and injective transport.
This contains no factor supplier in the unrestricted public endpoint. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
namespace Erdos585.EvenFactorLargeSupport
open QB4 B5 NEQ NEQAssembly
universe u v

theorem dense_order_lower {V : Type u} [Fintype V]
    (q : ℕ) (hq : 6 ≤ q) (G : SimpleGraph V)
    (hn : 2 ≤ Fintype.card V)
    (he : (q - 1) * Fintype.card V ≤ G.edgeSet.ncard + (q - 2)) :
    2 * q - 1 ≤ Fintype.card V := by
  classical
  let m := Fintype.card V
  have hdegree : ∀ a : V, G.degree a ≤ m - 1 := by
    intro a
    have h := G.degree_lt_card_verts a
    dsimp [m]
    omega
  have hsum : ∑ a : V, G.degree a ≤ m * (m - 1) := by
    calc
      ∑ a : V, G.degree a ≤ ∑ _a : V, (m - 1) :=
        sum_le_sum (fun a _ => hdegree a)
      _ = m * (m - 1) := by simp [m]
  have hcount : 2 * G.edgeSet.ncard = ∑ a : V, G.degree a := by
    simpa only [ec, dg_univ_eq_degree] using
      (ec_univ_eq_twice_edges (G := G)).symm
  by_contra hsmall
  have hm : m ≤ 2 * q - 2 := by dsimp [m]; omega
  have hq1 : q - 1 + 1 = q := by omega
  have hq2 : q - 2 + 2 = q := by omega
  have hm1 : m - 1 + 1 = m := by dsimp [m]; omega
  have hdelta : (2 * q - 2 - m) + m + 2 = 2 * q := by omega
  have hnonneg := Nat.zero_le ((m - 1) * (2 * q - 2 - m))
  change (q - 1) * m ≤ _ at he
  nlinarith

theorem regularPairs_large_support {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {q : ℕ} {U W : Finset V}
    (hUW : Disjoint U W) (h : RegularPairs q G U W) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧
      2 * q ≤ H.verts.ncard := by
  classical
  obtain ⟨F, hne, hF, hadj, hU, hW⟩ := h
  have hFU : ∀ x ∈ F, x.1 ∈ U := fun x hx => (mem_product.mp (hF hx)).1
  have hFW : ∀ x ∈ F, x.2 ∈ W := fun x hx => (mem_product.mp (hF hx)).2
  let H := pairSubgraph F hadj
  have hdeg : ∀ a ∈ H.verts, ∀ [Fintype (H.neighborSet a)], H.degree a = q := by
    rintro a ⟨x, hx, rfl | rfl⟩ _
    · rw [degree_pairSubgraph_left hadj hFW (disjoint_left.mp hUW (hFU x hx))]
      exact (hU x.1).resolve_left (card_ne_zero.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩)
    · rw [degree_pairSubgraph_right hadj hFU (disjoint_right.mp hUW (hFW x hx))]
      exact (hW x.2).resolve_left (card_ne_zero.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩)
  obtain ⟨p, hp⟩ := hne
  have hpRow : #{x ∈ F | x.1 = p.1} = q :=
    (hU p.1).resolve_left (card_ne_zero.mpr ⟨p, mem_filter.mpr ⟨hp, rfl⟩⟩)
  have hpCol : #{x ∈ F | x.2 = p.2} = q :=
    (hW p.2).resolve_left (card_ne_zero.mpr ⟨p, mem_filter.mpr ⟨hp, rfl⟩⟩)
  let A := F.image Prod.fst
  let B := F.image Prod.snd
  have hA : q ≤ #A := by
    have hi : Set.InjOn Prod.fst (↑(F.filter fun x => x.2 = p.2) : Set (V × V)) := by
      intro x hx y hy hxy
      apply Prod.ext hxy
      exact (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
    have hc := card_image_of_injOn hi
    have hs : (F.filter fun x => x.2 = p.2).image Prod.fst ⊆ A :=
      image_subset_image (filter_subset _ _)
    have hh := card_le_card hs
    rw [hc, hpCol] at hh
    exact hh
  have hB : q ≤ #B := by
    have hi : Set.InjOn Prod.snd (↑(F.filter fun x => x.1 = p.1) : Set (V × V)) := by
      intro x hx y hy hxy
      apply Prod.ext _ hxy
      exact (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
    have hc := card_image_of_injOn hi
    have hs : (F.filter fun x => x.1 = p.1).image Prod.snd ⊆ B :=
      image_subset_image (filter_subset _ _)
    have hh := card_le_card hs
    rw [hc, hpRow] at hh
    exact hh
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨x, hx, hxa⟩ := mem_image.mp ha
    obtain ⟨y, hy, hya⟩ := mem_image.mp hb
    exact disjoint_left.mp hUW (hxa ▸ hFU x hx) (hya ▸ hFW y hy)
  have hverts : H.verts = (↑(A ∪ B) : Set V) := by
    ext a
    change (∃ x ∈ F, x.1 = a ∨ x.2 = a) ↔ a ∈ A ∪ B
    constructor
    · rintro ⟨x, hx, hxa | hxa⟩
      · exact mem_union_left _ (mem_image.mpr ⟨x, hx, hxa⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨x, hx, hxa⟩)
    · intro ha
      rcases mem_union.mp ha with ha | ha
      · obtain ⟨x, hx, hxa⟩ := mem_image.mp ha
        exact ⟨x, hx, Or.inl hxa⟩
      · obtain ⟨x, hx, hxa⟩ := mem_image.mp ha
        exact ⟨x, hx, Or.inr hxa⟩
  refine ⟨H, ⟨p.1, p, hp, Or.inl rfl⟩, ?_, ?_⟩
  · intro a
    rw [SimpleGraph.Subgraph.coe_degree]
    exact hdeg a a.2
  · rw [hverts, Set.ncard_coe_finset, card_union_of_disjoint hAB]
    omega

theorem regular_map_large {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {K : SimpleGraph A} {G : SimpleGraph B} {q s : ℕ}
    (f : K →g G) (hf : Function.Injective f)
    (h : ∃ H : K.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧
      s ≤ H.verts.ncard) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧
      s ≤ H.verts.ncard := by
  classical
  obtain ⟨H, hne, hreg, hsize⟩ := h
  refine ⟨H.map f, hne.image f, ?_, ?_⟩
  · let e := NEQAssembly.subgraphMapIso f hf H
    intro a
    exact (e.symm.degree_eq a).symm.trans (hreg (e.symm a))
  · change s ≤ (f '' H.verts).ncard
    rwa [Set.ncard_image_of_injective _ hf]

end Erdos585.EvenFactorLargeSupport
