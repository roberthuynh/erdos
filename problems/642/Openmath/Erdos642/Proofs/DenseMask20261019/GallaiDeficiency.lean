import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Tactic

namespace Erdos642.DenseMask20261019.GallaiDeficiency
open SimpleGraph

variable {V W : Type*}

/-- The original graph with a clique of fresh universal vertices. -/
def augment (G : SimpleGraph V) (d : ℕ) : SimpleGraph (V ⊕ Fin d) where
  Adj u v := match u, v with
    | .inl a, .inl b => G.Adj a b
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr a, .inr b => a ≠ b
  symm := ⟨by intro u v; cases u <;> cases v <;> simp_all [G.adj_comm, ne_comm]⟩
  loopless := ⟨by intro u; cases u <;> simp⟩

private abbrev deleted (G : SimpleGraph V) (D : Set V) :=
  ((⊤ : G.Subgraph).deleteVerts D).coe

private theorem deleted_adj (G : SimpleGraph V) (D : Set V)
    (u v : ((⊤ : G.Subgraph).deleteVerts D).verts) :
    (deleted G D).Adj u v ↔ G.Adj u.val v.val := by
  change (_ ∧ _ ∧ _) ↔ _
  simp [u.property.2, v.property.2]

private theorem odd_iso [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : G.oddComponents.ncard = H.oddComponents.ncard := by
  have hc (C : G.ConnectedComponent) :
      C.supp.ncard = (e.connectedComponentEquiv C).supp.ncard :=
    Set.ncard_congr' (C.isoEquivSupp e)
  apply Set.ncard_congr'
  exact e.connectedComponentEquiv.subtypeEquiv (by intro C; change Odd _ ↔ Odd _; rw [hc C])

private theorem odd_le_one [Finite V] {G : SimpleGraph V} (h : G.Preconnected) :
    G.oddComponents.ncard ≤ 1 := by
  letI := h.subsingleton_connectedComponent
  exact Set.ncard_le_one_of_subsingleton _

private def allFreshDeletedIso (G : SimpleGraph V) (d : ℕ) (D : Set (V ⊕ Fin d))
    (hD : ∀ j, Sum.inr j ∈ D) :
    deleted (augment G d) D ≃g deleted G (Sum.inl ⁻¹' D) where
  toFun v := match v with
    | ⟨.inl a, ha⟩ => ⟨a, by simpa using ha⟩
    | ⟨.inr j, hj⟩ => False.elim (hj.2 (hD j))
  invFun v := ⟨.inl v.val, by simpa using v.property⟩
  left_inv := by
    rintro ⟨a, ha⟩
    cases a with
    | inl a => rfl
    | inr j => exact False.elim (ha.2 (hD j))
  right_inv := by intro v; rfl
  map_rel_iff' := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    cases u with
    | inr j => exact False.elim (hu.2 (hD j))
    | inl a =>
      cases v with
      | inr j => exact False.elim (hv.2 (hD j))
      | inl b =>
        change (deleted G (Sum.inl ⁻¹' D)).Adj _ _ ↔ _
        rw [deleted_adj, deleted_adj]
        rfl

/-- The universal-clique augmentation satisfies Tutte under the original deficiency bound. -/
theorem augmentation_tutte [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (heven : Even (Nat.card V + d))
    (hdef : ∀ D : Set V, (deleted G D).oddComponents.ncard ≤ D.ncard + d) :
    ∀ D, ¬(augment G d).IsTutteViolator D := by
  classical
  intro D
  change ¬ D.ncard < (deleted (augment G d) D).oddComponents.ncard
  apply not_lt.mpr
  by_cases hall : ∀ j, Sum.inr j ∈ D
  · rw [odd_iso (allFreshDeletedIso G d D hall)]
    apply (hdef (Sum.inl ⁻¹' D)).trans
    let f : (Sum.inl ⁻¹' D : Set V) ⊕ Fin d → D := fun v =>
      match v with
      | .inl a => ⟨.inl a.val, a.property⟩
      | .inr j => ⟨.inr j, hall j⟩
    have hi : Function.Injective f := by
      intro a b h
      cases a <;> cases b <;> simp_all [f, Subtype.ext_iff]
    have hh := Nat.card_le_card_of_injective f hi
    simpa only [Nat.card_sum, Nat.card_fin, Nat.card_coe_set_eq] using hh
  · push_neg at hall
    obtain ⟨j, hj⟩ := hall
    let z : ((⊤ : (augment G d).Subgraph).deleteVerts D).verts :=
      ⟨.inr j, by simpa using hj⟩
    have hp : (deleted (augment G d) D).Preconnected := by
      intro u v
      have hz (w : ((⊤ : (augment G d).Subgraph).deleteVerts D).verts) :
          (deleted (augment G d) D).Reachable w z := by
        by_cases hw : w = z
        · subst w; exact .refl _
        · apply SimpleGraph.Adj.reachable
          rw [deleted_adj]
          rcases w with ⟨w, hw'⟩
          cases w with
          | inl a => trivial
          | inr k =>
            change k ≠ j
            intro h; apply hw; subst k; rfl
      exact (hz u).trans (hz v).symm
    have ho := odd_le_one hp
    by_cases hD : D = ∅
    · subst D
      have hpar : Even (Nat.card ((⊤ : (augment G d).Subgraph).deleteVerts ∅).verts) := by
        simpa [Nat.card_sum, Nat.card_fin] using heven
      have hnot : ¬ Odd (deleted (augment G d) ∅).oddComponents.ncard := by
        rw [SimpleGraph.odd_ncard_oddComponents]
        exact Nat.not_odd_iff_even.mpr hpar
      simp only [Set.ncard_empty]
      obtain ⟨r, hr⟩ := Nat.not_odd_iff_even.mp hnot
      have hz : (deleted (augment G d) ∅).oddComponents.ncard = 0 := by omega
      exact hz.le
    · have hpos : 1 ≤ D.ncard := (Set.ncard_pos (s := D)).mpr (Set.nonempty_iff_ne_empty.mpr hD)
      exact ho.trans hpos

/-- Retain only matching edges with both endpoints in the original graph. -/
def originalPart {G : SimpleGraph V} {d : ℕ} (M : (augment G d).Subgraph) :
    G.Subgraph where
  verts := {v | ∃ w, M.Adj (.inl v) (.inl w)}
  Adj v w := M.Adj (.inl v) (.inl w)
  adj_sub := fun h => M.adj_sub h
  edge_vert := fun h => ⟨_, h⟩
  symm := ⟨fun _ _ h => M.adj_symm h⟩

theorem originalPart_matching {G : SimpleGraph V} {d : ℕ}
    {M : (augment G d).Subgraph} (hM : M.IsMatching) : (originalPart M).IsMatching := by
  rintro v ⟨w, hw⟩
  refine ⟨w, hw, ?_⟩
  intro z hz
  exact Sum.inl_injective (hM.eq_of_adj_left hz hw)

theorem originalPart_coverage [Fintype V] {G : SimpleGraph V} {d : ℕ}
    {M : (augment G d).Subgraph} (hM : M.IsPerfectMatching) :
    Nat.card V ≤ (originalPart M).verts.ncard + d := by
  classical
  have hp := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM
  have hex (v : ↥((originalPart M).vertsᶜ)) : ∃ j : Fin d, M.Adj (.inl v.val) (.inr j) := by
    obtain ⟨w, hw, _⟩ := hp (.inl v.val)
    cases w with
    | inl w => exact False.elim (v.property ⟨w, hw⟩)
    | inr j => exact ⟨j, hw⟩
  let f : ↥((originalPart M).vertsᶜ) → Fin d := fun v => (hex v).choose
  have hi : Function.Injective f := by
    intro u v huv
    have hu := (hex u).choose_spec
    have hv := (hex v).choose_spec
    change M.Adj (.inl u.val) (.inr (f u)) at hu
    change M.Adj (.inl v.val) (.inr (f v)) at hv
    rw [huv] at hu
    exact Subtype.ext (Sum.inl_injective (hM.1.eq_of_adj_right hu hv))
  have hc := Nat.card_le_card_of_injective f hi
  have hs := Set.ncard_add_ncard_compl (originalPart M).verts
  simp only [Nat.card_coe_set_eq, Nat.card_fin] at hc
  omega

theorem matching_card [Fintype V] {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) : M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have hd : ∀ v : M.verts, M.coe.degree v = 1 := by
    intro v
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    obtain ⟨w, hw, huniq⟩ := hM v.property
    refine ⟨⟨w, hw.snd_mem⟩, hw, ?_⟩
    intro z hz
    exact Subtype.ext (huniq z hz)
  have hs := M.coe.sum_degrees_eq_twice_card_edges
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hs hd
  simp only [hd, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hs
  have he : M.coe.edgeSet.ncard = M.edgeSet.ncard := by
    rw [← M.image_coe_edgeSet_coe]
    exact (Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)).symm
  calc
    M.verts.ncard = 2 * M.coe.edgeSet.ncard := by
      simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq] using hs
    _ = 2 * M.edgeSet.ncard := congrArg (2 * ·) he

/-- Forward finite matching deficiency, with an actual original matching. -/
theorem exists_matching_of_deficiency [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (heven : Even (Nat.card V + d))
    (hdef : ∀ D : Set V,
      ((⊤ : G.Subgraph).deleteVerts D).coe.oddComponents.ncard ≤ D.ncard + d) :
    ∃ M : G.Subgraph, M.IsMatching ∧ Nat.card V ≤ 2 * M.edgeSet.ncard + d := by
  classical
  obtain ⟨M, hM⟩ := SimpleGraph.tutte.mpr (augmentation_tutte G d heven hdef)
  refine ⟨originalPart M, originalPart_matching hM.1, ?_⟩
  simpa [matching_card (originalPart_matching hM.1)] using originalPart_coverage hM

end Erdos642.DenseMask20261019.GallaiDeficiency
