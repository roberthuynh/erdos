import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Openmath.Erdos642.Proofs.DenseMask20261019.GallaiMatching

namespace Erdos642.DenseMask20261019.GallaiPaths
open SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- In a connected union, a matching can exceed the other edge set by at most one. -/
theorem connected_union_surplus_bound (M N : G.Subgraph) (hM : M.IsMatching)
    (hc : (M.spanningCoe ⊔ N.spanningCoe).Connected) :
    M.edgeSet.ncard ≤ N.edgeSet.ncard + 1 := by
  classical
  have he := hc.card_vert_le_card_edgeSet_add_one
  have hu : (M.spanningCoe ⊔ N.spanningCoe).edgeSet.ncard ≤
      M.edgeSet.ncard + N.edgeSet.ncard := by
    rw [SimpleGraph.edgeSet_sup, Subgraph.edgeSet_spanningCoe, Subgraph.edgeSet_spanningCoe]
    exact Set.ncard_union_le _ _
  have hm := GallaiDeficiency.matching_card hM
  have hv : M.verts.ncard ≤ Nat.card V := by
    simpa using Set.ncard_le_ncard (Set.subset_univ M.verts)
  simp only [Nat.card_coe_set_eq] at he
  omega

/-- A positive-surplus connected union leaves exactly two vertices outside the smaller matching. -/
theorem connected_union_two_unmatched (M N : G.Subgraph)
    (hM : M.IsMatching) (hN : N.IsMatching)
    (hc : (M.spanningCoe ⊔ N.spanningCoe).Connected)
    (hpos : N.edgeSet.ncard < M.edgeSet.ncard) :
    N.vertsᶜ.ncard = 2 := by
  classical
  have hb := connected_union_surplus_bound M N hM hc
  have he := hc.card_vert_le_card_edgeSet_add_one
  have hu : (M.spanningCoe ⊔ N.spanningCoe).edgeSet.ncard ≤
      M.edgeSet.ncard + N.edgeSet.ncard := by
    rw [SimpleGraph.edgeSet_sup, Subgraph.edgeSet_spanningCoe, Subgraph.edgeSet_spanningCoe]
    exact Set.ncard_union_le _ _
  have hm := GallaiDeficiency.matching_card hM
  have hn := GallaiDeficiency.matching_card hN
  have hv : M.verts.ncard ≤ Nat.card V := by
    simpa using Set.ncard_le_ncard (Set.subset_univ M.verts)
  have hp := Set.ncard_add_ncard_compl N.verts
  simp only [Nat.card_coe_set_eq] at he
  omega

/-- A positive-surplus connected union has an actual simple path whose only vertices
outside the smaller matching are its distinct endpoints. -/
theorem connected_union_path (M N : G.Subgraph)
    (hM : M.IsMatching) (hN : N.IsMatching)
    (hc : (M.spanningCoe ⊔ N.spanningCoe).Connected)
    (hpos : N.edgeSet.ncard < M.edgeSet.ncard) :
    ∃ a b : V, ∃ p : (M.spanningCoe ⊔ N.spanningCoe).Walk a b,
      a ≠ b ∧ a ∉ N.verts ∧ b ∉ N.verts ∧ p.IsPath ∧
      ∀ x ∈ p.support, x ≠ a → x ≠ b → x ∈ N.verts := by
  classical
  have ht := connected_union_two_unmatched M N hM hN hc hpos
  obtain ⟨a, b, hab, heq⟩ := Set.ncard_eq_two.mp ht
  obtain ⟨p, hp⟩ := hc.exists_isPath a b
  refine ⟨a, b, p, hab, ?_, ?_, hp, ?_⟩
  · have : a ∈ N.vertsᶜ := by rw [heq]; simp
    exact this
  · have : b ∈ N.vertsᶜ := by rw [heq]; simp
    exact this
  · intro x hx hxa hxb
    by_contra hn
    have hm : x ∈ N.vertsᶜ := hn
    rw [heq] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    exact hm.elim hxa hxb

/-- Restriction to an actual ambient component, without inserting unmatched vertices. -/
def componentMatching (M : G.Subgraph) (C : G.ConnectedComponent) : C.toSimpleGraph.Subgraph where
  verts := {x | x.val ∈ M.verts}
  Adj x y := M.Adj x.val y.val
  adj_sub h := h.adj_sub
  edge_vert h := h.fst_mem
  symm := ⟨by intro x y h; exact h.symm⟩

theorem componentMatching_isMatching (M : G.Subgraph) (hM : M.IsMatching)
    (C : G.ConnectedComponent) : (componentMatching M C).IsMatching := by
  intro x hx
  obtain ⟨y, hxy, hy⟩ := hM hx
  have hyC : y ∈ C.supp := by
    change G.connectedComponentMk y = C
    exact (ConnectedComponent.sound hxy.adj_sub.reachable).symm.trans x.property
  refine ⟨⟨y, hyC⟩, hxy, ?_⟩
  intro z hz
  exact Subtype.ext (hy z.val hz)

private noncomputable def matchedPartition (M : G.Subgraph) :
    (Σ C : G.ConnectedComponent, (componentMatching M C).verts) ≃ M.verts where
  toFun x := ⟨x.2.val.val, x.2.property⟩
  invFun x := ⟨G.connectedComponentMk x.val, ⟨⟨x.val, rfl⟩, x.property⟩⟩
  left_inv x := by
    rcases x with ⟨C, ⟨⟨x, hx⟩, hm⟩⟩
    have hc : G.connectedComponentMk x = C := hx
    subst C
    rfl
  right_inv x := rfl

theorem sum_componentMatching_edges (M : G.Subgraph) (hM : M.IsMatching) :
    letI := Fintype.ofFinite G.ConnectedComponent
    ∑ C, (componentMatching M C).edgeSet.ncard = M.edgeSet.ncard := by
  classical
  letI := Fintype.ofFinite G.ConnectedComponent
  have hp := Nat.card_congr (matchedPartition M)
  simp only [Nat.card_sigma, Nat.card_coe_set_eq] at hp
  have hc (C : G.ConnectedComponent) :=
    GallaiDeficiency.matching_card (componentMatching_isMatching M hM C)
  simp_rw [hc] at hp
  rw [← Finset.mul_sum, GallaiDeficiency.matching_card hM] at hp
  omega

theorem component_union_connected (M N : G.Subgraph)
    (hcover : ∀ x y, G.Adj x y ↔ M.Adj x y ∨ N.Adj x y)
    (C : G.ConnectedComponent) :
    ((componentMatching M C).spanningCoe ⊔ (componentMatching N C).spanningCoe).Connected := by
  have he : (componentMatching M C).spanningCoe ⊔ (componentMatching N C).spanningCoe =
      C.toSimpleGraph := by
    ext x y
    exact (hcover x.val y.val).symm
  rw [he]
  exact C.connected_toSimpleGraph

/-- The actual number of positive-surplus components pays the global matching surplus. -/
theorem positive_component_count (M N : G.Subgraph) (hM : M.IsMatching)
    (hcover : ∀ x y, G.Adj x y ↔ M.Adj x y ∨ N.Adj x y)
    (hN : N.IsMatching) (k : ℕ) (hk : N.edgeSet.ncard + k ≤ M.edgeSet.ncard) :
    k ≤ {C : G.ConnectedComponent |
      (componentMatching N C).edgeSet.ncard < (componentMatching M C).edgeSet.ncard}.ncard := by
  classical
  letI := Fintype.ofFinite G.ConnectedComponent
  have hbound (C : G.ConnectedComponent) :
      (componentMatching M C).edgeSet.ncard ≤ (componentMatching N C).edgeSet.ncard +
        if (componentMatching N C).edgeSet.ncard < (componentMatching M C).edgeSet.ncard
        then 1 else 0 := by
    split_ifs with h
    · exact connected_union_surplus_bound _ _ (componentMatching_isMatching M hM C)
        (component_union_connected M N hcover C)
    · omega
  have hs := Finset.sum_le_sum (fun C (_ : C ∈ Finset.univ) => hbound C)
  rw [Finset.sum_add_distrib, sum_componentMatching_edges M hM,
    sum_componentMatching_edges N hN] at hs
  have hi : (∑ C : G.ConnectedComponent,
      if (componentMatching N C).edgeSet.ncard < (componentMatching M C).edgeSet.ncard
      then 1 else 0) = {C : G.ConnectedComponent |
      (componentMatching N C).edgeSet.ncard < (componentMatching M C).edgeSet.ncard}.ncard := by
    simp [← Set.fintypeCard_eq_ncard, Fintype.card_subtype]
  rw [hi] at hs
  omega

open GallaiTwins

def twinMatching (G : SimpleGraph V) (A : Set V) : (doubled G A).Subgraph where
  verts := {x | project x ∉ A}
  Adj x y := x ≠ y ∧ project x = project y
  adj_sub h := Or.inl h
  edge_vert := by
    intro x y h
    rcases h with ⟨hne, he⟩
    cases x with
    | inl x =>
      cases y with
      | inl y => exact False.elim (hne (congrArg Sum.inl he))
      | inr y =>
        change x ∉ A
        change x = y.val at he
        exact he.symm ▸ y.property
    | inr x => exact x.property
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.symm⟩⟩

theorem twinMatching_isMatching (G : SimpleGraph V) (A : Set V) :
    (twinMatching G A).IsMatching := by
  intro x hx
  cases x with
  | inl x =>
    refine ⟨Sum.inr ⟨x, hx⟩, ⟨by simp, rfl⟩, ?_⟩
    intro y hy
    cases y with
    | inl y => exact False.elim (hy.1 (congrArg Sum.inl hy.2))
    | inr y => exact congrArg Sum.inr (Subtype.ext hy.2.symm)
  | inr x =>
    refine ⟨Sum.inl x.val, ⟨by simp, rfl⟩, ?_⟩
    intro y hy
    cases y with
    | inl y => exact congrArg Sum.inl hy.2.symm
    | inr y => exact False.elim (hy.1 (congrArg Sum.inr (Subtype.ext hy.2)))

private noncomputable def twinVertices (G : SimpleGraph V) (A : Set V) :
    (twinMatching G A).verts ≃ ↥(Aᶜ) ⊕ ↥(Aᶜ) where
  toFun x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | inl x => exact .inl ⟨x, hx⟩
    | inr x => exact .inr x
  invFun x := Sum.elim (fun x => ⟨Sum.inl x.val, x.property⟩)
    (fun x => ⟨Sum.inr x, x.property⟩) x
  left_inv x := by rcases x with ⟨x, hx⟩; cases x <;> rfl
  right_inv x := by cases x <;> rfl

theorem twinMatching_card (G : SimpleGraph V) (A : Set V) :
    (twinMatching G A).edgeSet.ncard = Aᶜ.ncard := by
  classical
  have hc := Nat.card_congr (twinVertices G A)
  simp only [Nat.card_sum, Nat.card_coe_set_eq] at hc
  have hm := GallaiDeficiency.matching_card (twinMatching_isMatching G A)
  omega

def unionLeft (M N : G.Subgraph) : (M.spanningCoe ⊔ N.spanningCoe).Subgraph where
  verts := M.verts
  Adj x y := M.Adj x y
  adj_sub h := Or.inl h
  edge_vert h := h.fst_mem
  symm := ⟨by intro x y h; exact h.symm⟩

def unionRight (M N : G.Subgraph) : (M.spanningCoe ⊔ N.spanningCoe).Subgraph where
  verts := N.verts
  Adj x y := N.Adj x y
  adj_sub h := Or.inr h
  edge_vert h := h.fst_mem
  symm := ⟨by intro x y h; exact h.symm⟩

theorem fiber_connected (G : SimpleGraph V) (A : Set V)
    (M : (doubled G A).Subgraph) (u v : CopyVertex A) (hp : project u = project v) :
    (M.spanningCoe ⊔ (twinMatching G A).spanningCoe).Reachable u v := by
  by_cases he : u = v
  · subst v; exact .refl _
  · exact (show (M.spanningCoe ⊔ (twinMatching G A).spanningCoe).Adj u v from
      Or.inr ⟨he, hp⟩).reachable

theorem projected_supports_disjoint (G : SimpleGraph V) (A : Set V)
    (M : (doubled G A).Subgraph)
    {C D : (M.spanningCoe ⊔ (twinMatching G A).spanningCoe).ConnectedComponent}
    (hCD : C ≠ D) : Disjoint (project '' C.supp) (project '' D.supp) := by
  rw [Set.disjoint_left]
  rintro x ⟨u, hu, hux⟩ ⟨v, hv, hvx⟩
  have he := ConnectedComponent.sound (fiber_connected G A M u v (hux.trans hvx.symm))
  exact hCD (hu.symm.trans (he.trans hv))

private theorem weak_reachable {X Y : Type*} {H : SimpleGraph X} {J : SimpleGraph Y}
    (f : X → Y) (hf : ∀ x y, H.Adj x y → f x = f y ∨ J.Adj (f x) (f y))
    {x y : X} (hr : H.Reachable x y) : J.Reachable (f x) (f y) := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact .refl _
  | @cons x z y hx p ih =>
    apply Reachable.trans (v := f z) _ ih
    rcases hf x z hx with he | he
    · rw [he]
    · exact he.reachable

theorem terminal_projection_injective (A : Set V) {u v : CopyVertex A}
    (hu : project u ∈ A) (hv : project v ∈ A) (he : project u = project v) : u = v := by
  cases u with
  | inl u =>
    cases v with
    | inl v => exact congrArg Sum.inl he
    | inr v => exact False.elim (v.property hv)
  | inr u => exact False.elim (u.property hu)

structure APath (G : SimpleGraph V) (A : Set V) where
  first : V
  last : V
  walk : G.Walk first last
  distinct : first ≠ last
  first_mem : first ∈ A
  last_mem : last ∈ A
  simple : walk.IsPath
  internal : ∀ x ∈ walk.support, x ≠ first → x ≠ last → x ∉ A

abbrev twinUnion (G : SimpleGraph V) (A : Set V) (M : (doubled G A).Subgraph) :=
  M.spanningCoe ⊔ (twinMatching G A).spanningCoe

theorem positive_projected_path (G : SimpleGraph V) (A : Set V)
    (M : (doubled G A).Subgraph) (hM : M.IsMatching)
    (C : (twinUnion G A M).ConnectedComponent)
    (hpos : (componentMatching (unionRight M (twinMatching G A)) C).edgeSet.ncard <
      (componentMatching (unionLeft M (twinMatching G A)) C).edgeSet.ncard) :
    ∃ p : APath G A, ∀ x ∈ p.walk.support, x ∈ project '' C.supp := by
  classical
  let L := unionLeft M (twinMatching G A)
  let R := unionRight M (twinMatching G A)
  have hL : L.IsMatching := hM
  have hR : R.IsMatching := twinMatching_isMatching G A
  have hcover : ∀ x y, (twinUnion G A M).Adj x y ↔ L.Adj x y ∨ R.Adj x y :=
    fun _ _ => Iff.rfl
  have hc := component_union_connected L R hcover C
  obtain ⟨a, b, p, hab, ha, hb, hp, hint⟩ := connected_union_path
    (componentMatching L C) (componentMatching R C)
    (componentMatching_isMatching L hL C) (componentMatching_isMatching R hR C) hc hpos
  have haA : project a.val ∈ A := by simpa [componentMatching, R, unionRight, twinMatching] using ha
  have hbA : project b.val ∈ A := by simpa [componentMatching, R, unionRight, twinMatching] using hb
  have hne : project a.val ≠ project b.val := by
    intro he
    exact hab (Subtype.ext (terminal_projection_injective A haA hbA he))
  let S : Set V := project '' C.supp
  let f : C.supp → S := fun x => ⟨project x.val, ⟨x.val, x.property, rfl⟩⟩
  have hf : ∀ x y, ((componentMatching L C).spanningCoe ⊔
      (componentMatching R C).spanningCoe).Adj x y →
      f x = f y ∨ (G.induce S).Adj (f x) (f y) := by
    intro x y h
    have hd : (doubled G A).Adj x.val y.val := by
      rcases h with h | h
      · exact M.adj_sub h
      · exact Or.inl h
    rcases hd with ⟨_, he⟩ | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr he
  have hr := weak_reachable f hf p.reachable
  obtain ⟨q, hq⟩ : ∃ q : (G.induce S).Walk (f a) (f b), q.IsPath :=
    hr.elim_path (fun q => ⟨q.val, q.property⟩)
  let inc : G.induce S →g G := ⟨Subtype.val, fun h => h⟩
  have hs : ∀ x ∈ (q.map inc).support, x ∈ S := by
    intro x hx
    rw [Walk.support_map] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact y.property
  have hi : ∀ x ∈ (q.map inc).support, x ≠ project a.val → x ≠ project b.val → x ∉ A := by
    intro x hx hxa hxb hxA
    obtain ⟨z, hz, hzx⟩ := hs x hx
    let zz : C.supp := ⟨z, hz⟩
    have hnot : zz ∉ (componentMatching R C).verts := by
      change ¬ project z ∉ A
      exact not_not.mpr (hzx.symm ▸ hxA)
    have ht := connected_union_two_unmatched (componentMatching L C) (componentMatching R C)
      (componentMatching_isMatching L hL C) (componentMatching_isMatching R hR C) hc hpos
    have heq : (componentMatching R C).vertsᶜ = {a, b} := by
      symm
      apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite _)
      · intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        exact hy.elim (fun he => he ▸ ha) (fun he => he ▸ hb)
      · simpa [ht, hab] using (le_refl (2 : ℕ))
    have hzab : zz = a ∨ zz = b := by
      change zz ∈ (componentMatching R C).vertsᶜ at hnot
      simpa [heq] using hnot
    rcases hzab with he | he
    · exact hxa (hzx.symm.trans (congrArg (fun y : C.supp => project y.val) he))
    · exact hxb (hzx.symm.trans (congrArg (fun y : C.supp => project y.val) he))
  exact ⟨⟨project a.val, project b.val, q.map inc, hne, haA, hbA,
    hq.map Subtype.val_injective, hi⟩, hs⟩

/-- An arbitrary surplus matching gives original simple terminal paths with disjoint full supports. -/
theorem paths_of_doubled_matching (G : SimpleGraph V) (A : Set V) (k : ℕ)
    (M : (doubled G A).Subgraph) (hM : M.IsMatching)
    (hk : Aᶜ.ncard + k ≤ M.edgeSet.ncard) :
    ∃ p : Fin k → APath G A,
      Pairwise fun i j => Disjoint {x | x ∈ (p i).walk.support} {x | x ∈ (p j).walk.support} := by
  classical
  let L := unionLeft M (twinMatching G A)
  let R := unionRight M (twinMatching G A)
  have hL : L.IsMatching := hM
  have hR : R.IsMatching := twinMatching_isMatching G A
  have hcover : ∀ x y, (twinUnion G A M).Adj x y ↔ L.Adj x y ∨ R.Adj x y :=
    fun _ _ => Iff.rfl
  have hkk : R.edgeSet.ncard + k ≤ L.edgeSet.ncard := by
    change (twinMatching G A).edgeSet.ncard + k ≤ M.edgeSet.ncard
    rwa [twinMatching_card]
  have hcount := positive_component_count L R hL hcover hR k hkk
  let P := {C : (twinUnion G A M).ConnectedComponent |
    (componentMatching R C).edgeSet.ncard < (componentMatching L C).edgeSet.ncard}
  letI := Fintype.ofFinite P
  have hcard : Fintype.card (Fin k) ≤ Fintype.card P := by
    simpa only [Fintype.card_fin, Set.fintypeCard_eq_ncard] using hcount
  let e : Fin k ↪ P := Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  have hex (i : Fin k) := positive_projected_path G A M hM (e i).val (e i).property
  choose p hp using hex
  refine ⟨p, ?_⟩
  intro i j hij
  have hne : (e i).val ≠ (e j).val := by
    intro he
    exact hij (e.injective (Subtype.ext he))
  have hd := projected_supports_disjoint G A M hne
  rw [Set.disjoint_left] at hd ⊢
  intro x hx hy
  exact hd (hp i x hx) (hp j x hy)

end Erdos642.DenseMask20261019.GallaiPaths








