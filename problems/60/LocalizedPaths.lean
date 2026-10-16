import PolarityTransfer

namespace Erdos60.Geometry
open scoped Classical
variable {P L : Type*} [Membership P L] [Fintype P] [DecidableEq P]

/-- Actual missing base edges with at least one endpoint outside the core. -/
noncomputable def outsideMissing (G Q : SimpleGraph P) (S : Finset P) : Finset (Sym2 P) :=
  (Q.edgeFinset \ G.edgeFinset).filter (fun e => ¬e.toFinset ⊆ S)

omit [Fintype P] in
theorem Polarity.internal_core_path_count [Configuration.Nondegenerate P L]
    (π : Polarity (P := P) (L := L)) {u v : P} (hn : ¬π.graph.Adj u v)
    (paths : Finset (π.ThreePath u v)) (S : Finset P) :
    (paths.filter (fun p => p.val.1 ∈ S ∨ p.val.2 ∈ S)).card ≤ 2 * S.card := by
  classical
  have hfirst : (paths.filter (fun p => p.val.1 ∈ S)).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun p : π.ThreePath u v => p.val.1)
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p hp r hr heq
      dsimp only at heq
      apply Subtype.ext
      apply Prod.ext heq
      exact π.three_path_right_unique hn p.property.1 p.property.2.1 p.property.2.2
        (heq ▸ r.property.2.1) r.property.2.2
  have hsecond : (paths.filter (fun p => p.val.2 ∈ S)).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun p : π.ThreePath u v => p.val.2)
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p hp r hr heq
      dsimp only at heq
      apply Subtype.ext
      apply Prod.ext ?_ heq
      exact π.three_path_left_unique hn p.property.1 p.property.2.1 p.property.2.2
        r.property.1 (heq.symm ▸ r.property.2.1)
  have heq : paths.filter (fun p => p.val.1 ∈ S ∨ p.val.2 ∈ S) =
      paths.filter (fun p => p.val.1 ∈ S) ∪ paths.filter (fun p => p.val.2 ∈ S) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  rw [heq]
  have hu := Finset.card_union_le (paths.filter (fun p => p.val.1 ∈ S))
    (paths.filter (fun p => p.val.2 ∈ S))
  omega

omit [Fintype P] in
theorem Polarity.ThreePath.no_core_edge
    (π : Polarity (P := P) (L := L)) {u v : P} (p : π.ThreePath u v) (S : Finset P)
    (hfirst : p.val.1 ∉ S) (hsecond : p.val.2 ∉ S) :
    ∀ e ∈ p.edges π, ¬e.toFinset ⊆ S := by
  classical
  intro e he hsub
  simp only [ThreePath.edges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact hfirst (hsub (by simp [Sym2.toFinset_mk_eq]))
  · exact hfirst (hsub (by simp [Sym2.toFinset_mk_eq]))
  · exact hsecond (hsub (by simp [Sym2.toFinset_mk_eq]))

/-- The localized survivor family is constructed from actual geometric paths.
Internal missing edges are paid by 2|S| and other missing edges by their actual
outside-endpoint edge count. -/
theorem Polarity.localized_counting_path_family [Configuration.ProjectivePlane P L] [Finite L]
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (S : Finset P)
    {u v : P} (huv : u ≠ v) (hn : ¬π.graph.Adj u v) :
    ∃ R : Finset (Finset (Sym2 P)),
      (∀ p ∈ R, Counting.IsThreePath s(u,v) p ∧ p ⊆ (π.graph ⊓ G).edgeFinset) ∧
      (∀ p ∈ R, ∀ r ∈ R, p ≠ r → Disjoint p r) ∧
      Configuration.ProjectivePlane.order P L - 1 - 2 * S.card -
        (outsideMissing G π.graph S).card ≤ R.card := by
  classical
  obtain ⟨paths,hnum,hdis⟩ := π.exists_disjoint_three_paths huv hn
  let good := paths.filter (fun p => ¬(p.val.1 ∈ S ∨ p.val.2 ∈ S))
  have hbad := π.internal_core_path_count hn paths S
  have hsplit := Finset.card_filter_add_card_filter_not (s := paths)
    (p := fun p => p.val.1 ∈ S ∨ p.val.2 ∈ S)
  have hgoodnum : Configuration.ProjectivePlane.order P L - 1 - 2 * S.card ≤ good.card := by
    dsimp [good]
    omega
  let E := good.image (fun p => p.edges π)
  have hEcard : E.card = good.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb heq
    dsimp only at heq
    by_contra hne
    have hd := hdis a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hne
    have hm : s(u,a.val.1) ∈ a.edges π := by simp [Polarity.ThreePath.edges]
    have hm' : s(u,a.val.1) ∈ b.edges π :=
      (congrArg (fun z : Finset (Sym2 P) => s(u,a.val.1) ∈ z) heq).mp hm
    exact Finset.disjoint_left.mp hd hm hm'
  have hEbase : ∀ p ∈ E, Counting.IsThreePath s(u,v) p ∧ p ⊆ π.graph.edgeFinset ∧
      ∀ e ∈ p, ¬e.toFinset ⊆ S := by
    intro p hp
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
    have hr' := Finset.mem_filter.mp hr
    have havoid := not_or.mp hr'.2
    exact ⟨Polarity.ThreePath.counting_shape π huv hn r,
      Polarity.ThreePath.edges_subset π r,
      Polarity.ThreePath.no_core_edge π r S havoid.1 havoid.2⟩
  have hEdis : ∀ p ∈ E, ∀ r ∈ E, p ≠ r → Disjoint p r := by
    intro p hp r hr hne
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hr
    exact hdis a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (fun h => hne (congrArg (fun p => p.edges π) h))
  let D := outsideMissing G π.graph S
  let R := E.filter (fun p => Disjoint p D)
  have hRactual : ∀ p ∈ R, p ⊆ G.edgeFinset := by
    intro p hp e he
    have hp' := Finset.mem_filter.mp hp
    by_contra hnot
    have heD : e ∈ D := Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨(hEbase p hp'.1).2.1 he,hnot⟩,(hEbase p hp'.1).2.2 e he⟩
    exact Finset.disjoint_left.mp hp'.2 he heD
  refine ⟨R,?_,?_,?_⟩
  · intro p hp
    have hpE := (Finset.mem_filter.mp hp).1
    refine ⟨(hEbase p hpE).1,?_⟩
    intro e he
    have heQ := (hEbase p hpE).2.1 he
    have heG := hRactual p hp he
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_inf, Set.mem_inter_iff] at heQ heG ⊢
    exact ⟨heQ,heG⟩
  · intro p hp r hr hne
    exact hEdis p (Finset.mem_filter.mp hp).1 r (Finset.mem_filter.mp hr).1 hne
  · have hret := Counting.retained_ge_sub_missing E D hEdis
    have hEnum : Configuration.ProjectivePlane.order P L - 1 - 2 * S.card ≤ E.card := by
      rw [hEcard]
      exact hgoodnum
    exact (Nat.sub_le_sub_right hEnum D.card).trans hret

theorem Polarity.localized_family_for_added_edge [Configuration.ProjectivePlane P L] [Finite L]
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (S : Finset P)
    (e : Sym2 P) (he : e ∈ G.edgeFinset \ π.graph.edgeFinset) :
    ∃ R : Finset (Finset (Sym2 P)),
      (∀ p ∈ R, Counting.IsThreePath e p ∧ p ⊆ (π.graph ⊓ G).edgeFinset) ∧
      (∀ p ∈ R, ∀ r ∈ R, p ≠ r → Disjoint p r) ∧
      Configuration.ProjectivePlane.order P L - 1 - 2 * S.card -
        (outsideMissing G π.graph S).card ≤ R.card := by
  classical
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hadj : G.Adj u v := by simpa using (Finset.mem_sdiff.mp he).1
    have hnadj : ¬π.graph.Adj u v := by simpa using (Finset.mem_sdiff.mp he).2
    exact π.localized_counting_path_family G S hadj.ne hnadj

/-- The localized retained-path bound on the actual host, with every path
supplier/counting obligation discharged. No assumption bounds missing edges
inside S; they are paid by the internal-vertex count. -/
theorem Polarity.localized_cycle_lower [Configuration.ProjectivePlane P L] [Finite L]
    (π : Polarity (P := P) (L := L)) (G : SimpleGraph P) (S : Finset P) :
    (G.edgeFinset \ π.graph.edgeFinset).card *
      (Configuration.ProjectivePlane.order P L - 1 - 2 * S.card -
        (outsideMissing G π.graph S).card) ≤ Counting.cycleCount G := by
  classical
  let A := G.edgeFinset \ π.graph.edgeFinset
  let H := π.graph ⊓ G
  let k := Configuration.ProjectivePlane.order P L - 1 - 2 * S.card -
    (outsideMissing G π.graph S).card
  have hex : ∀ e : Sym2 P, ∃ paths : Finset (Finset (Sym2 P)), e ∈ A →
      (∀ p ∈ paths, Counting.IsThreePath e p ∧ p ⊆ H.edgeFinset) ∧
      (∀ p ∈ paths, ∀ r ∈ paths, p ≠ r → Disjoint p r) ∧ k ≤ paths.card := by
    intro e
    by_cases he : e ∈ A
    · obtain ⟨paths,hp⟩ := π.localized_family_for_added_edge G S e he
      refine ⟨paths,fun _ => ?_⟩
      simpa only [Finset.subset_iff,SimpleGraph.mem_edgeFinset] using hp
    · exact ⟨∅,fun h => False.elim (he h)⟩
  choose paths hp using hex
  have hHsub : H.edgeFinset ⊆ G.edgeFinset := by
    intro e he
    simp only [H, SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_inf, Set.mem_inter_iff] at he ⊢
    exact he.2
  have hmissing : H.edgeFinset \ G.edgeFinset = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hHsub
  have hA : ∀ e ∈ A, e ∈ G.edgeFinset ∧ e ∉ H.edgeFinset := by
    intro e he
    refine ⟨(Finset.mem_sdiff.mp he).1,?_⟩
    intro heH
    simp only [H, SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_inf, Set.mem_inter_iff] at heH
    exact (Finset.mem_sdiff.mp he).2 (SimpleGraph.mem_edgeFinset.mpr heH.1)
  have hmissing' : @SimpleGraph.edgeFinset P H H.fintypeEdgeSet \ G.edgeFinset = ∅ := by
    apply Finset.sdiff_eq_empty_iff_subset.mpr
    intro e he
    simp only [H, SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_inf, Set.mem_inter_iff] at he ⊢
    exact he.2
  have hc := Counting.retained_path_count G H A paths k
    (by simpa only [SimpleGraph.mem_edgeFinset] using hA)
    (by
      intro e he p hp'
      simpa only [Finset.subset_iff,SimpleGraph.mem_edgeFinset] using (hp e he).1 p hp')
    (fun e he p hp' r hr hne => (hp e he).2.1 p hp' r hr hne)
    (fun e he => (hp e he).2.2)
  have hnormalize (T : SimpleGraph P) (i : Fintype T.edgeSet) :
      @SimpleGraph.edgeFinset P T i = @SimpleGraph.edgeFinset P T T.fintypeEdgeSet :=
    congrArg (fun i => @SimpleGraph.edgeFinset P T i) (Subsingleton.elim i T.fintypeEdgeSet)
  simp only [hnormalize] at hmissing'
  simpa only [hnormalize,hmissing',Finset.card_empty,Nat.sub_zero] using hc

#print axioms Polarity.internal_core_path_count
#print axioms Polarity.ThreePath.no_core_edge
#print axioms Polarity.localized_counting_path_family
#print axioms Polarity.localized_family_for_added_edge
#print axioms Polarity.localized_cycle_lower

end Erdos60.Geometry
