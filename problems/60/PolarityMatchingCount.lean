import PolarityTransfer
import PolarityExactCount
import MarkedPathBijection

namespace Erdos60.Geometry
open scoped Classical
variable {P L : Type*} [Membership P L] [Fintype P] [DecidableEq P]

/-- Every canonical endpoint-marked edge-set path has an oriented geometry-path
representative, reversing its internal pair when its endpoint witness reverses. -/
theorem Polarity.base_path_edges_surjective
    (π : Polarity (P := P) (L := L)) (u v : P)
    (p : Finset (Sym2 P)) (hp : p ∈ Counting.baseThreePaths π.graph s(u,v)) :
    ∃ r : π.ThreePath u v, r.edges π = p := by
  obtain ⟨hshape,hsub⟩ := (Counting.mem_baseThreePaths _ _ _).mp hp
  obtain ⟨a,x,y,b,he,hd,rfl⟩ := hshape
  have hax : π.graph.Adj a x := by
    have := hsub (by simp : s(a,x) ∈ ({s(a,x),s(x,y),s(y,b)} : Finset (Sym2 P)))
    simpa using this
  have hxy : π.graph.Adj x y := by
    have := hsub (by simp : s(x,y) ∈ ({s(a,x),s(x,y),s(y,b)} : Finset (Sym2 P)))
    simpa using this
  have hyb : π.graph.Adj y b := by
    have := hsub (by simp : s(y,b) ∈ ({s(a,x),s(x,y),s(y,b)} : Finset (Sym2 P)))
    simpa using this
  simp only [Sym2.eq_iff] at he
  rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · refine ⟨⟨(x,y),hax,hxy,hyb⟩,?_⟩
    ext e
    simp only [Polarity.ThreePath.edges,Finset.mem_insert,Finset.mem_singleton]
  · refine ⟨⟨(y,x),hyb.symm,hxy.symm,hax.symm⟩,?_⟩
    ext e
    simp [Polarity.ThreePath.edges,Sym2.eq_swap,or_comm,or_left_comm]

/-- Canonical unordered path edge sets have exactly the cardinality of actual
oriented three-paths in a polarity graph with fixed nonadjacent endpoints. -/
theorem Polarity.baseThreePaths_card [Configuration.ProjectivePlane P L] [Finite L]
    (π : Polarity (P := P) (L := L)) {u v : P} (huv : u ≠ v)
    (hnadj : ¬π.graph.Adj u v) :
    (Counting.baseThreePaths π.graph s(u,v)).card = Nat.card (π.ThreePath u v) := by
  classical
  let : Fintype (π.ThreePath u v) := by unfold Polarity.ThreePath; infer_instance
  have hi : Set.InjOn (fun p : π.ThreePath u v => p.edges π) ((Finset.univ : Finset (π.ThreePath u v)) : Set _) := by
    intro p hp r hr heq
    dsimp only at heq
    by_contra hne
    have hd := Polarity.ThreePath.edge_disjoint π huv hnadj p r hne
    have hm : s(u,p.val.1) ∈ p.edges π := by simp [Polarity.ThreePath.edges]
    have hm' : s(u,p.val.1) ∈ r.edges π := heq ▸ hm
    exact Finset.disjoint_left.mp hd hm hm'
  have hf : Counting.baseThreePaths π.graph s(u,v) =
      Finset.univ.image (fun p : π.ThreePath u v => p.edges π) := by
    ext p
    constructor
    · intro hp
      obtain ⟨r,rfl⟩ := π.base_path_edges_surjective u v p hp
      exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
    · intro hp
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
      exact (Counting.mem_baseThreePaths _ _ _).mpr
        ⟨Polarity.ThreePath.counting_shape π huv hnadj r,
          Polarity.ThreePath.edges_subset π r⟩
  rw [hf,Finset.card_image_iff.mpr hi]
  simp [Nat.card_eq_fintype_card]

/-- Actual ordinary C4 count after adding any matching on the absolute set.
The exact path supply is proved by source Lemma 2.5, not a count premise. -/
theorem Polarity.matching_absolute_cycle_count
    [Configuration.ProjectivePlane P L] [Finite L]
    (π : Polarity (P := P) (L := L)) (K : SimpleGraph P)
    (hm : Counting.IsMatchingGraph K)
    (hsupport : ∀ a b, K.Adj a b → π.Absolute a ∧ π.Absolute b) :
    Counting.cycleCount (π.graph ⊔ K) = K.edgeFinset.card *
      (Configuration.ProjectivePlane.order P L - 1) := by
  classical
  apply Counting.matching_exact_cycle_count_canonical π.graph K {a | π.Absolute a}
  · apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨C,hC⟩
    obtain ⟨hsub,a,b,c,d,hd,rfl⟩ := (Counting.mem_cycles _ _).mp hC
    have hab : π.graph.Adj a b := by have := hsub (by simp [Counting.fourEdges] : s(a,b) ∈ Counting.fourEdges a b c d); simpa using this
    have hbc : π.graph.Adj b c := by have := hsub (by simp [Counting.fourEdges] : s(b,c) ∈ Counting.fourEdges a b c d); simpa using this
    have hcd : π.graph.Adj c d := by have := hsub (by simp [Counting.fourEdges] : s(c,d) ∈ Counting.fourEdges a b c d); simpa using this
    have hda : π.graph.Adj d a := by have := hsub (by simp [Counting.fourEdges] : s(d,a) ∈ Counting.fourEdges a b c d); simpa using this
    have hac : a ≠ c := by
      intro h
      have := (List.nodup_cons.mp hd).1
      exact this (by simp [h])
    have hbd : b ≠ d := by
      intro h
      have := (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1
      exact this (by simp [h])
    exact π.no_four_cycle hac hbd hab hbc hcd hda
  · exact hm
  · exact hsupport
  · intro a ha b hb
    exact π.absolute_not_adjacent ha hb
  · intro e he
    revert he
    refine Sym2.inductionOn e (fun u v => ?_)
    intro he
    have hK : K.Adj u v := by simpa using he
    obtain ⟨hu,hv⟩ := hsupport u v hK
    have hn := π.absolute_not_adjacent hu hv
    rw [π.baseThreePaths_card hK.ne hn]
    exact (π.three_path_count_min_iff_absolute hK.ne hn).mpr ⟨hu,hv⟩

end Erdos60.Geometry
