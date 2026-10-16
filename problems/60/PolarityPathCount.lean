import PolarityPaths

namespace Erdos60.Geometry
variable {P L : Type*} [Membership P L]

/-- Every neighbor apart from the single point where the two endpoint polar
lines intersect supplies a genuine three-edge path. -/
theorem Polarity.exists_three_path_of_neighbor [Configuration.ProjectivePlane P L]
    (π : Polarity (P := P) (L := L)) {u v w a : P}
    (hwu : w ∈ π.line u) (hwv : w ∈ π.line v)
    (huv : u ≠ v) (hnadj : ¬π.graph.Adj u v)
    (hua : π.graph.Adj u a) (haw : a ≠ w) :
    ∃ p : π.ThreePath u v, p.val.1 = a := by
  have hav : a ≠ v := by intro h; exact hnadj (h ▸ hua)
  have hlines : π.line a ≠ π.line v := fun h => hav (π.line.injective h)
  obtain ⟨b, hb, _⟩ := Configuration.HasPoints.existsUnique_point P L _ _ hlines
  have hnotav : a ∉ π.line v := by
    intro ha
    have hau := (π.reciprocal u a).mp hua.2
    rcases Configuration.Nondegenerate.eq_or_eq hau hwu ha hwv with h | h
    · exact haw h
    · exact huv (π.line.injective h)
  have hab : a ≠ b := by intro h; exact hnotav (h ▸ hb.2)
  have hbv : b ≠ v := by
    intro h
    have hv : v ∈ π.line a := h ▸ hb.1
    exact hnotav ((π.reciprocal v a).mp hv)
  exact ⟨⟨(a,b), hua, ⟨hab, (π.reciprocal b a).mp hb.1⟩, ⟨hbv, hb.2⟩⟩, rfl⟩

/-- Actual three-path count lower bound for a fixed nonedge of an actual
finite polarity graph. This assumes no path-count source theorem. -/
theorem Polarity.three_path_count_lower [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L))
    {u v : P} (huv : u ≠ v) (hnadj : ¬π.graph.Adj u v) :
    Configuration.ProjectivePlane.order P L - 1 ≤ Nat.card (π.ThreePath u v) := by
  classical
  let : Fintype (π.ThreePath u v) := by unfold Polarity.ThreePath; infer_instance
  obtain ⟨w, hw, _⟩ := Configuration.HasPoints.existsUnique_point P L
    (π.line u) (π.line v) (fun h => huv (π.line.injective h))
  let s : Finset P := (π.graph.neighborFinset u).erase w
  have hex : ∀ a : s, ∃ p : π.ThreePath u v, p.val.1 = a.val := by
    intro a
    have ha := Finset.mem_erase.mp a.property
    exact π.exists_three_path_of_neighbor hw.1 hw.2 huv hnadj
      (by simpa only [SimpleGraph.mem_neighborFinset] using ha.2) ha.1
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact (hf a).symm.trans ((congrArg (fun p : π.ThreePath u v => p.val.1) hab).trans (hf b))
  have hcard : s.card ≤ Nat.card (π.ThreePath u v) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
      (Nat.card_le_card_of_injective f hfinj)
  have hdeg : Configuration.ProjectivePlane.order P L ≤ π.graph.degree u := by
    rcases π.degree_eq_order_or_succ u with h | h <;> omega
  have herase := Finset.pred_card_le_card_erase (s := π.graph.neighborFinset u) (a := w)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at herase
  exact (Nat.sub_le_sub_right hdeg 1).trans (herase.trans hcard)

/-- Explicit simplicity correspondence for the ordered-pair path representation. -/
theorem Polarity.ThreePath.vertices_distinct
    (π : Polarity (P := P) (L := L)) {u v : P} (huv : u ≠ v)
    (hnadj : ¬π.graph.Adj u v) (p : π.ThreePath u v) :
    u ≠ p.val.1 ∧ u ≠ p.val.2 ∧ u ≠ v ∧ p.val.1 ≠ p.val.2 ∧
      p.val.1 ≠ v ∧ p.val.2 ≠ v := by
  obtain ⟨⟨a,b⟩, ha, hab, hb⟩ := p
  refine ⟨ha.ne, ?_, huv, hab.ne, ?_, hb.ne⟩
  · intro h
    exact hnadj (h ▸ hb)
  · intro h
    exact hnadj (h ▸ ha)

/-- A finite actual family ready for retained-path counting: at least q−1
simple paths, with pairwise disjoint actual undirected edge Finsets. -/
theorem Polarity.exists_disjoint_three_paths [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L))
    {u v : P} (huv : u ≠ v) (hnadj : ¬π.graph.Adj u v) :
    ∃ paths : Finset (π.ThreePath u v),
      Configuration.ProjectivePlane.order P L - 1 ≤ paths.card ∧
      (∀ p ∈ paths, ∀ r ∈ paths, p ≠ r → Disjoint (p.edges π) (r.edges π)) := by
  classical
  let : Fintype (π.ThreePath u v) := by unfold Polarity.ThreePath; infer_instance
  refine ⟨Finset.univ, ?_, ?_⟩
  · simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using
      π.three_path_count_lower huv hnadj
  · intro p _ r _ hpr
    exact Polarity.ThreePath.edge_disjoint π huv hnadj p r hpr

#print axioms Polarity.exists_three_path_of_neighbor
#print axioms Polarity.three_path_count_lower
#print axioms Polarity.ThreePath.vertices_distinct
#print axioms Polarity.exists_disjoint_three_paths
end Erdos60.Geometry
