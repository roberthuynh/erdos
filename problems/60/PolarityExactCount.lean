import PolarityPathCount

namespace Erdos60.Geometry
variable {P L : Type*} [Membership P L]

/-- Projection to the first internal vertex is injective for fixed nonadjacent endpoints. -/
theorem Polarity.three_path_count_le_degree [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L))
    {u v : P} (hnadj : ¬π.graph.Adj u v) :
    letI := Classical.decRel π.graph.Adj
    Nat.card (π.ThreePath u v) ≤ π.graph.degree u := by
  classical
  let f : π.ThreePath u v → π.graph.neighborFinset u := fun p =>
    ⟨p.val.1, by simpa only [SimpleGraph.mem_neighborFinset] using p.property.1⟩
  have hi : Function.Injective f := by
    intro p r h
    have ha : p.val.1 = r.val.1 := congrArg Subtype.val h
    apply Subtype.ext
    apply Prod.ext ha
    exact π.three_path_right_unique hnadj p.property.1 p.property.2.1 p.property.2.2
      (ha ▸ r.property.2.1) r.property.2.2
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe,
    SimpleGraph.card_neighborFinset_eq_degree] using Nat.card_le_card_of_injective f hi

/-- Exact three-valued range from source Lemma 2.5, for actual polarity graphs. -/
theorem Polarity.three_path_count_range [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L))
    {u v : P} (huv : u ≠ v) (hnadj : ¬π.graph.Adj u v) :
    Nat.card (π.ThreePath u v) = Configuration.ProjectivePlane.order P L - 1 ∨
    Nat.card (π.ThreePath u v) = Configuration.ProjectivePlane.order P L ∨
    Nat.card (π.ThreePath u v) = Configuration.ProjectivePlane.order P L + 1 := by
  classical
  have hlo := π.three_path_count_lower huv hnadj
  have hhi := π.three_path_count_le_degree hnadj
  have hd := π.degree_eq_order_or_succ u
  omega

theorem Polarity.degree_sub_one_le_three_path_count [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L))
    {u v : P} (huv : u ≠ v) (hnadj : ¬π.graph.Adj u v) :
    letI := Classical.decRel π.graph.Adj
    π.graph.degree u - 1 ≤ Nat.card (π.ThreePath u v) := by
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
  have herase := Finset.pred_card_le_card_erase (s := π.graph.neighborFinset u) (a := w)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at herase
  exact herase.trans hcard


theorem Polarity.three_path_count_reverse [Fintype P]
    (π : Polarity (P := P) (L := L)) (u v : P) :
    Nat.card (π.ThreePath u v) = Nat.card (π.ThreePath v u) := by
  let e : π.ThreePath u v ≃ π.ThreePath v u := {
    toFun := fun p => ⟨(p.val.2,p.val.1),p.property.2.2.symm,p.property.2.1.symm,p.property.1.symm⟩
    invFun := fun p => ⟨(p.val.2,p.val.1),p.property.2.2.symm,p.property.2.1.symm,p.property.1.symm⟩
    left_inv := fun p => by apply Subtype.ext; rfl
    right_inv := fun p => by apply Subtype.ext; rfl }
  exact Nat.card_congr e

/-- The smallest count forces both endpoints to be absolute. -/
theorem Polarity.absolute_of_three_path_count_min [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L))
    {u v : P} (huv : u ≠ v) (hnadj : ¬π.graph.Adj u v)
    (hc : Nat.card (π.ThreePath u v) = Configuration.ProjectivePlane.order P L - 1) :
    π.Absolute u ∧ π.Absolute v := by
  classical
  have hq := Configuration.ProjectivePlane.one_lt_order P L
  have hleft : ∀ {a b : P}, a ≠ b → ¬π.graph.Adj a b →
      Nat.card (π.ThreePath a b) = Configuration.ProjectivePlane.order P L - 1 →
      π.Absolute a := by
    intro a b hab hnon hcount
    by_contra hn
    have hd := π.degree_of_not_absolute a hn
    have hl := π.degree_sub_one_le_three_path_count hab hnon
    omega
  refine ⟨hleft huv hnadj hc, hleft huv.symm (fun h => hnadj h.symm) ?_⟩
  rw [← π.three_path_count_reverse u v]
  exact hc

/-- An absolute second endpoint removes the unique common neighbor from possible first vertices. -/
theorem Polarity.three_path_count_le_degree_sub_one_of_absolute
    [Configuration.ProjectivePlane P L] [Fintype P] [Finite L]
    (π : Polarity (P := P) (L := L)) {u v : P}
    (huv : u ≠ v) (hnadj : ¬π.graph.Adj u v) (hv : π.Absolute v) :
    letI := Classical.decRel π.graph.Adj
    Nat.card (π.ThreePath u v) ≤ π.graph.degree u - 1 := by
  classical
  let : Fintype (π.ThreePath u v) := by unfold Polarity.ThreePath; infer_instance
  obtain ⟨w, hw, _⟩ := Configuration.HasPoints.existsUnique_point P L
    (π.line u) (π.line v) (fun h => huv (π.line.injective h))
  have huw : u ≠ w := by
    intro h
    exact hnadj ⟨huv, h.symm ▸ hw.2⟩
  have hwv : w ≠ v := by
    intro h
    exact hnadj ⟨huv, (π.reciprocal v u).mp (h ▸ hw.1)⟩
  have hwu : w ∈ π.graph.neighborFinset u := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (show π.graph.Adj u w from ⟨huw, (π.reciprocal w u).mp hw.1⟩)
  have havoid : ∀ p : π.ThreePath u v, p.val.1 ≠ w := by
    intro p heq
    have hbW : p.val.2 ∈ π.line w := by
      rw [← heq]
      exact (π.reciprocal p.val.1 p.val.2).mp p.property.2.1.2
    have hvW : v ∈ π.line w := (π.reciprocal w v).mp hw.2
    rcases Configuration.Nondegenerate.eq_or_eq hbW hvW p.property.2.2.2 hv with h | h
    · exact p.property.2.2.ne h
    · exact hwv (π.line.injective h)
  let f : π.ThreePath u v → ((π.graph.neighborFinset u).erase w) := fun p =>
    ⟨p.val.1, Finset.mem_erase.mpr ⟨havoid p,
      by simpa only [SimpleGraph.mem_neighborFinset] using p.property.1⟩⟩
  have hi : Function.Injective f := by
    intro p r h
    have ha : p.val.1 = r.val.1 := congrArg Subtype.val h
    apply Subtype.ext
    apply Prod.ext ha
    exact π.three_path_right_unique hnadj p.property.1 p.property.2.1 p.property.2.2
      (ha ▸ r.property.2.1) r.property.2.2
  have hc := Nat.card_le_card_of_injective f hi
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_erase_of_mem hwu, SimpleGraph.card_neighborFinset_eq_degree] using hc

/-- Source Lemma 2.5's exact characterization of the smallest count. -/
theorem Polarity.three_path_count_min_iff_absolute
    [Configuration.ProjectivePlane P L] [Fintype P] [Finite L]
    (π : Polarity (P := P) (L := L)) {u v : P}
    (huv : u ≠ v) (hnadj : ¬π.graph.Adj u v) :
    Nat.card (π.ThreePath u v) = Configuration.ProjectivePlane.order P L - 1 ↔
      π.Absolute u ∧ π.Absolute v := by
  classical
  constructor
  · exact π.absolute_of_three_path_count_min huv hnadj
  · rintro ⟨hu,hv⟩
    have hd := (π.degree_eq_order_iff_absolute u).mpr hu
    have hl := π.three_path_count_lower huv hnadj
    have hh := π.three_path_count_le_degree_sub_one_of_absolute huv hnadj hv
    omega

#print axioms Polarity.three_path_count_min_iff_absolute
#print axioms Polarity.absolute_of_three_path_count_min
#print axioms Polarity.three_path_count_le_degree
#print axioms Polarity.three_path_count_range
end Erdos60.Geometry
