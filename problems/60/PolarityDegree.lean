import Polarity
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Erdos60.Geometry
variable {P L : Type*} [Membership P L]

def Polarity.Absolute (π : Polarity (P := P) (L := L)) (x : P) : Prop := x ∈ π.line x

theorem Polarity.degree_add_diagonal [Fintype P]
    (π : Polarity (P := P) (L := L)) (x : P) :
    letI : Decidable (π.Absolute x) := Classical.propDecidable _
    letI := Classical.decRel π.graph.Adj
    π.graph.degree x + (if π.Absolute x then 1 else 0) =
      Configuration.pointCount P (π.line x) := by
  classical
  let s : Finset P := Finset.univ.filter (fun y => y ∈ π.line x)
  have hn : π.graph.neighborFinset x = s.erase x := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Polarity.adj_iff,
      Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, s]
    constructor
    · rintro ⟨hne, hi⟩
      exact ⟨hne.symm, (π.reciprocal x y).mp hi⟩
    · rintro ⟨hne, hi⟩
      exact ⟨hne.symm, (π.reciprocal y x).mp hi⟩
  have hs : s.card = Configuration.pointCount P (π.line x) := by
    simp [s, Configuration.pointCount, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn, ← hs]
  by_cases hx : π.Absolute x
  · have hx' : x ∈ s := by simpa [s, Polarity.Absolute] using hx
    simp only [if_pos hx]
    exact Finset.card_erase_add_one hx'
  · have hx' : x ∉ s := by simpa [s, Polarity.Absolute] using hx
    simp [hx, Finset.erase_eq_of_notMem hx']

theorem Polarity.degree_eq_order_or_succ [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L)) (x : P) :
    letI := Classical.decRel π.graph.Adj
    π.graph.degree x = Configuration.ProjectivePlane.order P L ∨
    π.graph.degree x = Configuration.ProjectivePlane.order P L + 1 := by
  classical
  have h := π.degree_add_diagonal x
  rw [Configuration.ProjectivePlane.pointCount_eq] at h
  by_cases hx : π.Absolute x
  · simp only [if_pos hx] at h
    exact Or.inl (Nat.add_right_cancel h)
  · simp only [if_neg hx, Nat.add_zero] at h
    exact Or.inr h

theorem Polarity.degree_eq_order_iff_absolute [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L)) (x : P) :
    letI := Classical.decRel π.graph.Adj
    π.graph.degree x = Configuration.ProjectivePlane.order P L ↔ π.Absolute x := by
  classical
  have h := π.degree_add_diagonal x
  rw [Configuration.ProjectivePlane.pointCount_eq] at h
  constructor
  · intro hd
    by_contra hn
    simp only [if_neg hn, Nat.add_zero, hd] at h
    exact Nat.ne_add_one _ h
  · intro ha
    simp only [if_pos ha] at h
    exact Nat.add_right_cancel h

theorem Polarity.degree_of_not_absolute [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L)) (x : P)
    (hx : ¬π.Absolute x) :
    letI := Classical.decRel π.graph.Adj
    π.graph.degree x = Configuration.ProjectivePlane.order P L + 1 := by
  classical
  have h := π.degree_add_diagonal x
  rw [Configuration.ProjectivePlane.pointCount_eq] at h
  simpa only [if_neg hx, Nat.add_zero] using h

theorem Polarity.absolute_not_adjacent [Configuration.Nondegenerate P L]
    (π : Polarity (P := P) (L := L)) {a b : P}
    (ha : π.Absolute a) (hb : π.Absolute b) : ¬π.graph.Adj a b := by
  intro hab
  have hba := (π.reciprocal a b).mp hab.2
  rcases Configuration.Nondegenerate.eq_or_eq ha hba hab.2 hb with h | h
  · exact hab.ne h
  · exact hab.ne (π.line.injective h)

/-- Internal vertices of length-three paths between a fixed nonedge are
determined by either internal vertex. This is a required part of source
Lemma 2.5, proved from incidence uniqueness rather than assumed. -/
theorem Polarity.three_path_right_unique [Configuration.Nondegenerate P L]
    (π : Polarity (P := P) (L := L)) {u v a b d : P}
    (huv : ¬π.graph.Adj u v) (hua : π.graph.Adj u a)
    (hab : π.graph.Adj a b) (hbv : π.graph.Adj b v)
    (had : π.graph.Adj a d) (hdv : π.graph.Adj d v) : b = d := by
  have hav : a ≠ v := by intro h; exact huv (h ▸ hua)
  exact π.common_neighbor_unique hav hab hbv.symm had hdv.symm

theorem Polarity.three_path_left_unique [Configuration.Nondegenerate P L]
    (π : Polarity (P := P) (L := L)) {u v a b c : P}
    (huv : ¬π.graph.Adj u v) (hua : π.graph.Adj u a)
    (hab : π.graph.Adj a b) (hbv : π.graph.Adj b v)
    (huc : π.graph.Adj u c) (hcb : π.graph.Adj c b) : a = c := by
  have hub : u ≠ b := by intro h; exact huv (h ▸ hbv)
  exact π.common_neighbor_unique hub hua hab.symm huc hcb.symm

theorem Polarity.three_path_no_reversed_middle [Configuration.Nondegenerate P L]
    (π : Polarity (P := P) (L := L)) {u v a b : P}
    (huv : u ≠ v) (hua : π.graph.Adj u a)
    (hab : π.graph.Adj a b) (hbv : π.graph.Adj b v)
    (hub : π.graph.Adj u b) (hav : π.graph.Adj a v) : False := by
  exact hab.ne (π.common_neighbor_unique huv hua hav.symm hub hbv.symm)

#print axioms Polarity.degree_add_diagonal
#print axioms Polarity.degree_eq_order_or_succ
#print axioms Polarity.degree_eq_order_iff_absolute
#print axioms Polarity.degree_of_not_absolute
#print axioms Polarity.absolute_not_adjacent
#print axioms Polarity.three_path_right_unique
#print axioms Polarity.three_path_left_unique
#print axioms Polarity.three_path_no_reversed_middle

end Erdos60.Geometry
