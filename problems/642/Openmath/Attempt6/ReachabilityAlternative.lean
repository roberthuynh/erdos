import Openmath.Attempt6.SampledReachability
import Openmath.Attempt6.BoundedDifferences

/-
Actual finite constructions for CJMM Lemma 7.7, Advances in Mathematics 469
(2025), 110228, pp. 37-38, DOI 10.1016/j.aim.2025.110228.
This file uses original graph adjacency throughout. Ambient logarithmic parameters
belong to the expander supplier and do not change the graph in the constructions.
-/

namespace Erdos585.Attempt6.ReachabilityAlternative

open Finset SimpleGraph RobustCore SampledReachability

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Centers and leaves of actual pairwise vertex-disjoint stars. -/
def StarPacking (J : SimpleGraph V) (U : Finset V) (t : ℕ)
    (C : Finset V) (leaf : V → Finset V) : Prop :=
  C ⊆ U ∧
  (∀ c ∈ C, leaf c ⊆ Uᶜ) ∧
  (∀ c ∈ C, ∀ v ∈ leaf c, J.Adj c v) ∧
  (∀ c ∈ C, (leaf c).card = t) ∧
  (∀ c ∈ C, ∀ d ∈ C, c ≠ d → Disjoint (leaf c) (leaf d))

theorem exists_maximal_star_packing (J : SimpleGraph V) [DecidableRel J.Adj]
    (U : Finset V) (t : ℕ) :
    ∃ C leaf, StarPacking J U t C leaf ∧
      ∀ v ∈ U \ C,
        ((J.neighborFinset v) \ (U ∪ C.biUnion leaf)).card < t := by
  classical
  let K : Finset (Finset V × (V → Finset V)) :=
    Finset.univ.filter (fun a => StarPacking J U t a.1 a.2)
  have hK : K.Nonempty := by
    refine ⟨(∅, fun _ => ∅), ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simp [StarPacking]⟩
  obtain ⟨a, ha, hmax⟩ := K.exists_max_image (fun a => a.1.card) hK
  have hpack : StarPacking J U t a.1 a.2 := (Finset.mem_filter.mp ha).2
  refine ⟨a.1, a.2, hpack, ?_⟩
  intro v hv
  obtain ⟨hvU, hvC⟩ := Finset.mem_sdiff.mp hv
  by_contra hnot
  have hlarge : t ≤ ((J.neighborFinset v) \ (U ∪ a.1.biUnion a.2)).card :=
    Nat.le_of_not_gt hnot
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hlarge
  let leaf : V → Finset V := Function.update a.2 v S
  have hnew : StarPacking J U t (insert v a.1) leaf := by
    rcases hpack with ⟨hCU, hout, hadj, hsize, hdisj⟩
    refine ⟨by simpa using Finset.insert_subset hvU hCU, ?_, ?_, ?_, ?_⟩
    · intro c hc x hx
      by_cases hcv : c = v
      · have hxS : x ∈ S := by simpa [leaf, hcv] using hx
        have hxu := (Finset.mem_sdiff.mp (hSsub hxS)).2
        simp only [Finset.mem_compl]
        exact fun hxU => hxu (Finset.mem_union_left _ hxU)
      · have hc : c ∈ a.1 := (Finset.mem_insert.mp hc).resolve_left hcv
        exact hout c hc (by simpa [leaf, hcv] using hx)
    · intro c hc x hx
      by_cases hcv : c = v
      · have hxadj : J.Adj v x := (J.mem_neighborFinset v x).mp
          (Finset.mem_sdiff.mp (hSsub (by simpa [leaf, hcv] using hx))).1
        simpa only [hcv] using hxadj
      · have hc : c ∈ a.1 := (Finset.mem_insert.mp hc).resolve_left hcv
        exact hadj c hc x (by simpa [leaf, hcv] using hx)
    · intro c hc
      by_cases hcv : c = v
      · simpa [leaf, hcv] using hScard
      · have hc : c ∈ a.1 := (Finset.mem_insert.mp hc).resolve_left hcv
        simpa [leaf, hcv] using hsize c hc
    · have hSdisj : ∀ c ∈ a.1, Disjoint S (a.2 c) := by
        intro c hc
        apply Finset.disjoint_left.mpr
        intro x hxS hxc
        exact (Finset.mem_sdiff.mp (hSsub hxS)).2
          (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, hc, hxc⟩))
      intro c hc d hd hcd
      by_cases hcv : c = v
      · have hdv : d ≠ v := by intro he; exact hcd (hcv.trans he.symm)
        have hdC : d ∈ a.1 := (Finset.mem_insert.mp hd).resolve_left hdv
        simpa [leaf, hcv, hdv] using hSdisj d hdC
      · have hc : c ∈ a.1 := (Finset.mem_insert.mp hc).resolve_left hcv
        by_cases hdv : d = v
        · simpa [leaf, hcv, hdv] using (hSdisj c hc).symm
        · have hd : d ∈ a.1 := (Finset.mem_insert.mp hd).resolve_left hdv
          simpa [leaf, hcv, hdv] using hdisj c hc d hd hcd
  have hmem : (insert v a.1, leaf) ∈ K :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew⟩
  have hle := hmax _ hmem
  simp only [Finset.card_insert_of_notMem hvC] at hle
  omega

/-- The packing uses exactly t leaves per center, with no repeated leaves. -/
theorem star_packing_leaf_card (J : SimpleGraph V) (U C : Finset V)
    (t : ℕ) (leaf : V → Finset V) (h : StarPacking J U t C leaf) :
    (C.biUnion leaf).card = t * C.card := by
  classical
  rw [Finset.card_biUnion]
  · calc
      ∑ c ∈ C, (leaf c).card = ∑ _c ∈ C, t := Finset.sum_congr rfl h.2.2.2.1
      _ = t * C.card := by simp [mul_comm]
  · intro c hc d hd hcd
    exact h.2.2.2.2 c hc d hd hcd

/-- Number of selected exterior columns incident to an original vertex. -/
def rowDegree (X : Finset V) (leaf : V → Finset V) (u : V) : ℕ :=
  (X.filter (fun x => u ∈ leaf x)).card

/-- A finite crossing incidence relation with exact column size and row capacities. -/
def BipartitePacking (J : SimpleGraph V) (U : Finset V) (r cap : ℕ)
    (X : Finset V) (leaf : V → Finset V) : Prop :=
  X ⊆ Uᶜ ∧
  (∀ x ∈ X, leaf x ⊆ U) ∧
  (∀ x ∈ X, ∀ u ∈ leaf x, J.Adj x u) ∧
  (∀ x ∈ X, (leaf x).card = r) ∧
  (∀ u ∈ U, rowDegree X leaf u ≤ cap)

theorem exists_maximal_bipartite_packing (J : SimpleGraph V) [DecidableRel J.Adj]
    (U : Finset V) (r cap : ℕ) :
    ∃ X leaf, BipartitePacking J U r cap X leaf ∧
      ∀ v ∈ Uᶜ \ X,
        ((J.neighborFinset v ∩ U).filter
          (fun u => rowDegree X leaf u < cap)).card < r := by
  classical
  let K : Finset (Finset V × (V → Finset V)) :=
    Finset.univ.filter (fun a => BipartitePacking J U r cap a.1 a.2)
  have hK : K.Nonempty := by
    refine ⟨(∅, fun _ => ∅), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simp [BipartitePacking, rowDegree]
  obtain ⟨a, ha, hmax⟩ := K.exists_max_image (fun a => a.1.card) hK
  have hpack : BipartitePacking J U r cap a.1 a.2 := (Finset.mem_filter.mp ha).2
  refine ⟨a.1, a.2, hpack, ?_⟩
  intro v hv
  obtain ⟨hvU, hvX⟩ := Finset.mem_sdiff.mp hv
  by_contra hnot
  have hlarge : r ≤ ((J.neighborFinset v ∩ U).filter
      (fun u => rowDegree a.1 a.2 u < cap)).card := Nat.le_of_not_gt hnot
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hlarge
  let leaf : V → Finset V := Function.update a.2 v S
  have hrow : ∀ u, rowDegree (insert v a.1) leaf u =
      if u ∈ S then rowDegree a.1 a.2 u + 1 else rowDegree a.1 a.2 u := by
    intro u
    have heq : (insert v a.1).filter (fun x => u ∈ leaf x) =
        if u ∈ S then insert v (a.1.filter (fun x => u ∈ a.2 x))
        else a.1.filter (fun x => u ∈ a.2 x) := by
      ext x
      split_ifs with huS
      all_goals
        by_cases hxv : x = v
        · subst x; simp [leaf, hvX, huS]
        · simp [leaf, hxv, huS]
    unfold rowDegree
    rw [heq]
    split_ifs
    · rw [Finset.card_insert_of_notMem (fun h => hvX (Finset.mem_filter.mp h).1)]
    · rfl
  have hnew : BipartitePacking J U r cap (insert v a.1) leaf := by
    rcases hpack with ⟨hXU, hout, hadj, hsize, hcap⟩
    refine ⟨Finset.insert_subset hvU hXU, ?_, ?_, ?_, ?_⟩
    · intro x hx u hu
      by_cases hxv : x = v
      · have huS : u ∈ S := by simpa [leaf, hxv] using hu
        exact (Finset.mem_inter.mp (Finset.mem_filter.mp (hSsub huS)).1).2
      · exact hout x ((Finset.mem_insert.mp hx).resolve_left hxv)
          (by simpa [leaf, hxv] using hu)
    · intro x hx u hu
      by_cases hxv : x = v
      · have huS : u ∈ S := by simpa [leaf, hxv] using hu
        have hadjvu := (J.mem_neighborFinset v u).mp
          (Finset.mem_inter.mp (Finset.mem_filter.mp (hSsub huS)).1).1
        simpa only [hxv] using hadjvu
      · exact hadj x ((Finset.mem_insert.mp hx).resolve_left hxv) u
          (by simpa [leaf, hxv] using hu)
    · intro x hx
      by_cases hxv : x = v
      · simpa [leaf, hxv] using hScard
      · simpa [leaf, hxv] using hsize x ((Finset.mem_insert.mp hx).resolve_left hxv)
    · intro u hu
      rw [hrow]
      split_ifs with huS
      · have := (Finset.mem_filter.mp (hSsub huS)).2
        omega
      · exact hcap u hu
  have hmem : (insert v a.1, leaf) ∈ K :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew⟩
  have hle := hmax _ hmem
  simp only [Finset.card_insert_of_notMem hvX] at hle
  omega

/-- The actual undirected crossing graph supplied by the selected columns. -/
def crossingGraph (U X : Finset V) (leaf : V → Finset V)
    (hout : X ⊆ Uᶜ) (hin : ∀ x ∈ X, leaf x ⊆ U) : SimpleGraph V where
  Adj x y := (x ∈ X ∧ y ∈ leaf x) ∨ (y ∈ X ∧ x ∈ leaf y)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun x h => by
    rcases h with h | h
    all_goals exact (Finset.mem_compl.mp (hout h.1)) (hin x h.1 h.2)⟩

theorem crossingGraph_le (J : SimpleGraph V) (U X : Finset V) (r cap : ℕ)
    (leaf : V → Finset V) (h : BipartitePacking J U r cap X leaf) :
    crossingGraph U X leaf h.1 h.2.1 ≤ J := by
  intro x y hxy
  rcases hxy with hxy | hxy
  · exact h.2.2.1 x hxy.1 y hxy.2
  · exact (h.2.2.1 y hxy.1 x hxy.2).symm

theorem crossingGraph_column_neighbors (U X : Finset V) (leaf : V → Finset V)
    (hout : X ⊆ Uᶜ) (hin : ∀ x ∈ X, leaf x ⊆ U)
    (x : V) (hx : x ∈ X) :
    (crossingGraph U X leaf hout hin).neighborSet x = (leaf x : Set V) := by
  ext u
  change ((x ∈ X ∧ u ∈ leaf x) ∨ (u ∈ X ∧ x ∈ leaf u)) ↔ u ∈ leaf x
  constructor
  · rintro (h | h)
    · exact h.2
    · exact False.elim ((Finset.mem_compl.mp (hout hx)) (hin u h.1 h.2))
  · exact fun hu => Or.inl ⟨hx, hu⟩

theorem crossingGraph_row_neighbors (U X : Finset V) (leaf : V → Finset V)
    (hout : X ⊆ Uᶜ) (hin : ∀ x ∈ X, leaf x ⊆ U)
    (u : V) (hu : u ∈ U) :
    (crossingGraph U X leaf hout hin).neighborSet u =
      (X.filter (fun x => u ∈ leaf x) : Set V) := by
  ext x
  change ((u ∈ X ∧ x ∈ leaf u) ∨ (x ∈ X ∧ u ∈ leaf x)) ↔
    x ∈ X.filter (fun x => u ∈ leaf x)
  rw [Finset.mem_filter]
  constructor
  · rintro (h | h)
    · exact False.elim ((Finset.mem_compl.mp (hout h.1)) hu)
    · exact h
  · exact Or.inr

/-- Double counting the actual crossing incidences. -/
theorem sum_rowDegree (A X : Finset V) (leaf : V → Finset V) :
    ∑ u ∈ A, rowDegree X leaf u = ∑ x ∈ X, (leaf x ∩ A).card := by
  classical
  have hright : ∀ x, leaf x ∩ A = A.filter (fun u => u ∈ leaf x) := by
    intro x
    ext u
    simp [and_comm]
  simp_rw [hright]
  simp only [rowDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- A maximal star packing bounds the entire external boundary of remaining centers. -/
theorem star_packing_boundary_le (J : SimpleGraph V) [DecidableRel J.Adj]
    (U C : Finset V) (t : ℕ) (leaf : V → Finset V)
    (hpack : StarPacking J U t C leaf)
    (hmax : ∀ v ∈ U \ C,
      ((J.neighborFinset v) \ (U ∪ C.biUnion leaf)).card < t) :
    (externalNeighbors J (U \ C)).card ≤ C.card + t * U.card := by
  classical
  let R : V → Finset V := fun v => (J.neighborFinset v) \ (U ∪ C.biUnion leaf)
  have hsub : externalNeighbors J (U \ C) ⊆
      (C ∪ C.biUnion leaf) ∪ (U \ C).biUnion R := by
    intro x hx
    have hxdata : x ∉ U \ C ∧ ∃ v ∈ U \ C, J.Adj v x := by
      simpa only [externalNeighbors, Finset.mem_filter, Finset.mem_compl] using hx
    by_cases hxC : x ∈ C
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hxC)
    by_cases hxL : x ∈ C.biUnion leaf
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hxL)
    obtain ⟨v, hv, hvx⟩ := hxdata.2
    have hxU : x ∉ U := fun h => hxdata.1 (Finset.mem_sdiff.mpr ⟨h, hxC⟩)
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨v, hv, Finset.mem_sdiff.mpr ⟨(J.mem_neighborFinset v x).mpr hvx,
      by simpa using And.intro hxU hxL⟩⟩
  have hR : ((U \ C).biUnion R).card ≤ (U \ C).card * t := by
    calc
      _ ≤ ∑ v ∈ U \ C, (R v).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ U \ C, t := Finset.sum_le_sum fun v hv => (hmax v hv).le
      _ = _ := by simp
  have hsplit := Finset.card_sdiff_add_card_eq_card hpack.1
  calc
    _ ≤ ((C ∪ C.biUnion leaf) ∪ (U \ C).biUnion R).card := Finset.card_le_card hsub
    _ ≤ (C.card + (C.biUnion leaf).card) + ((U \ C).biUnion R).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ (C.card + t * C.card) + (U \ C).card * t := by
      rw [star_packing_leaf_card J U C t leaf hpack]
      exact Nat.add_le_add_left hR _
    _ = C.card + t * U.card := by nlinarith [hsplit]

/-- Saturation can only occur at rows receiving at least t packed-leaf incidences. -/
theorem saturated_row_leaf_degree (J : SimpleGraph V) [DecidableRel J.Adj]
    (U C X : Finset V) (t r : ℕ) (star leaf : V → Finset V)
    (hp : BipartitePacking J U r (2 * t) X leaf)
    (hmax : ∀ v ∈ U \ C,
      ((J.neighborFinset v) \ (U ∪ C.biUnion star)).card < t)
    (u : V) (hu : u ∈ U \ C) (hsat : rowDegree X leaf u = 2 * t) :
    t ≤ rowDegree (X ∩ C.biUnion star) leaf u := by
  classical
  let D := X.filter (fun x => u ∈ leaf x)
  let L := C.biUnion star
  have hsub : D \ L ⊆ (J.neighborFinset u) \ (U ∪ L) := by
    intro x hx
    obtain ⟨hxD, hxL⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hxX, hxu⟩ := Finset.mem_filter.mp hxD
    apply Finset.mem_sdiff.mpr
    refine ⟨(J.mem_neighborFinset u x).mpr (hp.2.2.1 x hxX u hxu).symm, ?_⟩
    simp only [Finset.mem_union, not_or]
    exact ⟨Finset.mem_compl.mp (hp.1 hxX), hxL⟩
  have hsmall : (D \ L).card ≤ t := (Finset.card_le_card hsub).trans (hmax u hu).le
  have hsplit := Finset.card_inter_add_card_sdiff D L
  have heq : D ∩ L = (X ∩ L).filter (fun x => u ∈ leaf x) := by
    ext x
    simp [D, and_assoc, and_left_comm, and_comm]
  change t ≤ ((X ∩ L).filter (fun x => u ∈ leaf x)).card
  rw [← heq]
  have hD : D.card = 2 * t := hsat
  omega

/-- Actual incidence double counting bounds the number of saturated remaining rows. -/
theorem saturated_row_card_le (J : SimpleGraph V) [DecidableRel J.Adj]
    (U C X : Finset V) (t r : ℕ) (ht : 0 < t) (star leaf : V → Finset V)
    (hstar : StarPacking J U t C star)
    (hp : BipartitePacking J U r (2 * t) X leaf)
    (hmax : ∀ v ∈ U \ C,
      ((J.neighborFinset v) \ (U ∪ C.biUnion star)).card < t) :
    ((U \ C).filter (fun u => rowDegree X leaf u = 2 * t)).card ≤ r * C.card := by
  classical
  let A := (U \ C).filter (fun u => rowDegree X leaf u = 2 * t)
  have hbound : t * A.card ≤ r * (C.biUnion star).card := by
    calc
      _ = ∑ _u ∈ A, t := by simp [mul_comm]
      _ ≤ ∑ u ∈ A, rowDegree (X ∩ C.biUnion star) leaf u := by
        apply Finset.sum_le_sum
        intro u hu
        obtain ⟨hu, hsat⟩ := Finset.mem_filter.mp hu
        exact saturated_row_leaf_degree J U C X t r star leaf hp hmax u hu hsat
      _ = ∑ x ∈ X ∩ C.biUnion star, (leaf x ∩ A).card := sum_rowDegree _ _ _
      _ ≤ ∑ _x ∈ X ∩ C.biUnion star, r := by
        apply Finset.sum_le_sum
        intro x hx
        exact (Finset.card_le_card Finset.inter_subset_left).trans_eq
          (hp.2.2.2.1 x (Finset.mem_inter.mp hx).1)
      _ = r * (X ∩ C.biUnion star).card := by simp [mul_comm]
      _ ≤ r * (C.biUnion star).card := Nat.mul_le_mul_left _
        (Finset.card_le_card Finset.inter_subset_right)
  rw [star_packing_leaf_card J U C t star hstar] at hbound
  change A.card ≤ r * C.card
  nlinarith

/-- Every exterior robust neighbor of unsaturated rows is selected by maximality. -/
theorem exterior_robust_neighbors_selected (J : SimpleGraph V) [DecidableRel J.Adj]
    (U X : Finset V) (r cap : ℕ) (leaf : V → Finset V)
    (A : Finset V) (hAU : A ⊆ U)
    (hA : ∀ u ∈ A, rowDegree X leaf u < cap)
    (hmax : ∀ v ∈ Uᶜ \ X,
      ((J.neighborFinset v ∩ U).filter
        (fun u => rowDegree X leaf u < cap)).card < r) :
    robustNeighborhood J A (r : ℝ) \ U ⊆ X := by
  classical
  intro v hv
  obtain ⟨hvrob, hvU⟩ := Finset.mem_sdiff.mp hv
  by_contra hvX
  have hlt := hmax v (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hvU, hvX⟩)
  have hsub : J.neighborFinset v ∩ A ⊆
      (J.neighborFinset v ∩ U).filter (fun u => rowDegree X leaf u < cap) := by
    intro u hu
    obtain ⟨hun, huA⟩ := Finset.mem_inter.mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hun, hAU huA⟩, hA u huA⟩
  have hdegree : (r : ℝ) ≤ ((J.neighborFinset v ∩ A).card : ℝ) :=
    (Finset.mem_filter.mp hvrob).2
  have hr : r ≤ (J.neighborFinset v ∩ A).card := by exact_mod_cast hdegree
  exact (not_lt_of_ge (hr.trans (Finset.card_le_card hsub))) hlt

/-- Removing B from a seed adds at most B to its external neighborhood. -/
theorem externalNeighbors_sdiff_subset (J : SimpleGraph V) (W B : Finset V) :
    externalNeighbors J (W \ B) ⊆ externalNeighbors J W ∪ B := by
  classical
  intro x hx
  have hxdata : x ∉ W \ B ∧ ∃ u ∈ W \ B, J.Adj u x := by
    simpa only [externalNeighbors, Finset.mem_filter, Finset.mem_compl] using hx
  by_cases hxB : x ∈ B
  · exact Finset.mem_union_right _ hxB
  · apply Finset.mem_union_left
    simp only [externalNeighbors, Finset.mem_filter, Finset.mem_compl]
    refine ⟨fun hxW => hxdata.1 (Finset.mem_sdiff.mpr ⟨hxW, hxB⟩), ?_⟩
    obtain ⟨u, hu, hux⟩ := hxdata.2
    exact ⟨u, (Finset.mem_sdiff.mp hu).1, hux⟩

                                                                            
theorem robust_neighborhood_card_le_selected_add (J : SimpleGraph V)
    [DecidableRel J.Adj] (U B X : Finset V) (r cap : ℕ) (leaf : V → Finset V)
    (hA : ∀ u ∈ U \ B, rowDegree X leaf u < cap)
    (hmax : ∀ v ∈ Uᶜ \ X,
      ((J.neighborFinset v ∩ U).filter
        (fun u => rowDegree X leaf u < cap)).card < r) :
    (robustNeighborhood J (U \ B) (r : ℝ)).card ≤ X.card + B.card := by
  classical
  have hselected := exterior_robust_neighbors_selected J U X r cap leaf
    (U \ B) Finset.sdiff_subset hA hmax
  have hsub : robustNeighborhood J (U \ B) (r : ℝ) ⊆ X ∪ B := by
    intro v hv
    by_cases hvU : v ∈ U
    · have hvA : v ∉ U \ B := by
        have := (Finset.mem_filter.mp hv).1
        have hx : v ∉ U \ B ∧ ∃ u ∈ U \ B, J.Adj u v := by
          simpa only [externalNeighbors, Finset.mem_filter, Finset.mem_compl] using this
        exact hx.1
      exact Finset.mem_union_right _ (by
        by_contra hvB
        exact hvA (Finset.mem_sdiff.mpr ⟨hvU, hvB⟩))
    · exact Finset.mem_union_left _ (hselected (Finset.mem_sdiff.mpr ⟨hv, hvU⟩))
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- These neighbor-set cardinalities are the actual graph degrees. -/
theorem crossingGraph_degrees (J : SimpleGraph V) (U X : Finset V) (r cap : ℕ)
    (leaf : V → Finset V) (h : BipartitePacking J U r cap X leaf) :
    (∀ x ∈ X, ((crossingGraph U X leaf h.1 h.2.1).neighborSet x).ncard = r) ∧
    (∀ u ∈ U, ((crossingGraph U X leaf h.1 h.2.1).neighborSet u).ncard ≤ cap) := by
  classical
  constructor
  · intro x hx
    rw [crossingGraph_column_neighbors U X leaf h.1 h.2.1 x hx]
    simpa using h.2.2.2.1 x hx
  · intro u hu
    rw [crossingGraph_row_neighbors U X leaf h.1 h.2.1 u hu]
    simpa only [Set.ncard_coe_finset, rowDegree] using h.2.2.2.2 u hu

                                                                                     
                                                                               
                                                                                
                                                                                  
  
theorem repaired_structural_alternative
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s : ℝ) (hL : 1 ≤ L) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (hU : 1 ≤ U.card)
    (hsmall : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3)
    (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset)
    (hF : (F.card : ℝ) ≤ s * U.card / 4)
    (r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t)
    (hs : 20 * (r : ℝ) * t ≤ s) :
    (∃ C star, StarPacking (G.deleteEdges F) U t C star ∧
      epsilon * U.card / (20 * (r : ℝ) * L ^ 2) ≤ C.card) ∨
    (∃ X leaf, BipartitePacking (G.deleteEdges F) U r (2 * t) X leaf ∧
      epsilon * U.card / (2 * L ^ 2) ≤ X.card) := by
  classical
  let J := G.deleteEdges F
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hUr : (0 : ℝ) < U.card := by exact_mod_cast (by omega : 0 < U.card)
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hLpos : 0 < L ^ 2 := by positivity
  have hrpos : (0 : ℝ) < r := by positivity
  have hspos : 0 ≤ s := (by positivity : 0 ≤ 20 * (r : ℝ) * t).trans hs
  obtain ⟨C, star, hstar, hmax⟩ := exists_maximal_star_packing J U t
  by_cases hC : epsilon * U.card / (20 * (r : ℝ) * L ^ 2) ≤ C.card
  · exact Or.inl ⟨C, star, hstar, hC⟩
  right
  obtain ⟨X, leaf, hp, hXmax⟩ := exists_maximal_bipartite_packing J U r (2 * t)
  let S := (U \ C).filter (fun u => rowDegree X leaf u = 2 * t)
  let B := C ∪ S
  let A := U \ B
  have hSat : S.card ≤ r * C.card :=
    saturated_row_card_le J U C X t r (by omega) star leaf hstar hp hmax
  have hBU : B ⊆ U := Finset.union_subset hstar.1
    (Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset)
  have hBnat : B.card ≤ (r + 1) * C.card := by
    calc
      B.card ≤ C.card + S.card := Finset.card_union_le _ _
      _ ≤ C.card + r * C.card := Nat.add_le_add_left hSat _
      _ = _ := by ring
  have hBaux : (B.card : ℝ) ≤ 2 * (r : ℝ) * C.card := by
    have hcast : (B.card : ℝ) ≤ ((r : ℝ) + 1) * C.card := by exact_mod_cast hBnat
    nlinarith [mul_nonneg (sub_nonneg.mpr hrR) (Nat.cast_nonneg C.card)]
  have hCmul : 20 * (r : ℝ) * L ^ 2 * C.card < epsilon * U.card := by
    simpa only [mul_comm] using
      (lt_div_iff₀ (by positivity : 0 < 20 * (r : ℝ) * L ^ 2)).mp (lt_of_not_ge hC)
  have hBmul : 10 * L ^ 2 * B.card < epsilon * U.card := by
    have hm := mul_le_mul_of_nonneg_left hBaux (by positivity : 0 ≤ 10 * L ^ 2)
    nlinarith
  have hBhalf : 2 * (B.card : ℝ) ≤ U.card := by
    have hEU : epsilon * U.card ≤ (U.card : ℝ) :=
      mul_le_of_le_one_left (Nat.cast_nonneg _) heps1
    nlinarith [mul_nonneg (sub_nonneg.mpr hL2) (Nat.cast_nonneg B.card)]
  have hsplit : (A.card : ℝ) + B.card = U.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hBU
  have hApos : 1 ≤ A.card := by
    have hpos : (0 : ℝ) < A.card := by nlinarith
    have : 0 < A.card := by exact_mod_cast hpos
    omega
  have hAU : A ⊆ U := Finset.sdiff_subset
  have hAcardU : (A.card : ℝ) ≤ U.card := by exact_mod_cast Finset.card_le_card hAU
  have hAsmall : (A.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3 := hAcardU.trans hsmall
  have hFA : (F.card : ℝ) ≤ s * A.card / 2 := by
    have hm := mul_le_mul_of_nonneg_left hBhalf hspos
    nlinarith
  have hAunsat : ∀ u ∈ A, rowDegree X leaf u < 2 * t := by
    intro u hu
    obtain ⟨huU, huB⟩ := Finset.mem_sdiff.mp hu
    have huC : u ∉ C := fun h => huB (Finset.mem_union_left _ h)
    have hne : rowDegree X leaf u ≠ 2 * t := by
      intro he
      exact huB (Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨huU, huC⟩, he⟩))
    exact lt_of_le_of_ne (hp.2.2.2.2 u huU) hne
  have hNbound : (externalNeighbors J A).card ≤ C.card + t * U.card + B.card := by
    have heq : A = (U \ C) \ B := by
      ext u
      simp only [A, B, Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [heq]
    exact (Finset.card_le_card (externalNeighbors_sdiff_subset J (U \ C) B)).trans
      ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (star_packing_boundary_le J U C t star hstar hmax) _))
  have hN3 : (externalNeighbors J A).card ≤ 3 * t * U.card := by
    have hCcard := Finset.card_le_card hstar.1
    have hBcard := Finset.card_le_card hBU
    nlinarith
  obtain hhuge | hrob := robust_neighborhood_alternative G L epsilon s hG A hApos
    hAsmall F hFG hFA (r : ℝ) hrpos
  · have hhuge2 : s * A.card ≤ 2 * (r : ℝ) * (externalNeighbors J A).card := by
      simpa only [mul_comm] using
        (div_le_iff₀ (by positivity : 0 < 2 * (r : ℝ))).mp hhuge
    have hN3R : ((externalNeighbors J A).card : ℝ) ≤ 3 * (t : ℝ) * U.card := by
      exact_mod_cast hN3
    have hleft := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg A.card)
    have hright := mul_le_mul_of_nonneg_left hN3R (by positivity : 0 ≤ 2 * (r : ℝ))
    have hpositive : 0 < (r : ℝ) * t * U.card := by positivity
    nlinarith
  · refine ⟨X, leaf, hp, ?_⟩
    have hrobcard := robust_neighborhood_card_le_selected_add J U B X r (2 * t)
      leaf hAunsat hXmax
    have hrobR : ((robustNeighborhood J A (r : ℝ)).card : ℝ) ≤ X.card + B.card := by
      exact_mod_cast hrobcard
    have hnum : epsilon * A.card ≤ ((X.card : ℝ) + B.card) * L ^ 2 :=
      (div_le_iff₀ hLpos).mp (hrob.trans hrobR)
    apply (div_le_iff₀ (by positivity : 0 < 2 * L ^ 2)).mpr
    have hEB : epsilon * B.card ≤ L ^ 2 * B.card :=
      mul_le_mul_of_nonneg_right (heps1.trans hL2) (Nat.cast_nonneg _)
    nlinarith

                                                                                       
theorem crossingGraph_isBipartiteWith (U X : Finset V) (leaf : V → Finset V)
    (hout : X ⊆ Uᶜ) (hin : ∀ x ∈ X, leaf x ⊆ U) :
    (crossingGraph U X leaf hout hin).IsBipartiteWith (U : Set V) (X : Set V) := by
  classical
  refine ⟨Set.disjoint_left.mpr ?_, ?_⟩
  · intro v hvU hvX
    exact (Finset.mem_compl.mp (hout hvX)) hvU
  · intro u v huv
    rcases huv with huv | huv
    · exact Or.inr ⟨huv.1, hin u huv.1 huv.2⟩
    · exact Or.inl ⟨hin v huv.1 huv.2, huv.1⟩

/-- Graph-facing form: actual vertex-disjoint stars or an actual bipartite subgraph. -/
theorem repaired_structural_graph_alternative
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s : ℝ) (hL : 1 ≤ L) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (hU : 1 ≤ U.card)
    (hsmall : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3)
    (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset)
    (hF : (F.card : ℝ) ≤ s * U.card / 4)
    (r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t)
    (hs : 20 * (r : ℝ) * t ≤ s) :
    (∃ C star, StarPacking (G.deleteEdges F) U t C star ∧
      epsilon * U.card / (20 * (r : ℝ) * L ^ 2) ≤ C.card) ∨
    (∃ X : Finset V, ∃ H : SimpleGraph V,
      X ⊆ Uᶜ ∧ H ≤ G.deleteEdges F ∧
      H.IsBipartiteWith (U : Set V) (X : Set V) ∧
      epsilon * U.card / (2 * L ^ 2) ≤ X.card ∧
      (∀ x ∈ X, (H.neighborSet x).ncard = r) ∧
      (∀ u ∈ U, (H.neighborSet u).ncard ≤ 2 * t)) := by
  obtain hstar | ⟨X, leaf, hp, hcard⟩ := repaired_structural_alternative G L epsilon s
    hL heps heps1 hG U hU hsmall F hFG hF r t hr ht hs
  · exact Or.inl hstar
  · right
    refine ⟨X, crossingGraph U X leaf hp.1 hp.2.1, hp.1,
      crossingGraph_le (G.deleteEdges F) U X r (2 * t) leaf hp,
      crossingGraph_isBipartiteWith U X leaf hp.1 hp.2.1, hcard, ?_⟩
    exact crossingGraph_degrees (G.deleteEdges F) U X r (2 * t) leaf hp

open MeasureTheory Real OAI.ErdosGallai.Sampling

/-- The repaired star threshold still gives the growth needed by CJMM 7.12.
The scalar ratio hypothesis is met by its layer and star parameters once L is large.
-/
theorem repaired_star_boundary_lower_tail
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (U C : Finset V) (star : V → Finset V) (r t : ℕ)
    (hr : 0 < r) (ht : 0 < t) (L epsilon : ℝ) (hL : 0 < L)
    (heps : 0 ≤ epsilon) (hstar : StarPacking J U t C star)
    (hC : epsilon * U.card / (20 * (r : ℝ) * L ^ 2) ≤ C.card)
    (q : unitInterval) (hratio : 5 * (r : ℝ) ≤ 4 * (q : ℝ) * t) :
    (sampleMeasure V q).real
      {ω | ((sampledHitBoundary J U (sampleVertices ω)).card : ℝ) <
        epsilon * U.card / (32 * L ^ 2)} ≤
      exp (-(q : ℝ) * epsilon * U.card / (160 * (r : ℝ) * L ^ 2)) := by
  classical
  have hout : ∀ c ∈ C, star c ⊆ externalNeighbors J U := by
    intro c hc v hv
    simp only [externalNeighbors, Finset.mem_filter, Finset.mem_compl]
    exact ⟨Finset.mem_compl.mp (hstar.2.1 c hc hv),
      ⟨c, hstar.1 hc, hstar.2.2.1 c hc v hv⟩⟩
  have htail := sampled_star_boundary_lower_tail J U C star t ht hstar.1 hout
    hstar.2.2.1 hstar.2.2.2.2 hstar.2.2.2.1 q
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hCmul : epsilon * U.card ≤ (C.card : ℝ) * (20 * (r : ℝ) * L ^ 2) :=
    (div_le_iff₀ (by positivity)).mp hC
  have hgrowth : epsilon * U.card / (32 * L ^ 2) ≤
      (t : ℝ) * (q : ℝ) * C.card / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 32 * L ^ 2)).mpr
    have hmul := mul_le_mul_of_nonneg_right hratio
      (by positivity : 0 ≤ 4 * L ^ 2 * (C.card : ℝ))
    nlinarith
  have hevent : (sampleMeasure V q).real
      {ω | ((sampledHitBoundary J U (sampleVertices ω)).card : ℝ) <
        epsilon * U.card / (32 * L ^ 2)} ≤
      (sampleMeasure V q).real
      {ω | ((sampledHitBoundary J U (sampleVertices ω)).card : ℝ) <
        (t : ℝ) * (q : ℝ) * C.card / 2} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    exact fun _ h => h.trans_le hgrowth
  apply (hevent.trans htail).trans
  apply Real.exp_le_exp.mpr
  have hq := mul_le_mul_of_nonneg_left hC q.property.1
  calc
    -(q : ℝ) * C.card / 8 ≤
        -((q : ℝ) * (epsilon * U.card / (20 * (r : ℝ) * L ^ 2))) / 8 := by linarith
    _ = _ := by ring

/-- Actual selected columns hit by the sampled reservoir. -/
noncomputable def hitColumns (X : Finset V) (leaf : V → Finset V) (Q : Finset V) : Finset V :=
  X.filter (fun x => (leaf x ∩ Q).Nonempty)

theorem hitColumns_mono (X : Finset V) (leaf : V → Finset V)
    {Q R : Finset V} (hQR : Q ⊆ R) : hitColumns X leaf Q ⊆ hitColumns X leaf R := by
  classical
  intro x hx
  obtain ⟨hxX, u, hu⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxX, u, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hu).1, hQR (Finset.mem_inter.mp hu).2⟩⟩

/-- One exposed vertex changes the number of hit columns by at most its row degree. -/
theorem hitColumns_insert_card_le (X : Finset V) (leaf : V → Finset V)
    (Q : Finset V) (u : V) :
    (hitColumns X leaf (insert u Q)).card ≤ (hitColumns X leaf Q).card + rowDegree X leaf u := by
  classical
  have hsub : hitColumns X leaf (insert u Q) \ hitColumns X leaf Q ⊆
      X.filter (fun x => u ∈ leaf x) := by
    intro x hx
    obtain ⟨hxnew, hxold⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hxX, v, hv⟩ := Finset.mem_filter.mp hxnew
    obtain ⟨hvleaf, hvQ⟩ := Finset.mem_inter.mp hv
    rcases Finset.mem_insert.mp hvQ with hveq | hvQ
    · exact Finset.mem_filter.mpr ⟨hxX, by simpa only [hveq] using hvleaf⟩
    · exact False.elim (hxold (Finset.mem_filter.mpr
        ⟨hxX, v, Finset.mem_inter.mpr ⟨hvleaf, hvQ⟩⟩))
  have hcount := Finset.card_le_card hsub
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (hitColumns_mono X leaf (Finset.subset_insert u Q))
  unfold rowDegree
  omega

theorem sample_hit_probability (q : unitInterval) (S : Finset V) :
    (sampleMeasure V q).real {ω | (S ∩ sampleVertices ω).Nonempty} =
      1 - (1 - (q : ℝ)) ^ S.card := by
  classical
  have heq : {ω | (S ∩ sampleVertices ω).Nonempty} =
      {ω | Disjoint S (sampleVertices ω)}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Finset.disjoint_iff_inter_eq_empty,
      Finset.nonempty_iff_ne_empty]
  rw [heq, measureReal_compl (MeasurableSet.of_discrete), probReal_univ,
    sample_miss_probability]

/-- Expected hit count for the actual columns, without an independence assumption between columns. -/
theorem hitColumns_integral (q : unitInterval) (X : Finset V) (leaf : V → Finset V)
    (r : ℕ) (hsize : ∀ x ∈ X, (leaf x).card = r) :
    (∫ ω, ((hitColumns X leaf (sampleVertices ω)).card : ℝ) ∂sampleMeasure V q) =
      (X.card : ℝ) * (1 - (1 - (q : ℝ)) ^ r) := by
  classical
  let Z : V → (V → Bool) → ℝ := fun x =>
    {ω | (leaf x ∩ sampleVertices ω).Nonempty}.indicator (fun _ => 1)
  have heq : (fun ω => ((hitColumns X leaf (sampleVertices ω)).card : ℝ)) =
      fun ω => ∑ x ∈ X, Z x ω := by
    funext ω
    simp only [hitColumns, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, Z, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq, integral_finsetSum]
  · have hz : ∀ x ∈ X, (∫ ω, Z x ω ∂sampleMeasure V q) =
        1 - (1 - (q : ℝ)) ^ r := by
      intro x hx
      dsimp only [Z]
      rw [integral_indicator_const _ MeasurableSet.of_discrete,
        sample_hit_probability, hsize x hx]
      simp
    simp_rw [Finset.sum_congr rfl hz]
    simp
    ring
  · intro x hx
    exact Integrable.of_mem_Icc 0 1 (measurable_of_finite _).aemeasurable
      (ae_of_all _ (by intro ω; by_cases h : (leaf x ∩ sampleVertices ω).Nonempty <;>
        simp [Z, h]))

/-- Elementary lower bound for the chance of hitting one column. -/
theorem one_sub_miss_pow_ge (q : unitInterval) (r : ℕ)
    (hqr : (1 / 6 : ℝ) ≤ (q : ℝ) * r) :
    (1 / 8 : ℝ) ≤ 1 - (1 - (q : ℝ)) ^ r := by
  have hbase : 1 - (q : ℝ) ≤ exp (-(q : ℝ)) := by
    linarith [Real.add_one_le_exp (-(q : ℝ))]
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr q.property.2) hbase r
  have heq : exp (-(q : ℝ)) ^ r = exp (-((q : ℝ) * r)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq] at hpow
  have hexp : (8 / 7 : ℝ) ≤ exp ((q : ℝ) * r) := by
    linarith [Real.add_one_le_exp ((q : ℝ) * r)]
  have hinv : exp (-((q : ℝ) * r)) ≤ (7 / 8 : ℝ) := by
    rw [Real.exp_neg]
    apply (inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 7 / 8)).mpr
    norm_num
    exact hexp
  linarith

/-- The bipartite hit count has the source expectation lower bound. -/
theorem hitColumns_integral_ge (q : unitInterval) (X : Finset V)
    (leaf : V → Finset V) (r : ℕ) (hsize : ∀ x ∈ X, (leaf x).card = r)
    (hqr : (1 / 6 : ℝ) ≤ (q : ℝ) * r) :
    (X.card : ℝ) / 8 ≤
      ∫ ω, ((hitColumns X leaf (sampleVertices ω)).card : ℝ) ∂sampleMeasure V q := by
  rw [hitColumns_integral q X leaf r hsize]
  have := mul_le_mul_of_nonneg_left (one_sub_miss_pow_ge q r hqr) (Nat.cast_nonneg X.card)
  linarith

/-- Actual hit columns are among the outside vertices reached in one sampled step. -/
theorem hitColumns_subset_sampledHitBoundary
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (U X : Finset V) (r cap : ℕ) (leaf : V → Finset V)
    (hp : BipartitePacking J U r cap X leaf) (Q : Finset V) :
    hitColumns X leaf Q ⊆ sampledHitBoundary J U Q := by
  classical
  intro x hx
  obtain ⟨hxX, u, hu⟩ := Finset.mem_filter.mp hx
  obtain ⟨huleaf, huQ⟩ := Finset.mem_inter.mp hu
  have huU := hp.2.1 x hxX huleaf
  have hxU := Finset.mem_compl.mp (hp.1 hxX)
  have hxu := hp.2.2.1 x hxX u huleaf
  apply Finset.mem_filter.mpr
  refine ⟨?_, u, Finset.mem_inter.mpr ⟨?_, huQ⟩⟩
  · simp only [externalNeighbors, Finset.mem_filter, Finset.mem_compl]
    exact ⟨hxU, u, huU, hxu.symm⟩
  · exact Finset.mem_inter.mpr ⟨(J.mem_neighborFinset x u).mpr hxu, huU⟩

/-- The exact real-valued parameters of CJMM 7.12 meet the repaired growth ratio. -/
theorem source_star_growth_ratio (p L : ℝ) (hp : 0 < p) (hL : 8 ≤ L) :
    5 * (p⁻¹ * L ^ 4) ≤
      4 * (p / (6 * L ^ 4)) * ((p⁻¹) ^ 2 * L ^ 9) := by
  have hLpos : 0 < L := by linarith
  have heq : 4 * (p / (6 * L ^ 4)) * ((p⁻¹) ^ 2 * L ^ 9) =
      (2 * L / 3) * (p⁻¹ * L ^ 4) := by
    field_simp
    <;> ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right (by linarith : (5 : ℝ) ≤ 2 * L / 3) (by positivity)

/-- The repaired star failure exponent with the source layer parameters. -/
theorem source_star_exponent_identity (p L epsilon w : ℝ) (hp : p ≠ 0) (hL : L ≠ 0) :
    (p / (6 * L ^ 4)) * epsilon * w / (160 * (p⁻¹ * L ^ 4) * L ^ 2) =
      epsilon * p ^ 2 * w / (960 * L ^ 10) := by
  field_simp
  <;> ring

/-- A coordinate change affects only columns incident to that original vertex. -/
theorem hitColumns_coordinate_change (X : Finset V) (leaf : V → Finset V)
    (u : V) (omega eta : V → Bool)
    (hchange : ∀ v, v ≠ u → omega v = eta v) :
    |((hitColumns X leaf (sampleVertices omega)).card : ℝ) -
      ((hitColumns X leaf (sampleVertices eta)).card : ℝ)| ≤ rowDegree X leaf u := by
  classical
  have hsub : sampleVertices eta ⊆ insert u (sampleVertices omega) := by
    intro v hv
    by_cases hvu : v = u
    · exact Finset.mem_insert.mpr (Or.inl hvu)
    · apply Finset.mem_insert.mpr
      right
      simpa only [sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and,
        hchange v hvu] using hv
  have hsub2 : sampleVertices omega ⊆ insert u (sampleVertices eta) := by
    intro v hv
    by_cases hvu : v = u
    · exact Finset.mem_insert.mpr (Or.inl hvu)
    · apply Finset.mem_insert.mpr
      right
      simpa only [sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and,
        hchange v hvu] using hv
  have h1 := (Finset.card_le_card (hitColumns_mono X leaf hsub)).trans
    (hitColumns_insert_card_le X leaf (sampleVertices omega) u)
  have h2 := (Finset.card_le_card (hitColumns_mono X leaf hsub2)).trans
    (hitColumns_insert_card_le X leaf (sampleVertices eta) u)
  have h1R : ((hitColumns X leaf (sampleVertices eta)).card : ℝ) ≤
      (hitColumns X leaf (sampleVertices omega)).card + (rowDegree X leaf u : ℝ) := by
    exact_mod_cast h1
  have h2R : ((hitColumns X leaf (sampleVertices omega)).card : ℝ) ≤
      (hitColumns X leaf (sampleVertices eta)).card + (rowDegree X leaf u : ℝ) := by
    exact_mod_cast h2
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- Outside the original shore the coverage function is constant in that coordinate. -/
theorem rowDegree_eq_zero_of_not_mem (J : SimpleGraph V) (U X : Finset V)
    (r cap : ℕ) (leaf : V → Finset V) (hp : BipartitePacking J U r cap X leaf)
    (u : V) (hu : u ∉ U) : rowDegree X leaf u = 0 := by
  classical
  unfold rowDegree
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxX, hux⟩ := Finset.mem_filter.mp hx
  exact hu (hp.2.1 x hxX hux)

/-- Ready-to-use bounded-differences constants, zero outside the sampled shore. -/
theorem bipartite_hit_coordinate_change
    (J : SimpleGraph V) (U X : Finset V) (r cap : ℕ) (leaf : V → Finset V)
    (hp : BipartitePacking J U r cap X leaf)
    (u : V) (omega eta : V → Bool)
    (hchange : ∀ v, v ≠ u → omega v = eta v) :
    |((hitColumns X leaf (sampleVertices omega)).card : ℝ) -
      ((hitColumns X leaf (sampleVertices eta)).card : ℝ)| ≤
        if u ∈ U then (cap : ℝ) else 0 := by
  have h := hitColumns_coordinate_change X leaf u omega eta hchange
  split_ifs with hu
  · exact h.trans (by exact_mod_cast hp.2.2.2.2 u hu)
  · simpa only [rowDegree_eq_zero_of_not_mem J U X r cap leaf hp u hu,
      Nat.cast_zero] using h

/-- Sum of the actual bounded-differences constants for the bipartite branch. -/
theorem bipartite_hit_sum_sq_constants (U : Finset V) (cap : ℕ) :
    (∑ u : V, (if u ∈ U then (cap : ℝ) else 0) ^ 2) = (cap : ℝ) ^ 2 * U.card := by
  classical
  simp [Finset.sum_ite, mul_comm]

/-- Concentration of the actual dependent column-coverage indicators. -/
theorem bipartite_hit_lower_tail (q : unitInterval)
    (J : SimpleGraph V) (U X : Finset V) (r cap : ℕ) (leaf : V → Finset V)
    (hp : BipartitePacking J U r cap X leaf)
    (hqr : (1 / 6 : ℝ) ≤ (q : ℝ) * r) :
    (sampleMeasure V q).real
      {omega | ((hitColumns X leaf (sampleVertices omega)).card : ℝ) ≤ X.card / 16} ≤
      exp (-(X.card : ℝ) ^ 2 / (512 * (cap : ℝ) ^ 2 * U.card)) := by
  apply BoundedDifferences.lower_tail_row_cap q
    (fun omega => ((hitColumns X leaf (sampleVertices omega)).card : ℝ))
    U (cap : ℝ) (X.card : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro u omega eta hchange
    exact bipartite_hit_coordinate_change J U X r cap leaf hp u omega eta hchange
  · exact hitColumns_integral_ge q X leaf r hp.2.2.2.1 hqr

/-- The actual bipartite alternative supplies one-step original-edge boundary growth. -/
theorem bipartite_boundary_lower_tail (q : unitInterval)
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (U X : Finset V) (hU : 1 ≤ U.card) (r cap : ℕ) (hcap : 0 < cap)
    (leaf : V → Finset V) (hp : BipartitePacking J U r cap X leaf)
    (L epsilon : ℝ) (hL : 0 < L) (heps : 0 ≤ epsilon)
    (hX : epsilon * U.card / (2 * L ^ 2) ≤ X.card)
    (hqr : (1 / 6 : ℝ) ≤ (q : ℝ) * r) :
    (sampleMeasure V q).real
      {omega | ((sampledHitBoundary J U (sampleVertices omega)).card : ℝ) <
        epsilon * U.card / (32 * L ^ 2)} ≤
      exp (-epsilon ^ 2 * U.card / (2048 * (cap : ℝ) ^ 2 * L ^ 4)) := by
  have hUr : (0 : ℝ) < U.card := by exact_mod_cast (by omega : 0 < U.card)
  have hcapR : (0 : ℝ) < cap := by exact_mod_cast hcap
  have hX16 : epsilon * U.card / (32 * L ^ 2) ≤ (X.card : ℝ) / 16 := by
    have hn := (div_le_iff₀ (by positivity : 0 < 2 * L ^ 2)).mp hX
    apply (div_le_iff₀ (by positivity : 0 < 32 * L ^ 2)).mpr
    nlinarith
  have hevent : (sampleMeasure V q).real
      {omega | ((sampledHitBoundary J U (sampleVertices omega)).card : ℝ) <
        epsilon * U.card / (32 * L ^ 2)} ≤
      (sampleMeasure V q).real
      {omega | ((hitColumns X leaf (sampleVertices omega)).card : ℝ) ≤ X.card / 16} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro omega homega
    have hcount : ((hitColumns X leaf (sampleVertices omega)).card : ℝ) ≤
        (sampledHitBoundary J U (sampleVertices omega)).card := by
      exact_mod_cast Finset.card_le_card
        (hitColumns_subset_sampledHitBoundary J U X r cap leaf hp (sampleVertices omega))
    exact (hcount.trans_lt homega).le.trans hX16
  apply (hevent.trans (bipartite_hit_lower_tail q J U X r cap leaf hp hqr)).trans
  apply Real.exp_le_exp.mpr
  have hsq : (epsilon * U.card / (2 * L ^ 2)) ^ 2 ≤ (X.card : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hX 2
  have hd := div_le_div_of_nonneg_right hsq
    (by positivity : 0 ≤ 512 * (cap : ℝ) ^ 2 * U.card)
  have heq : (epsilon * U.card / (2 * L ^ 2)) ^ 2 /
      (512 * (cap : ℝ) ^ 2 * U.card) =
        epsilon ^ 2 * U.card / (2048 * (cap : ℝ) ^ 2 * L ^ 4) := by
    field_simp
    <;> ring
  rw [heq] at hd
  simpa only [neg_div, neg_mul] using neg_le_neg hd

/-- Unconditional fixed-set one-step growth, with both graph structures constructed.
The next independently sampled layer can use this estimate for every eligible history.
-/
theorem one_step_boundary_growth
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s : ℝ) (hL : 1 ≤ L) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (hU : 1 ≤ U.card)
    (hsmall : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3)
    (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset)
    (hF : (F.card : ℝ) ≤ s * U.card / 4)
    (r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t)
    (hs : 20 * (r : ℝ) * t ≤ s)
    (q : unitInterval) (hratio : 5 * (r : ℝ) ≤ 4 * (q : ℝ) * t)
    (hqr : (1 / 6 : ℝ) ≤ (q : ℝ) * r) :
    (sampleMeasure V q).real
      {omega | ((sampledHitBoundary (G.deleteEdges F) U (sampleVertices omega)).card : ℝ) <
        epsilon * U.card / (32 * L ^ 2)} ≤
      exp (-(q : ℝ) * epsilon * U.card / (160 * (r : ℝ) * L ^ 2)) +
      exp (-epsilon ^ 2 * U.card / (8192 * (t : ℝ) ^ 2 * L ^ 4)) := by
  classical
  obtain ⟨C, star, hp, hC⟩ | ⟨X, leaf, hp, hX⟩ :=
    repaired_structural_alternative G L epsilon s hL heps heps1 hG U hU hsmall
      F hFG hF r t hr ht hs
  · exact (repaired_star_boundary_lower_tail (G.deleteEdges F) U C star r t
      (by omega) (by omega) L epsilon (by linarith) heps.le hp hC q hratio).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hb := bipartite_boundary_lower_tail q (G.deleteEdges F) U X hU r (2 * t)
      (by omega) leaf hp L epsilon (by linarith) heps.le hX hqr
    have heq : exp (-epsilon ^ 2 * U.card / (2048 * ((2 * t : ℕ) : ℝ) ^ 2 * L ^ 4)) =
        exp (-epsilon ^ 2 * U.card / (8192 * (t : ℝ) ^ 2 * L ^ 4)) := by
      push_cast
      congr 1
      ring
    rw [heq] at hb
    exact hb.trans (le_add_of_nonneg_left (Real.exp_pos _).le)

/-- Natural-valued source parameters with every rounding loss explicit. -/
theorem source_nat_parameters (p q : unitInterval) (L : ℝ)
    (hp : 0 < (p : ℝ)) (hL : 16 ≤ L) (hq : (p : ℝ) / (6 * L ^ 4) ≤ (q : ℝ)) :
    let r := ⌈(p : ℝ)⁻¹ * L ^ 4⌉₊
    let t := ⌈((p : ℝ)⁻¹) ^ 2 * L ^ 9⌉₊
    1 ≤ r ∧ 1 ≤ t ∧
      (r : ℝ) ≤ 2 * (p : ℝ)⁻¹ * L ^ 4 ∧
      (t : ℝ) ≤ 2 * ((p : ℝ)⁻¹) ^ 2 * L ^ 9 ∧
      20 * (r : ℝ) * t ≤ 80 * ((p : ℝ)⁻¹) ^ 3 * L ^ 13 ∧
      5 * (r : ℝ) ≤ 4 * (q : ℝ) * t ∧
      (1 / 6 : ℝ) ≤ (q : ℝ) * r := by
  let a := (p : ℝ)⁻¹ * L ^ 4
  let b := ((p : ℝ)⁻¹) ^ 2 * L ^ 9
  have hL1 : 1 ≤ L := by linarith
  have hpinv : 1 ≤ (p : ℝ)⁻¹ := (one_le_inv₀ hp).mpr p.property.2
  have ha : 1 ≤ a := one_le_mul_of_one_le_of_one_le hpinv (one_le_pow₀ hL1)
  have hb : 1 ≤ b := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hpinv) (one_le_pow₀ hL1)
  have hra : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
  have htb : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
  have hr2 : (⌈a⌉₊ : ℝ) ≤ 2 * a := by linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ a)]
  have ht2 : (⌈b⌉₊ : ℝ) ≤ 2 * b := by linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ b)]
  have hr1 : 1 ≤ ⌈a⌉₊ := by exact_mod_cast (ha.trans hra)
  have ht1 : 1 ≤ ⌈b⌉₊ := by exact_mod_cast (hb.trans htb)
  have hbudget : 20 * (⌈a⌉₊ : ℝ) * ⌈b⌉₊ ≤ 80 * ((p : ℝ)⁻¹) ^ 3 * L ^ 13 := by
    have hm := mul_le_mul hr2 ht2 (Nat.cast_nonneg ⌈b⌉₊) (by linarith : 0 ≤ 2 * a)
    have heq : 20 * ((2 * a) * (2 * b)) = 80 * ((p : ℝ)⁻¹) ^ 3 * L ^ 13 := by dsimp [a, b]; ring
    nlinarith
  have hqat : (p : ℝ) / (6 * L ^ 4) * b ≤ (q : ℝ) * (⌈b⌉₊ : ℝ) :=
    mul_le_mul hq htb (by linarith : 0 ≤ b) q.property.1
  have heq : 4 * ((p : ℝ) / (6 * L ^ 4)) * b = (2 * L / 3) * a := by
    dsimp [a, b]
    field_simp
    <;> ring
  have hrat0 : 10 * a ≤ 4 * ((p : ℝ) / (6 * L ^ 4)) * b := by
    rw [heq]
    exact mul_le_mul_of_nonneg_right (by linarith : (10 : ℝ) ≤ 2 * L / 3) (by linarith : 0 ≤ a)
  have hratio : 5 * (⌈a⌉₊ : ℝ) ≤ 4 * (q : ℝ) * (⌈b⌉₊ : ℝ) := by nlinarith
  have hqar : (p : ℝ) / (6 * L ^ 4) * a ≤ (q : ℝ) * (⌈a⌉₊ : ℝ) :=
    mul_le_mul hq hra (by linarith : 0 ≤ a) q.property.1
  have heqa : (p : ℝ) / (6 * L ^ 4) * a = (1 / 6 : ℝ) := by
    dsimp [a]
    field_simp
  rw [heqa] at hqar
  exact ⟨hr1, ht1, by simpa only [a, mul_assoc] using hr2,
    by simpa only [b, mul_assoc] using ht2, hbudget, hratio, hqar⟩

theorem source_failure_exponents (p q : unitInterval) (L epsilon w : ℝ) (r t : ℕ)
    (hp : 0 < (p : ℝ)) (hL : 1 ≤ L) (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hw : 0 ≤ w) (hr : 0 < r) (ht : 0 < t)
    (hq : (p : ℝ) / (6 * L ^ 4) ≤ (q : ℝ))
    (hrup : (r : ℝ) ≤ 2 * (p : ℝ)⁻¹ * L ^ 4)
    (htup : (t : ℝ) ≤ 2 * ((p : ℝ)⁻¹) ^ 2 * L ^ 9) :
    epsilon ^ 2 * (p : ℝ) ^ 4 * w / (32768 * L ^ 22) ≤
      (q : ℝ) * epsilon * w / (160 * (r : ℝ) * L ^ 2) ∧
    epsilon ^ 2 * (p : ℝ) ^ 4 * w / (32768 * L ^ 22) ≤
      epsilon ^ 2 * w / (8192 * (t : ℝ) ^ 2 * L ^ 4) := by
  have hLp : 0 < L := by linarith
  have hq0 : 0 ≤ (q : ℝ) := q.property.1
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have htp : (0 : ℝ) < t := by exact_mod_cast ht
  have hpowp : (p : ℝ) ^ 4 ≤ (p : ℝ) ^ 2 := by
    have h2 := pow_le_one₀ p.property.1 p.property.2 (n := 2)
    nlinarith [sq_nonneg ((p : ℝ) ^ 2)]
  have hnum : epsilon ^ 2 * (p : ℝ) ^ 4 * w ≤ epsilon * (p : ℝ) ^ 2 * w := by
    have he2 : epsilon ^ 2 ≤ epsilon := by nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul he2 hpowp (by positivity) heps) hw
  have hden : 1920 * L ^ 10 ≤ 32768 * L ^ 22 := by
    have hpow := pow_le_pow_right₀ hL (by norm_num : 10 ≤ 22)
    nlinarith [pow_nonneg hLp.le 10]
  have htarget : epsilon ^ 2 * (p : ℝ) ^ 4 * w / (32768 * L ^ 22) ≤
      epsilon * (p : ℝ) ^ 2 * w / (1920 * L ^ 10) :=
    div_le_div₀ (by positivity) hnum (by positivity) hden
  constructor
  · have hnumq : ((p : ℝ) / (6 * L ^ 4)) * epsilon * w ≤ (q : ℝ) * epsilon * w := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq heps) hw
    have hdenr : 160 * (r : ℝ) * L ^ 2 ≤ 160 * (2 * (p : ℝ)⁻¹ * L ^ 4) * L ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hrup (by positivity : 0 ≤ 160 * L ^ 2)]
    have heq : ((p : ℝ) / (6 * L ^ 4)) * epsilon * w /
        (160 * (2 * (p : ℝ)⁻¹ * L ^ 4) * L ^ 2) =
        epsilon * (p : ℝ) ^ 2 * w / (1920 * L ^ 10) := by field_simp; ring
    rw [← heq] at htarget
    exact htarget.trans (div_le_div₀ (by positivity) hnumq (by positivity) hdenr)
  · have ht2 := pow_le_pow_left₀ (Nat.cast_nonneg t) htup 2
    have hdent : 8192 * (t : ℝ) ^ 2 * L ^ 4 ≤
        8192 * (2 * ((p : ℝ)⁻¹) ^ 2 * L ^ 9) ^ 2 * L ^ 4 := by
      nlinarith [mul_le_mul_of_nonneg_right ht2 (by positivity : 0 ≤ 8192 * L ^ 4)]
    have heq : epsilon ^ 2 * w / (8192 * (2 * ((p : ℝ)⁻¹) ^ 2 * L ^ 9) ^ 2 * L ^ 4) =
        epsilon ^ 2 * (p : ℝ) ^ 4 * w / (32768 * L ^ 22) := by field_simp; ring
    rw [← heq]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hdent

theorem source_one_step_boundary_growth
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hL : 16 ≤ L) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hq : (p : ℝ) / (6 * L ^ 4) ≤ (q : ℝ))
    (hs : 80 * ((p : ℝ)⁻¹) ^ 3 * L ^ 13 ≤ s)
    (hG : RobustCore.RobustExpanderAt G L epsilon s)
    (U : Finset V) (hU : 1 ≤ U.card)
    (hsmall : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3)
    (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset)
    (hF : (F.card : ℝ) ≤ s * U.card / 4) :
    (sampleMeasure V q).real
      {omega | ((SampledReachability.sampledHitBoundary (G.deleteEdges F) U
        (sampleVertices omega)).card : ℝ) < epsilon * U.card / (32 * L ^ 2)} ≤
      2 * exp (-epsilon ^ 2 * (p : ℝ) ^ 4 * U.card / (32768 * L ^ 22)) := by
  classical
  let r := ⌈(p : ℝ)⁻¹ * L ^ 4⌉₊
  let t := ⌈((p : ℝ)⁻¹) ^ 2 * L ^ 9⌉₊
  obtain ⟨hr, ht, hrup, htup, hbudget, hratio, hqr⟩ := source_nat_parameters p q L hp hL hq
  have hmain := one_step_boundary_growth G L epsilon s (by linarith) heps heps1 hG
    U hU hsmall F hFG hF r t hr ht (hbudget.trans hs) q hratio hqr
  obtain ⟨hA, hB⟩ := source_failure_exponents p q L epsilon U.card r t hp
    (by linarith) heps.le heps1 (Nat.cast_nonneg _) (by omega) (by omega) hq hrup htup
  let d := epsilon ^ 2 * (p : ℝ) ^ 4 * U.card / (32768 * L ^ 22)
  have hAe : exp (-(q : ℝ) * epsilon * U.card / (160 * (r : ℝ) * L ^ 2)) ≤ exp (-d) := by
    apply Real.exp_le_exp.mpr
    simpa only [d, neg_div, neg_mul] using neg_le_neg hA
  have hBe : exp (-epsilon ^ 2 * U.card / (8192 * (t : ℝ) ^ 2 * L ^ 4)) ≤ exp (-d) := by
    apply Real.exp_le_exp.mpr
    simpa only [d, neg_div, neg_mul] using neg_le_neg hB
  have hresult := hmain.trans (add_le_add hAe hBe)
  have heq : exp (-d) + exp (-d) = 2 * exp (-d) := by ring
  rw [heq] at hresult
  simpa only [d, neg_div, neg_mul] using hresult

theorem source_budget_of_reservoir_budget (p : unitInterval) (L : ℝ)
    (hp : 0 < (p : ℝ)) (hL : 16 ≤ L) :
    80 * ((p : ℝ)⁻¹) ^ 3 * L ^ 13 ≤ ((p : ℝ)⁻¹) ^ 4 * L ^ 30 := by
  have hL1 : 1 ≤ L := by linarith
  have hpow := pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 17)
  have hbig : 80 * (p : ℝ) ≤ L ^ 17 := by nlinarith [p.property.2]
  calc
    _ = (80 * (p : ℝ)) * (((p : ℝ)⁻¹) ^ 4 * L ^ 13) := by field_simp
    _ ≤ L ^ 17 * (((p : ℝ)⁻¹) ^ 4 * L ^ 13) := mul_le_mul_of_nonneg_right hbig (by positivity)
    _ = _ := by ring

/-- Fixed-set growth directly under the reservoir lemma budget, with rounding absorbed. -/
theorem reservoir_budget_one_step_growth
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hL : 16 ≤ L) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hq : (p : ℝ) / (6 * L ^ 4) ≤ (q : ℝ))
    (hs : ((p : ℝ)⁻¹) ^ 4 * L ^ 30 ≤ s)
    (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (hU : 1 ≤ U.card)
    (hsmall : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3)
    (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset)
    (hF : (F.card : ℝ) ≤ s * U.card / 4) :
    (sampleMeasure V q).real
      {omega | ((sampledHitBoundary (G.deleteEdges F) U
        (sampleVertices omega)).card : ℝ) < epsilon * U.card / (32 * L ^ 2)} ≤
      2 * exp (-epsilon ^ 2 * (p : ℝ) ^ 4 * U.card / (32768 * L ^ 22)) :=
  source_one_step_boundary_growth G p q L epsilon s hp hL heps heps1 hq
    ((source_budget_of_reservoir_budget p L hp hL).trans hs)
    hG U hU hsmall F hFG hF

end Erdos585.Attempt6.ReachabilityAlternative
