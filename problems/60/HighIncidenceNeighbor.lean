import CompletionBasic
import DisjointCellBudget

namespace Erdos60.Completion
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def bundleFinset (G : SimpleGraph V) (v u : V) : Finset V :=
  Finset.univ.filter (fun x => x ∈ bundle G v u)

omit [DecidableEq V] in
@[simp] theorem mem_bundleFinset (G : SimpleGraph V) (v u x : V) :
    x ∈ bundleFinset G v u ↔ x ∈ bundle G v u := by simp [bundleFinset]

theorem exists_clean_sparse_bundle (G : SimpleGraph V) (hG : NoFourCycle G)
    (v : V) (S E : Finset V)
    (hbudget : S.card + 2 * E.card < 2 * G.degree v) :
    ∃ u, G.Adj v u ∧ Disjoint (bundleFinset G v u) E ∧
      (bundleFinset G v u ∩ S).card ≤ 1 := by
  classical
  have hd : (G.neighborFinset v : Set V).PairwiseDisjoint (bundleFinset G v) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    exact Set.disjoint_left.mp
      (bundles_disjoint hG (by simpa using ha) (by simpa using hb) hab)
      ((mem_bundleFinset G v a x).mp hxa) ((mem_bundleFinset G v b x).mp hxb)
  by_contra hn
  have hclean : ∀ u ∈ G.neighborFinset v, Disjoint (bundleFinset G v u) E →
      2 ≤ (bundleFinset G v u ∩ S).card := by
    intro u hu hc
    by_contra hh
    exact hn ⟨u,by simpa using hu,hc,by omega⟩
  have h := disjoint_cell_budget (G.neighborFinset v) (bundleFinset G v) S E hd hclean
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h
  omega

/-- The actual outside cell loses at most its center and one local neighbor. -/
theorem cell_card_add_two_ge_degree (G : SimpleGraph V) (hG : NoFourCycle G)
    {v u : V} (hvu : G.Adj v u) :
    G.degree u ≤ (Finset.univ.filter (fun x => x ∈ cell G v u)).card + 2 := by
  classical
  let C := Finset.univ.filter (fun x => x ∈ cell G v u)
  let R := G.neighborFinset u ∩ G.neighborFinset v
  have hR : R.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' := Finset.mem_inter.mp ha
    have hb' := Finset.mem_inter.mp hb
    exact common_neighbor_unique hG hvu.ne (by simpa using ha'.2) (by simpa using ha'.1)
      (by simpa using hb'.2) (by simpa using hb'.1)
  have hsub : G.neighborFinset u ⊆ insert v (R ∪ C) := by
    intro x hx
    by_cases hxv : x = v
    · exact Finset.mem_insert.mpr (Or.inl hxv)
    · apply Finset.mem_insert.mpr
      right
      by_cases hvx : G.Adj v x
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hx,by simpa using hvx⟩))
      · exact Finset.mem_union.mpr (Or.inr (by
          simp only [C,Finset.mem_filter,Finset.mem_univ,true_and]
          exact ⟨by simpa using hx,hxv,hvx⟩))
  have hc := Finset.card_le_card hsub
  have hi := Finset.card_insert_le v (R ∪ C)
  have hu := Finset.card_union_le R C
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
  change G.degree u ≤ C.card + 2
  omega


/-- Completion §5's actual high-incidence neighbor. The supplied finite sets
are identified with actual degree predicates; the good full set is full\B.
No selected bundle, low-point witness, or high-incidence conclusion is assumed. -/
theorem high_incidence_neighbor
    (G : SimpleGraph V) (hG : NoFourCycle G) (q : ℕ) (hq : 10^8 ≤ q)
    (hmin : ∀ x, 999 * q ≤ 1000 * G.degree x)
    (hcap : ∀ x, G.degree x ≤ q+1)
    (S D B A : Finset V)
    (hS : ∀ x, x ∈ S ↔ G.degree x ≤ q)
    (hD : ∀ x, x ∈ D ↔ G.degree x ≤ q-1)
    (hA : ∀ x, x ∈ A ↔ G.degree x = q+1 ∧ x ∉ B)
    (hSc : 1000 * S.card ≤ 1001 * q)
    (hDc : 1000 * D.card ≤ q) (hBc : B.card ≤ 11000) (v : V) :
    ∃ u, G.Adj v u ∧ q-2 ≤ (G.neighborFinset u ∩ A).card := by
  classical
  have hUnion := Finset.card_union_le D B
  have hmv := hmin v
  have hbudget : S.card + 2 * (D ∪ B).card < 2 * G.degree v := by omega
  obtain ⟨u,hvu,hclean,hsmall⟩ := exists_clean_sparse_bundle G hG v S (D ∪ B) hbudget
  let C := Finset.univ.filter (fun x => x ∈ cell G v u)
  have hbundle : bundleFinset G v u = insert u C := by
    ext x
    simp [bundleFinset,bundle,C]
  have huC : u ∉ C := by
    intro h
    have hh : u ∈ cell G v u := (Finset.mem_filter.mp h).2
    exact hh.2.2 hvu
  have huBundle : u ∈ bundleFinset G v u := by rw [hbundle]; simp
  have hnot : ∀ x ∈ bundleFinset G v u, x ∉ D ∧ x ∉ B := by
    intro x hx
    constructor
    · intro hxD
      exact Finset.disjoint_left.mp hclean hx (Finset.mem_union.mpr (Or.inl hxD))
    · intro hxB
      exact Finset.disjoint_left.mp hclean hx (Finset.mem_union.mpr (Or.inr hxB))
  have huD := (hnot u huBundle).1
  have hdu : q ≤ G.degree u := by
    have hn : ¬G.degree u ≤ q-1 := fun h => huD ((hD u).mpr h)
    omega
  have hdiag : q+1 ≤ G.degree u + (if u ∈ S then 1 else 0) := by
    split_ifs with huS
    · omega
    · have hn : ¬G.degree u ≤ q := fun h => huS ((hS u).mpr h)
      omega
  have hlow : (C ∩ S).card + (if u ∈ S then 1 else 0) ≤ 1 := by
    by_cases huS : u ∈ S
    · have he : bundleFinset G v u ∩ S = insert u (C ∩ S) := by
        ext x
        simp only [hbundle,Finset.mem_inter,Finset.mem_insert]
        constructor
        · rintro ⟨hx,hxS⟩
          rcases hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr ⟨hx,hxS⟩
        · rintro (rfl | hx)
          · exact ⟨Or.inl rfl,huS⟩
          · exact ⟨Or.inr hx.1,hx.2⟩
      rw [he,Finset.card_insert_of_notMem (fun h => huC (Finset.mem_inter.mp h).1)] at hsmall
      simpa only [if_pos huS] using hsmall
    · have he : bundleFinset G v u ∩ S = C ∩ S := by
        ext x
        simp only [hbundle,Finset.mem_inter,Finset.mem_insert]
        constructor
        · rintro ⟨hx,hxS⟩
          rcases hx with rfl | hx
          · exact False.elim (huS hxS)
          · exact ⟨hx,hxS⟩
        · intro hx
          exact ⟨Or.inr hx.1,hx.2⟩
      rw [he] at hsmall
      simpa only [if_neg huS,Nat.add_zero] using hsmall
  have hsplit : C ⊆ (C ∩ A) ∪ (C ∩ S) := by
    intro x hx
    by_cases hxS : x ∈ S
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hx,hxS⟩))
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_inter.mpr
      refine ⟨hx,(hA x).mpr ⟨?_,?_⟩⟩
      · have hn : ¬G.degree x ≤ q := fun h => hxS ((hS x).mpr h)
        have hc := hcap x
        omega
      · exact (hnot x (by rw [hbundle]; exact Finset.mem_insert.mpr (Or.inr hx))).2
  have hCcard := (Finset.card_le_card hsplit).trans (Finset.card_union_le (C ∩ A) (C ∩ S))
  have hdegree := cell_card_add_two_ge_degree G hG hvu
  change G.degree u ≤ C.card + 2 at hdegree
  have hsub : C ∩ A ⊆ G.neighborFinset u ∩ A := by
    intro x hx
    have hc : x ∈ cell G v u := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).2
    exact Finset.mem_inter.mpr ⟨by simpa using hc.1,(Finset.mem_inter.mp hx).2⟩
  have hcount := Finset.card_le_card hsub
  refine ⟨u,hvu,?_⟩
  omega

#print axioms exists_clean_sparse_bundle
#print axioms cell_card_add_two_ge_degree
#print axioms high_incidence_neighbor


end Erdos60.Completion
