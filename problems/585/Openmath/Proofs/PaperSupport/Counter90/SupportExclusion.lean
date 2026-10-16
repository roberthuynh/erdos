import Openmath.Proofs.PaperSupport.Counter90.SupportFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.Counter90

theorem clipped_row_degree (Q : Finset (Fin 12)) (hq : (11 : Fin 12) ∉ Q) (i : Fin 10) :
    rowDegree Q i = (Q ∩ (rowNeighbors i \ {11})).card := by
  unfold rowDegree
  congr 1
  ext j
  simp only [rowDegree,mem_inter,mem_sdiff,mem_singleton]
  constructor
  · rintro ⟨hQ,hN⟩
    exact ⟨hQ,hN,by intro h; subst j; exact hq hQ⟩
  · rintro ⟨hQ,hN,_⟩
    exact ⟨hQ,hN⟩

theorem omitted_holes_subset (Q : Finset (Fin 12)) (i : Fin 10) :
    holes i \ Q ⊆ baseColumns \ Q := by
  intro j hj
  obtain ⟨hh,hQ⟩ := mem_sdiff.mp hj
  exact mem_sdiff.mpr ⟨(mem_sdiff.mp hh).1,hQ⟩

/-- Every balanced original active support fails an actual induced degree-six constraint. -/
theorem no_balanced_support (P : Finset (Fin 10)) (Q : Finset (Fin 12))
    (hne : P.Nonempty) (hbal : P.card = Q.card)
    (hr : ∀ i ∈ P, 6 ≤ rowDegree Q i)
    (hc : ∀ j ∈ Q, 6 ≤ columnDegree P j) : False := by
  have hten : P.card ≤ 10 := by simpa using card_le_univ P
  have hQ11 : (11 : Fin 12) ∉ Q := by
    intro hj
    have hf := degree_six_full P (columnNeighbors 11) lastColumn_card (hc 11 hj)
    have h1 := hr 1 (hf (by decide : (1 : Fin 10) ∈ columnNeighbors 11))
    have h9 := hr 9 (hf (by decide : (9 : Fin 10) ∈ columnNeighbors 11))
    have hp := pair_lower Q (rowNeighbors 1) (rowNeighbors 9) h1 h9
    rw [firstPair_inter] at hp
    omega
  have hP9 : (9 : Fin 10) ∉ P := by
    intro hi
    have hf := degree_six_full Q (rowNeighbors 9) lastRow_card (hr 9 hi)
    exact hQ11 (hf lastRow_lastColumn)
  have hnine : P.card ≤ 9 := by
    have hp := card_excluding P {9} (by intro i hi; have h := mem_singleton.mp hi; subst i; exact hP9)
    have hs : (univ \ ({9} : Finset (Fin 10))).card = 9 := by decide
    rwa [hs] at hp
  have hQ10 : (10 : Fin 12) ∉ Q := by
    intro hj
    have hf := degree_six_full P (columnNeighbors 10) beforeLastColumn_card (hc 10 hj)
    have h0 := hr 0 (hf (by decide : (0 : Fin 10) ∈ columnNeighbors 10))
    have h1 := hr 1 (hf (by decide : (1 : Fin 10) ∈ columnNeighbors 10))
    rw [clipped_row_degree Q hQ11] at h0 h1
    have hp := pair_lower Q (rowNeighbors 0 \ {11}) (rowNeighbors 1 \ {11}) h0 h1
    rw [clippedPair_inter] at hp
    omega
  have hbase : Q ⊆ baseColumns := by
    intro j hj
    have hlt := j.isLt
    have hne10 : j ≠ 10 := by intro h; subst j; exact hQ10 hj
    have hne11 : j ≠ 11 := by intro h; subst j; exact hQ11 hj
    have hv10 : j.val ≠ 10 := by intro h; exact hne10 (Fin.ext h)
    have hv11 : j.val ≠ 11 := by intro h; exact hne11 (Fin.ext h)
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have hP1 : (1 : Fin 10) ∉ P := by
    intro hi
    have hd := hr 1 hi
    rw [base_row_degree Q hbase] at hd
    have hl : (Q ∩ baseNeighbors 1).card ≤ (baseNeighbors 1).card := card_le_card inter_subset_right
    rw [rowOne_base] at hl
    omega
  have height : P.card ≤ 8 := by
    have hp := card_excluding P {1,9} (by
      intro i hi
      simp only [mem_insert,mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hP1
      · exact hP9)
    have hs : (univ \ ({1,9} : Finset (Fin 10))).card = 8 := by decide
    rwa [hs] at hp
  have hP0 : (0 : Fin 10) ∉ P := by
    intro hi
    have hP2 : (2 : Fin 10) ∉ P := by
      intro h2
      have hp := pair_base_lower Q hbase 0 2 (hr 0 hi) (hr 2 h2)
      rw [rowZero_two_inter] at hp
      omega
    have hseven : P.card ≤ 7 := by
      have hp := card_excluding P {1,2,9} (by
        intro i hi
        simp only [mem_insert,mem_singleton] at hi
        rcases hi with rfl | rfl | rfl
        · exact hP1
        · exact hP2
        · exact hP9)
      have hs : (univ \ ({1,2,9} : Finset (Fin 10))).card = 7 := by decide
      rwa [hs] at hp
    have hP3 : (3 : Fin 10) ∉ P := by
      intro h3
      have hp := pair_base_lower Q hbase 0 3 (hr 0 hi) (hr 3 h3)
      rw [rowZero_three_inter] at hp
      omega
    have hsix : P.card ≤ 6 := by
      have hp := card_excluding P {1,2,3,9} (by
        intro i hi
        simp only [mem_insert,mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl
        · exact hP1
        · exact hP2
        · exact hP3
        · exact hP9)
      have hs : (univ \ ({1,2,3,9} : Finset (Fin 10))).card = 6 := by decide
      rwa [hs] at hp
    have hP5 : (5 : Fin 10) ∉ P := by
      intro h5
      have hp := pair_base_lower Q hbase 0 5 (hr 0 hi) (hr 5 h5)
      rw [rowZero_five_inter] at hp
      omega
    have hfive : P.card ≤ 5 := by
      have hp := card_excluding P {1,2,3,5,9} (by
        intro i hi
        simp only [mem_insert,mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl
        · exact hP1
        · exact hP2
        · exact hP3
        · exact hP5
        · exact hP9)
      have hs : (univ \ ({1,2,3,5,9} : Finset (Fin 10))).card = 5 := by decide
      rwa [hs] at hp
    have hd := hr 0 hi
    have hl : rowDegree Q 0 ≤ Q.card := card_le_card inter_subset_left
    omega
  have hprem : P ⊆ remainingRows := by
    have hf : ∀ i : Fin 10, i ≠ 0 → i ≠ 1 → i ≠ 9 → i ∈ remainingRows := by decide
    intro i hi
    exact hf i (by intro h; subst i; exact hP0 hi)
      (by intro h; subst i; exact hP1 hi) (by intro h; subst i; exact hP9 hi)
  have hseven : P.card ≤ 7 := by
    have hp := card_le_card hprem
    rwa [remainingRows_card] at hp
  have hsix : 6 ≤ Q.card := by
    obtain ⟨i,hi⟩ := hne
    exact (hr i hi).trans (card_le_card inter_subset_left)
  have hk : Q.card = 6 ∨ Q.card = 7 := by omega
  rcases hk with hk | hk
  · let S := P ∩ exceptional
    have hS : S ⊆ exceptional := inter_subset_right
    have hS3 : 3 ≤ S.card := by
      have hsub : P \ S ⊆ remainingRows \ exceptional := by
        intro i hi
        obtain ⟨hiP,hiS⟩ := mem_sdiff.mp hi
        refine mem_sdiff.mpr ⟨hprem hiP,?_⟩
        intro hiE
        exact hiS (mem_inter.mpr ⟨hiP,hiE⟩)
      have hp := card_le_card hsub
      rw [remaining_complete_card] at hp
      have hpart : (P \ S).card + S.card = P.card := card_sdiff_add_card_eq_card inter_subset_left
      omega
    have hsub : S.biUnion holes ⊆ baseColumns \ Q := by
      intro j hj
      obtain ⟨i,hi,hjH⟩ := mem_biUnion.mp hj
      have hiP : i ∈ P := (mem_inter.mp hi).1
      have heq : Q ∩ rowNeighbors i = Q :=
        eq_of_subset_of_card_le inter_subset_left (by change Q.card ≤ rowDegree Q i; rw [hk]; exact hr i hiP)
      have hQN : Q ⊆ rowNeighbors i := by
        have h : Q ∩ rowNeighbors i ⊆ rowNeighbors i := inter_subset_right
        rwa [heq] at h
      obtain ⟨hjB,hjN⟩ := mem_sdiff.mp hjH
      exact mem_sdiff.mpr ⟨hjB,fun hjQ => hjN (hQN hjQ)⟩
    have hl := exceptional_holes_lower S hS hS3
    have hu := card_le_card hsub
    rw [card_sdiff_of_subset hbase,baseColumns_card,hk] at hu
    omega
  · have hPeq : P = remainingRows :=
      eq_of_subset_of_card_le hprem (by rw [remainingRows_card]; omega)
    have h2 : (2 : Fin 10) ∈ P := by rw [hPeq]; decide
    have h3 : (3 : Fin 10) ∈ P := by rw [hPeq]; decide
    have h4 : (4 : Fin 10) ∈ P := by rw [hPeq]; decide
    have h2l := holes_omitted_lower Q hbase 2 (hr 2 h2)
    have h3l := holes_omitted_lower Q hbase 3 (hr 3 h3)
    have h4l := holes_omitted_lower Q hbase 4 (hr 4 h4)
    rw [holes_two_card,hk] at h2l
    rw [holes_three_card,hk] at h3l
    rw [holes_four_card,hk] at h4l
    have h23 : Disjoint (holes 2 \ Q) (holes 3 \ Q) :=
      holes_two_three_disjoint.mono sdiff_subset sdiff_subset
    have h24 : Disjoint (holes 2 \ Q) (holes 4 \ Q) :=
      holes_two_four_disjoint.mono sdiff_subset sdiff_subset
    have h34 : Disjoint (holes 3 \ Q) (holes 4 \ Q) :=
      holes_three_four_disjoint.mono sdiff_subset sdiff_subset
    have h234 : Disjoint ((holes 2 \ Q) ∪ (holes 3 \ Q)) (holes 4 \ Q) :=
      disjoint_union_left.mpr ⟨h24,h34⟩
    have hsub : ((holes 2 \ Q) ∪ (holes 3 \ Q)) ∪ (holes 4 \ Q) ⊆ baseColumns \ Q :=
      union_subset (union_subset (omitted_holes_subset Q 2) (omitted_holes_subset Q 3))
        (omitted_holes_subset Q 4)
    have hu := card_le_card hsub
    rw [card_union_of_disjoint h234,card_union_of_disjoint h23,
      card_sdiff_of_subset hbase,baseColumns_card,hk] at hu
    omega

end Erdos585.Counter90
