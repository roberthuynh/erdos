import Openmath.Proofs.PaperSupport.Counter90.Types

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.Counter90

theorem pair_lower {V : Type*} [DecidableEq V] (Q A B : Finset V)
    (ha : 6 ≤ (Q ∩ A).card) (hb : 6 ≤ (Q ∩ B).card) :
    12 ≤ Q.card + (A ∩ B).card := by
  have hu : (Q ∩ A) ∪ (Q ∩ B) ⊆ Q := by
    intro x hx
    rcases mem_union.mp hx with h | h
    · exact (mem_inter.mp h).1
    · exact (mem_inter.mp h).1
  have hi : (Q ∩ A) ∩ (Q ∩ B) ⊆ A ∩ B := by
    intro x hx
    obtain ⟨hxa,hxb⟩ := mem_inter.mp hx
    exact mem_inter.mpr ⟨(mem_inter.mp hxa).2,(mem_inter.mp hxb).2⟩
  have hc := card_union_add_card_inter (Q ∩ A) (Q ∩ B)
  have h1 := card_le_card hu
  have h2 := card_le_card hi
  omega

theorem degree_six_full {V : Type*} [DecidableEq V] (P N : Finset V)
    (hc : N.card = 6) (hd : 6 ≤ (P ∩ N).card) : N ⊆ P := by
  have heq : P ∩ N = N := eq_of_subset_of_card_le inter_subset_right (by omega)
  rw [← heq]
  exact inter_subset_left

theorem base_row_degree (Q : Finset (Fin 12)) (hq : Q ⊆ baseColumns) (i : Fin 10) :
    rowDegree Q i = (Q ∩ baseNeighbors i).card := by
  unfold rowDegree
  congr 1
  ext j
  simp only [rowDegree,baseNeighbors,mem_inter]
  constructor
  · rintro ⟨hQ,hN⟩
    exact ⟨hQ,hq hQ,hN⟩
  · rintro ⟨hQ,_,hN⟩
    exact ⟨hQ,hN⟩

theorem pair_base_lower (Q : Finset (Fin 12)) (hq : Q ⊆ baseColumns)
    (i j : Fin 10) (hi : 6 ≤ rowDegree Q i) (hj : 6 ≤ rowDegree Q j) :
    12 ≤ Q.card + (baseNeighbors i ∩ baseNeighbors j).card := by
  rw [base_row_degree Q hq] at hi hj
  exact pair_lower Q _ _ hi hj

theorem card_excluding (P S : Finset (Fin 10)) (hs : ∀ i ∈ S, i ∉ P) :
    P.card ≤ (univ \ S).card := by
  apply card_le_card
  intro i hi
  exact mem_sdiff.mpr ⟨mem_univ _,fun h => hs i h hi⟩

theorem lastColumn : columnNeighbors 11 = {0,1,2,3,4,9} := by decide
theorem beforeLastColumn : columnNeighbors 10 = {0,1,2,3,4,5} := by decide
theorem lastColumn_card : (columnNeighbors 11).card = 6 := by decide
theorem beforeLastColumn_card : (columnNeighbors 10).card = 6 := by decide
theorem lastRow_card : (rowNeighbors 9).card = 6 := by decide
theorem lastRow_lastColumn : (11 : Fin 12) ∈ rowNeighbors 9 := by decide
theorem firstPair_inter : (rowNeighbors 1 ∩ rowNeighbors 9).card = 1 := by decide
theorem clippedPair_inter : ((rowNeighbors 0 \ {11}) ∩ (rowNeighbors 1 \ {11})).card = 2 := by decide
theorem baseColumns_card : baseColumns.card = 10 := by decide
theorem rowOne_base : (baseNeighbors 1).card = 5 := by decide
theorem rowZero_two_inter : (baseNeighbors 0 ∩ baseNeighbors 2).card = 3 := by decide
theorem rowZero_three_inter : (baseNeighbors 0 ∩ baseNeighbors 3).card = 4 := by decide
theorem rowZero_five_inter : (baseNeighbors 0 ∩ baseNeighbors 5).card = 5 := by decide
theorem remainingRows_card : remainingRows.card = 7 := by decide
theorem exceptional_card : exceptional.card = 4 := by decide
theorem remaining_complete_card : (remainingRows \ exceptional).card = 3 := by decide
theorem holes_two_card : (holes 2).card = 3 := by decide
theorem holes_three_card : (holes 3).card = 2 := by decide
theorem holes_four_card : (holes 4).card = 2 := by decide
theorem holes_two_three_disjoint : Disjoint (holes 2) (holes 3) := by decide
theorem holes_two_four_disjoint : Disjoint (holes 2) (holes 4) := by decide
theorem holes_three_four_disjoint : Disjoint (holes 3) (holes 4) := by decide

/-- A sixteen-subset typed fixed-incidence check, proved by the ordinary kernel. -/
theorem exceptional_holes_lower (S : Finset (Fin 10)) (hs : S ⊆ exceptional)
    (hc : 3 ≤ S.card) : 5 ≤ (S.biUnion holes).card := by
  have hcheck : ∀ T ∈ exceptional.powerset, 3 ≤ T.card → 5 ≤ (T.biUnion holes).card := by decide
  exact hcheck S (mem_powerset.mpr hs) hc

theorem holes_omitted_lower (Q : Finset (Fin 12)) (hq : Q ⊆ baseColumns)
    (i : Fin 10) (hi : 6 ≤ rowDegree Q i) :
    (holes i).card + 6 ≤ Q.card + (holes i \ Q).card := by
  have hrow := card_sdiff_add_card_inter Q (holes i)
  have hhole := card_sdiff_add_card_inter (holes i) Q
  have heq : Q \ holes i = Q ∩ rowNeighbors i := by
    ext j
    simp only [holes,mem_sdiff,mem_inter]
    constructor
    · rintro ⟨hj,hn⟩
      exact ⟨hj,by by_contra h; exact hn ⟨hq hj,h⟩⟩
    · rintro ⟨hj,hn⟩
      exact ⟨hj,fun h => h.2 hn⟩
  rw [heq] at hrow
  rw [inter_comm] at hhole
  unfold rowDegree at hi
  omega

end Erdos585.Counter90
