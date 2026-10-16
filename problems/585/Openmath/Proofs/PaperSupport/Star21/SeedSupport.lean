import Openmath.Proofs.PaperSupport.Star21.Types

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Star21

def seedRowDegree (Q : Finset (Fin 12)) (i : Fin 9) : ℕ :=
  (Q.filter fun j => seedRel i j).card

theorem holes_card (i : Fin 9) (hi : i.val < 4) : (holes i).card = 3 := by
  have h : ∀ i : Fin 9, i.val < 4 → (holes i).card = 3 := by decide
  exact h i hi

theorem holes_disjoint (i j : Fin 9) (hij : i ≠ j) : Disjoint (holes i) (holes j) := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hi := (mem_filter.mp hxi).2.2
  have hj := (mem_filter.mp hxj).2.2
  exact hij (Fin.ext (hi.symm.trans hj))

theorem seedRowDegree_eq (Q : Finset (Fin 12)) (i : Fin 9) :
    seedRowDegree Q i = (Q \ holes i).card := by
  unfold seedRowDegree
  congr 1
  ext j
  rw [mem_filter, mem_sdiff]
  rfl

/-- Each active starred row forces at least 10-k of its OWN holes to be omitted. -/
theorem omitted_holes_lower (Q : Finset (Fin 12)) (i : Fin 9)
    (hi : i.val < 4) (hr : 7 ≤ seedRowDegree Q i) :
    10 - Q.card ≤ (holes i \ Q).card := by
  have hrow := card_sdiff_add_card_inter Q (holes i)
  have hhole := card_sdiff_add_card_inter (holes i) Q
  rw [holes_card i hi, inter_comm] at hhole
  rw [← seedRowDegree_eq] at hrow
  omega

/-- New seed exclusion covers ALL possible original active supports, not one shore. -/
theorem seed_no_balanced_support (P : Finset (Fin 9)) (Q : Finset (Fin 12))
    (hne : P.Nonempty) (hbal : P.card = Q.card)
    (hr : ∀ i ∈ P, 7 ≤ seedRowDegree Q i) : False := by
  let S := P.filter fun i => i.val < 4
  have hSc : P.card ≤ S.card + 5 := by
    have hpart : (P \ S).card + S.card = P.card :=
      card_sdiff_add_card_eq_card (filter_subset _ P)
    have hsub : P \ S ⊆ univ.filter fun i : Fin 9 => 4 ≤ i.val := by
      intro i hi
      obtain ⟨hiP, hiS⟩ := mem_sdiff.mp hi
      have hni : ¬ i.val < 4 := by
        intro h
        exact hiS (mem_filter.mpr ⟨hiP, h⟩)
      exact mem_filter.mpr ⟨mem_univ _, by omega⟩
    have hfive : (univ.filter fun i : Fin 9 => 4 ≤ i.val).card = 5 := by decide
    have hle := card_le_card hsub
    rw [hfive] at hle
    omega
  have hklo : 7 ≤ Q.card := by
    obtain ⟨i, hi⟩ := hne
    exact (hr i hi).trans (card_le_card (filter_subset _ Q))
  have hkhi : Q.card ≤ 9 := by
    have h := Finset.card_le_univ P
    simp only [card_univ, Fintype.card_fin] at h
    omega
  have hdis : (S : Set (Fin 9)).PairwiseDisjoint (fun i => holes i \ Q) := by
    intro i hi j hj hij
    exact (holes_disjoint i j hij).mono Finset.sdiff_subset Finset.sdiff_subset
  have hsub : S.biUnion (fun i => holes i \ Q) ⊆ univ \ Q := by
    intro j hj
    obtain ⟨i, hi, hj⟩ := mem_biUnion.mp hj
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hj).2⟩
  have hsumupper : (∑ i ∈ S, (holes i \ Q).card) ≤ 12 - Q.card := by
    rw [← card_biUnion hdis]
    have h := card_le_card hsub
    rw [card_sdiff_of_subset (subset_univ Q), card_univ, Fintype.card_fin] at h
    exact h
  have hsumlower : (10-Q.card)*S.card ≤ ∑ i ∈ S, (holes i \ Q).card := by
    calc
      _ = ∑ i ∈ S, (10-Q.card) := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ S, (holes i \ Q).card := by
        apply sum_le_sum
        intro i hi
        obtain ⟨hiP, hi4⟩ := mem_filter.mp hi
        exact omitted_holes_lower Q i hi4 (hr i hiP)
  have hk : Q.card = 7 ∨ Q.card = 8 ∨ Q.card = 9 := by omega
  rcases hk with hk | hk | hk
  · rw [hk] at hsumlower hsumupper
    simp only [Nat.reduceSub] at hsumlower hsumupper
    omega
  · rw [hk] at hsumlower hsumupper
    simp only [Nat.reduceSub] at hsumlower hsumupper
    omega
  · rw [hk] at hsumlower hsumupper
    simp only [Nat.reduceSub, one_mul] at hsumlower hsumupper
    omega

end Erdos585.Star21
