import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Actual six-neighbor linear-family positive trace weight.
The proof uses a no-theta3 count and disjoint-fibre double counting.
No chosen favorable family, rank supplier or bounded ambient type is assumed.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

universe u
namespace Erdos585.QB6C02SixNeighbor
open Finset
variable {V : Type u} [DecidableEq V]

lemma erase_disjoint_of_inter_card_le_one {S T : Finset V} {x : V}
    (hST : #(S ∩ T) ≤ 1) (hxS : x ∈ S) (hxT : x ∈ T) :
    Disjoint (S.erase x) (T.erase x) := by
  apply disjoint_left.mpr
  intro y hyS hyT
  have hxy := card_le_one.mp hST x (mem_inter.mpr ⟨hxS, hxT⟩)
    y (mem_inter.mpr ⟨(mem_erase.mp hyS).2, (mem_erase.mp hyT).2⟩)
  exact (mem_erase.mp hyS).1 hxy.symm

lemma incident_erase_sum_le {N : Finset V} {H : Finset (Finset V)}
    (hsub : ∀ S ∈ H, S ⊆ N)
    (hlinear : ∀ S ∈ H, ∀ T ∈ H, S ≠ T → #(S ∩ T) ≤ 1)
    {x : V} (hx : x ∈ N) :
    (∑ S ∈ H.filter (fun S => x ∈ S), #(S.erase x)) ≤ #N - 1 := by
  classical
  let J := H.filter (fun S => x ∈ S)
  have hdis : (J : Set (Finset V)).PairwiseDisjoint (fun S => S.erase x) := by
    intro S hS T hT hST
    obtain ⟨hSH, hxS⟩ := mem_filter.mp hS
    obtain ⟨hTH, hxT⟩ := mem_filter.mp hT
    exact erase_disjoint_of_inter_card_le_one (hlinear S hSH T hTH hST) hxS hxT
  have hcontain : J.biUnion (fun S => S.erase x) ⊆ N.erase x := by
    intro y hy
    obtain ⟨S, hS, hyS⟩ := mem_biUnion.mp hy
    exact mem_erase.mpr ⟨(mem_erase.mp hyS).1,
      hsub S (mem_filter.mp hS).1 (mem_erase.mp hyS).2⟩
  have hc := card_le_card hcontain
  rw [card_biUnion hdis, card_erase_of_mem hx] at hc
  exact hc

lemma incidence_card_sum {N : Finset V} {H : Finset (Finset V)}
    (hsub : ∀ S ∈ H, S ⊆ N) :
    (∑ x ∈ N, #(H.filter (fun S => x ∈ S))) = ∑ S ∈ H, #S := by
  classical
  calc
    _ = ∑ x ∈ N, ∑ S ∈ H, if x ∈ S then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro x _
      have heq : (∑ S ∈ H, if x ∈ S then (1 : ℕ) else 0) =
          #(H.filter (fun S => x ∈ S)) := by
        rw [← sum_filter]
        simp
      exact heq.symm
    _ = ∑ S ∈ H, ∑ x ∈ N, if x ∈ S then (1 : ℕ) else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro S hS
      rw [← sum_filter]
      have hfilter : N.filter (fun x => x ∈ S) = S := by
        ext x
        simp only [mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hsub S hS h, h⟩⟩
      rw [hfilter]
      simp

lemma other_card_sum_le_seven {N : Finset V} {H : Finset (Finset V)}
    (hN : #N = 6) (hsub : ∀ S ∈ H, S ⊆ N)
    (hlinear : ∀ S ∈ H, ∀ T ∈ H, S ≠ T → #(S ∩ T) ≤ 1)
    {S T : Finset V} (hS : S ∈ H) (hT : T ∈ H) (hTS : T ≠ S) :
    #T + #S ≤ 7 := by
  have hcontain : T \ S ⊆ N \ S := by
    intro x hx
    exact mem_sdiff.mpr ⟨hsub T hT (mem_sdiff.mp hx).1, (mem_sdiff.mp hx).2⟩
  have hc := card_le_card hcontain
  have hNsplit := card_sdiff_add_card_eq_card (hsub S hS)
  have hTsplit := card_sdiff_add_card_inter T S
  have hi := hlinear T hT S hS hTS
  omega

lemma other_contains_complement {N : Finset V} {H : Finset (Finset V)}
    (hN : #N = 6) (hsub : ∀ S ∈ H, S ⊆ N)
    (hsize : ∀ S ∈ H, 3 ≤ #S)
    (hlinear : ∀ S ∈ H, ∀ T ∈ H, S ≠ T → #(S ∩ T) ≤ 1)
    {S T : Finset V} (hS : S ∈ H) (hScard : #S = 4)
    (hT : T ∈ H) (hTS : T ≠ S) : N \ S ⊆ T := by
  have hcontain : T \ S ⊆ N \ S := by
    intro x hx
    exact mem_sdiff.mpr ⟨hsub T hT (mem_sdiff.mp hx).1, (mem_sdiff.mp hx).2⟩
  have hc := card_le_card hcontain
  have hNsplit := card_sdiff_add_card_eq_card (hsub S hS)
  have hTsplit := card_sdiff_add_card_inter T S
  have hi := hlinear T hT S hS hTS
  have hTsize := hsize T hT
  have heq : T \ S = N \ S := eq_of_subset_of_card_le hcontain (by omega)
  intro x hx
  have hxTS : x ∈ T \ S := heq.symm ▸ hx
  exact sdiff_subset hxTS

lemma triple_family_card_le_four {N : Finset V} {H : Finset (Finset V)}
    (hN : #N = 6) (hsub : ∀ S ∈ H, S ⊆ N)
    (hthree : ∀ S ∈ H, #S = 3)
    (hlinear : ∀ S ∈ H, ∀ T ∈ H, S ≠ T → #(S ∩ T) ≤ 1) : #H ≤ 4 := by
  classical
  have hpoint : ∀ x ∈ N, #(H.filter (fun S => x ∈ S)) ≤ 2 := by
    intro x hx
    have hb := incident_erase_sum_le hsub hlinear hx
    have heq : (∑ S ∈ H.filter (fun S => x ∈ S), #(S.erase x)) =
        2 * #(H.filter (fun S => x ∈ S)) := by
      calc
        _ = ∑ _S ∈ H.filter (fun S => x ∈ S), (2 : ℕ) := by
          apply sum_congr rfl
          intro S hS
          obtain ⟨hSH, hxS⟩ := mem_filter.mp hS
          rw [card_erase_of_mem hxS, hthree S hSH]
        _ = _ := by simp [sum_const, mul_comm]
    rw [heq, hN] at hb
    omega
  have hsum := sum_le_sum hpoint
  have hi := incidence_card_sum hsub
  have hleft : (∑ S ∈ H, #S) = 3 * #H := by
    rw [sum_congr rfl hthree]
    simp [sum_const, mul_comm]
  have hright : (∑ _x ∈ N, (2 : ℕ)) = 12 := by
    norm_num [sum_const, nsmul_eq_mul, hN]
  rw [hi, hleft, hright] at hsum
  omega

/-- Literal actual finite-family trace bound in natural numbers. -/
theorem six_neighbor_nat (N : Finset V) (H : Finset (Finset V))
    (hN : #N = 6) (hsub : ∀ S ∈ H, S ⊆ N)
    (hsize : ∀ S ∈ H, 3 ≤ #S)
    (hlinear : ∀ S ∈ H, ∀ T ∈ H, S ≠ T → #(S ∩ T) ≤ 1) :
    (∑ S ∈ H, (#S - 2)) ≤ 4 := by
  classical
  by_cases hbig : ∃ S ∈ H, 4 ≤ #S
  · obtain ⟨S, hS, hScard⟩ := hbig
    have hSsix : #S ≤ 6 := by have hc := card_le_card (hsub S hS); omega
    by_cases hSlarge : 5 ≤ #S
    · have hHeq : H = {S} := by
        ext T
        constructor
        · intro hT
          apply mem_singleton.mpr
          by_contra hTS
          have hb := other_card_sum_le_seven hN hsub hlinear hS hT hTS
          have hTsize := hsize T hT
          omega
        · intro hT
          have hTS := mem_singleton.mp hT
          simpa only [hTS] using hS
      rw [hHeq, sum_singleton]
      omega
    · have hSfour : #S = 4 := by omega
      have hothers : #(H.erase S) ≤ 1 := by
        apply card_le_one.mpr
        intro T hT U hU
        by_contra hTU
        have hTH := (mem_erase.mp hT).2
        have hUH := (mem_erase.mp hU).2
        have hTC := other_contains_complement hN hsub hsize hlinear hS hSfour
          hTH (mem_erase.mp hT).1
        have hUC := other_contains_complement hN hsub hsize hlinear hS hSfour
          hUH (mem_erase.mp hU).1
        have hcontain : N \ S ⊆ T ∩ U := fun x hx => mem_inter.mpr ⟨hTC hx, hUC hx⟩
        have hc := card_le_card hcontain
        have hsplit := card_sdiff_add_card_eq_card (hsub S hS)
        have hi := hlinear T hTH U hUH hTU
        omega
      have hothers_three : ∀ T ∈ H.erase S, #T = 3 := by
        intro T hT
        have hTH := (mem_erase.mp hT).2
        have hb := other_card_sum_le_seven hN hsub hlinear hS hTH (mem_erase.mp hT).1
        have hTsize := hsize T hTH
        omega
      have hothers_sum : (∑ T ∈ H.erase S, (#T - 2)) = #(H.erase S) := by
        rw [sum_congr rfl (fun T hT => by rw [hothers_three T hT])]
        simp
      have hdecomp := sum_erase_add H (fun T => #T - 2) hS
      rw [hothers_sum, hSfour] at hdecomp
      omega
  · have hthree : ∀ S ∈ H, #S = 3 := by
      intro S hS
      have hlo := hsize S hS
      have hnot : ¬ 4 ≤ #S := fun hh => hbig ⟨S, hS, hh⟩
      omega
    have hcard := triple_family_card_le_four hN hsub hthree hlinear
    have hsum : (∑ S ∈ H, (#S - 2)) = #H := by
      rw [sum_congr rfl (fun S hS => by rw [hthree S hS])]
      simp
    rw [hsum]
    exact hcard

/-- Literal integer export; natural subtraction is paid by each actual size bound. -/
theorem six_neighbor_int (N : Finset V) (H : Finset (Finset V))
    (hN : #N = 6) (hsub : ∀ S ∈ H, S ⊆ N)
    (hsize : ∀ S ∈ H, 3 ≤ #S)
    (hlinear : ∀ S ∈ H, ∀ T ∈ H, S ≠ T → #(S ∩ T) ≤ 1) :
    (∑ S ∈ H, ((#S : ℤ) - 2)) ≤ 4 := by
  have hn := six_neighbor_nat N H hN hsub hsize hlinear
  have hc : ((∑ S ∈ H, (#S - 2) : ℕ) : ℤ) = ∑ S ∈ H, ((#S : ℤ) - 2) := by
    rw [Nat.cast_sum]
    apply sum_congr rfl
    intro S hS
    rw [Nat.cast_sub (by have hs := hsize S hS; omega)]
    rfl
  have hnz : ((∑ S ∈ H, (#S - 2) : ℕ) : ℤ) ≤ 4 := by exact_mod_cast hn
  rwa [hc] at hnz

end Erdos585.QB6C02SixNeighbor
