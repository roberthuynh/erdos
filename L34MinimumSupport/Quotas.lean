import L34MinimumSupport.Source

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.L34MinimumSupport
open QB4 B5
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Exact L34 source quotas retain every source vertex or lose only one. -/
theorem retained_factor_sorted {q : ℕ} {U W : Finset V} (hq : 6 ≤ q)
    (hUW : Disjoint U W) (_hn : 2 * q ≤ #U + #W) (horder : #U ≤ #W)
    (hminU : ∀ a ∈ U, q ≤ dg G W a) (hcapU : ∀ a ∈ U, dg G W a ≤ 2 * q - 2)
    (hminW : ∀ w ∈ W, q ≤ dg G U w) (hcapW : ∀ w ∈ W, dg G U w ≤ 2 * q - 2)
    (he : ec G U W + (2 * q - 5) = (q - 1) * (#U + #W))
    (hs : L34.Sparse q G U W) :
    ∃ A B : Finset V, A ⊆ U ∧ B ⊆ W ∧ Disjoint A B ∧
      #U + #W ≤ #A + #B + 1 ∧ FactorOn q G A B := by
  have hcapUi : ∀ a ∈ U, (dg G W a : ℤ) ≤ 2 * (q : ℤ) - 2 := fun a ha => by
    have hd := hcapU a ha;omega
  have hdU := deficiency_eq (G := G) (2 * (q : ℤ) - 2) W U
  have hd0 := deficiency_nonneg (G := G) (2 * (q : ℤ) - 2) hcapUi
  have hqZ : 6 ≤ (q : ℤ) := by exact_mod_cast hq
  zify at he horder
  rw [Bq.pred_cast (by omega), L34.constant_cast hq] at he
  have hcases : #W = #U ∨ #W = #U + 1 := by
    have ht : (#W : ℤ) - #U < 2 := by
      by_contra! hbad
      have hp : 0 ≤ ((q : ℤ) - 1) * (((#W : ℤ) - #U) - 2) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
    omega
  rcases hcases with hbal | hsur
  · have hbalZ : (#W : ℤ) = #U := by exact_mod_cast hbal
    have hd : deficiency (2 * (q : ℤ) - 2) G W U = 2 * (q : ℤ) - 5 := by
      rw [hbalZ] at he;nlinarith
    have h : L34.Input q 0 G U W :=
      ⟨by omega,by simpa using hbal,hminU,hcapU,hminW,hcapW,by simpa using hd,hs⟩
    exact ⟨U,W,Subset.refl U,Subset.refl W,hUW,by omega,h.balanced_factor hq⟩
  · have hsurZ : (#W : ℤ) = #U + 1 := by exact_mod_cast hsur
    have hd : deficiency (2 * (q : ℤ) - 2) G W U = (q : ℤ) - 4 := by
      rw [hsurZ] at he;nlinarith
    have h : L34.Input q 1 G U W :=
      ⟨by omega,hsur,hminU,hcapU,hminW,hcapW,by norm_num;linarith,hs⟩
    obtain ⟨w,hw,hf⟩ := h.surplus_factor hq
    have hwcard := card_erase_add_one hw
    exact ⟨U,W.erase w,Subset.refl U,erase_subset w W,
      hUW.mono (Subset.refl U) (erase_subset w W),by omega,hf⟩

/-- Sorting is internal and preserves the actual original edge quotas. -/
theorem retained_factor {q : ℕ} {U W : Finset V} (hq : 6 ≤ q)
    (hUW : Disjoint U W) (hn : 2 * q ≤ #U + #W)
    (hminU : ∀ a ∈ U, q ≤ dg G W a) (hcapU : ∀ a ∈ U, dg G W a ≤ 2 * q - 2)
    (hminW : ∀ w ∈ W, q ≤ dg G U w) (hcapW : ∀ w ∈ W, dg G U w ≤ 2 * q - 2)
    (he : ec G U W + (2 * q - 5) = (q - 1) * (#U + #W))
    (hs : L34.Sparse q G U W) :
    ∃ A B : Finset V, A ⊆ U ∧ B ⊆ W ∧ Disjoint A B ∧
      #U + #W ≤ #A + #B + 1 ∧ FactorOn q G A B := by
  by_cases horder : #U ≤ #W
  · exact retained_factor_sorted hq hUW hn horder hminU hcapU hminW hcapW he hs
  · have he' : ec G W U + (2 * q - 5) = (q - 1) * (#W + #U) := by
      rw [ec_comm,add_comm (#W) (#U)];exact he
    obtain ⟨A,B,hA,hB,hAB,hcard,hf⟩ := retained_factor_sorted hq hUW.symm (by omega)
      (by omega) hminW hcapW hminU hcapU he' hs.swap
    exact ⟨B,A,hB,hA,hAB.symm,by omega,BqMinimumSupport.factor_swap hf⟩

end Erdos585.L34MinimumSupport
