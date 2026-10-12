import Openmath.Proofs.PaperSupport.BqMinSizeSource
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.BqMinimumSupport
open QB4 B5
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem factor_swap {q : ℕ} {U W : Finset V} (h : FactorOn q G U W) :
    FactorOn q G W U := by
  obtain ⟨F,hF,hadj,hU,hW⟩ := h
  refine ⟨F.map ⟨Prod.swap,Prod.swap_injective⟩,?_,?_,fun w hw => ?_,fun u hu => ?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
    obtain ⟨hyU,hyW⟩ := mem_product.mp (hF hy)
    exact mem_product.mpr ⟨hyW,hyU⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
    exact (hadj y hy).symm
  · rw [filter_map,card_map]
    exact hW w hw
  · rw [filter_map,card_map]
    exact hU u hu

/- -/
theorem retained_factor_sorted {q : ℕ} {U W : Finset V} (hq : 5 ≤ q)
    (hUW : Disjoint U W) (_hn : 2 * q ≤ #U + #W) (horder : #U ≤ #W)
    (hminU : ∀ a ∈ U, q ≤ dg G W a) (hcapU : ∀ a ∈ U, dg G W a ≤ 2 * q - 2)
    (hminW : ∀ w ∈ W, q ≤ dg G U w) (hcapW : ∀ w ∈ W, dg G U w ≤ 2 * q - 2)
    (he : ec G U W + q = (q - 1) * (#U + #W)) (hs : Bq.Sparse q G U W) :
    ∃ A B : Finset V, A ⊆ U ∧ B ⊆ W ∧ Disjoint A B ∧
      #U + #W ≤ #A + #B + 1 ∧ FactorOn q G A B := by
  have hcapUi : ∀ a ∈ U, (dg G W a : ℤ) ≤ 2 * (q : ℤ) - 2 := fun a ha => by
    have hd := hcapU a ha;omega
  have hdU := deficiency_eq (G := G) (2 * (q : ℤ) - 2) W U
  have hdW := deficiency_eq (G := G) (2 * (q : ℤ) - 2) U W
  have hd0 := deficiency_nonneg (G := G) (2 * (q : ℤ) - 2) hcapUi
  have hc := ec_comm (G := G) W U
  have hqZ : 5 ≤ (q : ℤ) := by exact_mod_cast hq
  zify at he horder hc
  rw [Bq.pred_cast hq] at he
  have hcases : #W = #U ∨ #W = #U + 1 := by
    have ht : (#W : ℤ) - #U < 2 := by
      by_contra! hbad
      have hp : 0 ≤ ((q : ℤ) - 1) * (((#W : ℤ) - #U) - 2) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
    omega
  rcases hcases with hbal | hsur
  · have hbalZ : (#W : ℤ) = #U := by exact_mod_cast hbal
    have hdq : deficiency (2 * (q : ℤ) - 2) G W U = q := by rw [hbalZ] at he;nlinarith
    have hdq' : deficiency (2 * (q : ℤ) - 2) G U W = q := by rw [hbalZ] at hdW;nlinarith
    exact ⟨U,W,Subset.refl U,Subset.refl W,hUW,by omega,
      Bq.balanced_factor hq hbal.symm hminU hcapU hminW hcapW hdq hdq' hs⟩
  · have hsurZ : (#W : ℤ) = #U + 1 := by exact_mod_cast hsur
    have hd1 : deficiency (2 * (q : ℤ) - 2) G W U = 1 := by rw [hsurZ] at he;nlinarith
    have hr : R2Input q G U W := ⟨hUW,hsur,hminU,hcapU,hminW,hcapW,hd1,hs⟩
    obtain ⟨w,hw,hf⟩ := r2_original (G := G) q hq U W hr
    have hwcard := card_erase_add_one hw
    exact ⟨U,W.erase w,Subset.refl U,erase_subset w W,hUW.mono (Subset.refl U) (erase_subset w W),by omega,hf⟩

theorem retained_factor {q : ℕ} {U W : Finset V} (hq : 5 ≤ q)
    (hUW : Disjoint U W) (hn : 2 * q ≤ #U + #W)
    (hminU : ∀ a ∈ U, q ≤ dg G W a) (hcapU : ∀ a ∈ U, dg G W a ≤ 2 * q - 2)
    (hminW : ∀ w ∈ W, q ≤ dg G U w) (hcapW : ∀ w ∈ W, dg G U w ≤ 2 * q - 2)
    (he : ec G U W + q = (q - 1) * (#U + #W)) (hs : Bq.Sparse q G U W) :
    ∃ A B : Finset V, A ⊆ U ∧ B ⊆ W ∧ Disjoint A B ∧
      #U + #W ≤ #A + #B + 1 ∧ FactorOn q G A B := by
  by_cases horder : #U ≤ #W
  · exact retained_factor_sorted hq hUW hn horder hminU hcapU hminW hcapW he hs
  · have he' : ec G W U + q = (q - 1) * (#W + #U) := by
      rw [ec_comm,add_comm (#W) (#U)];exact he
    obtain ⟨A,B,hA,hB,hAB,hcard,hf⟩ := retained_factor_sorted hq hUW.symm (by omega)
      (by omega) hminW hcapW hminU hcapU he' hs.swap
    exact ⟨B,A,hB,hA,hAB.symm,by omega,factor_swap hf⟩
end Erdos585.BqMinimumSupport
