import L34.Selector

/-! Both actual shore signatures and every small-order floor. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.L34
open QB4 B5
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma constant_cast {q : ℕ} (hq : 6 ≤ q) :
    ((2 * q - 5 : ℕ) : ℤ) = 2 * (q : ℤ) - 5 := by omega

lemma boundary_order {q : ℕ} {U W : Finset V} (hq : 6 ≤ q)
    (hn : 2 * q ≤ #U + #W)
    (he : (q - 1) * (#U + #W) ≤ ec G U W + (2 * q - 5)) :
    2 * q + 1 ≤ #U + #W := by
  by_contra! hsmall
  have hsize : #U + #W = 2 * q := by omega
  have hp := ec_le_product (G := G) U W
  have hqZ : 6 ≤ (q : ℤ) := by exact_mod_cast hq
  have hs := sq_nonneg ((#U : ℤ) - #W)
  have hsq := sq_nonneg ((q : ℤ) - 2)
  zify at he hp hsize
  rw [Bq.pred_cast (by omega), constant_cast hq] at he
  nlinarith

lemma small_potential {q : ℕ} {X Y : Finset V} (hq : 6 ≤ q)
    (hn : 3 ≤ #X + #Y) (hsmall : #X + #Y ≤ 2 * q - 1) :
    4 * (q : ℤ) - 8 ≤ potential (2 * (q : ℤ) - 2) G X Y := by
  have hp := ec_le_product (G := G) X Y
  have hqZ : 6 ≤ (q : ℤ) := by exact_mod_cast hq
  zify at hn hsmall hp
  have hs := sq_nonneg ((#X : ℤ) - #Y)
  have hi : (((#X : ℤ) + #Y) - 3) *
      (((#X : ℤ) + #Y) - (2 * (q : ℤ) - 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
  have hj : 0 ≤ ((q : ℤ) - 3) * (((#X : ℤ) + #Y) - 3) :=
    mul_nonneg (by omega) (by omega)
  unfold potential
  nlinarith

/-- Derive j=0/1, the entire scar and all selection inputs internally. -/
theorem critical_sorted {q : ℕ} {U W : Finset V} (hq : 6 ≤ q)
    (hUW : Disjoint U W) (hn : 2 * q ≤ #U + #W) (horder : #U ≤ #W)
    (hminU : ∀ a ∈ U, q ≤ dg G W a) (hcapU : ∀ a ∈ U, dg G W a ≤ 2 * q - 2)
    (hminW : ∀ w ∈ W, q ≤ dg G U w) (hcapW : ∀ w ∈ W, dg G U w ≤ 2 * q - 2)
    (he : ec G U W + (2 * q - 5) = (q - 1) * (#U + #W))
    (hs : Sparse q G U W) : RegularPairs q G U W := by
  have hcapUi : ∀ a ∈ U, (dg G W a : ℤ) ≤ 2 * (q : ℤ) - 2 := fun a ha => by
    have hd := hcapU a ha
    omega
  have hdU := deficiency_eq (G := G) (2 * (q : ℤ) - 2) W U
  have hd0 := deficiency_nonneg (G := G) (2 * (q : ℤ) - 2) hcapUi
  have hqZ : 6 ≤ (q : ℤ) := by exact_mod_cast hq
  zify at he horder hn
  rw [Bq.pred_cast (by omega), constant_cast hq] at he
  have hcases : #W = #U ∨ #W = #U + 1 := by
    have ht : (#W : ℤ) - #U < 2 := by
      by_contra! hbad
      have hp : 0 ≤ ((q : ℤ) - 1) * (((#W : ℤ) - #U) - 2) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
    omega
  have hUne : U.Nonempty := by
    by_contra! hnU
    have hu : #U = 0 := card_eq_zero.mpr hnU
    rcases hcases with hh | hh
    · omega
    · omega
  rcases hcases with hbal | hsur
  · have hbalZ : (#W : ℤ) = #U := by exact_mod_cast hbal
    have hd : deficiency (2 * (q : ℤ) - 2) G W U = 2 * (q : ℤ) - 5 := by
      rw [hbalZ] at he
      nlinarith
    have h : Input q 0 G U W :=
      ⟨by omega, by simpa using hbal, hminU, hcapU, hminW, hcapW, by simpa using hd, hs⟩
    exact (h.balanced_factor hq).regular_pairs (by omega) hUne
  · have hsurZ : (#W : ℤ) = #U + 1 := by exact_mod_cast hsur
    have hd : deficiency (2 * (q : ℤ) - 2) G W U = (q : ℤ) - 4 := by
      rw [hsurZ] at he
      nlinarith
    have h : Input q 1 G U W :=
      ⟨by omega, hsur, hminU, hcapU, hminW, hcapW, by norm_num; linarith, hs⟩
    obtain ⟨w, hw, hf⟩ := h.surplus_factor hq
    exact hf.regular_pairs (by omega) hUne |>.mono_sets (Subset.refl U) (erase_subset w W)

theorem critical_pair {q : ℕ} {U W : Finset V} (hq : 6 ≤ q)
    (hUW : Disjoint U W) (hn : 2 * q ≤ #U + #W)
    (hminU : ∀ a ∈ U, q ≤ dg G W a) (hcapU : ∀ a ∈ U, dg G W a ≤ 2 * q - 2)
    (hminW : ∀ w ∈ W, q ≤ dg G U w) (hcapW : ∀ w ∈ W, dg G U w ≤ 2 * q - 2)
    (he : ec G U W + (2 * q - 5) = (q - 1) * (#U + #W))
    (hs : Sparse q G U W) : RegularPairs q G U W := by
  by_cases horder : #U ≤ #W
  · exact critical_sorted hq hUW hn horder hminU hcapU hminW hcapW he hs
  · have hn' : 2 * q ≤ #W + #U := by omega
    have he' : ec G W U + (2 * q - 5) = (q - 1) * (#W + #U) := by
      rw [ec_comm, add_comm (#W) (#U)]
      exact he
    exact (critical_sorted hq hUW.symm hn' (by omega) hminW hcapW hminU hcapU
      he' hs.swap).swap

end Erdos585.L34
