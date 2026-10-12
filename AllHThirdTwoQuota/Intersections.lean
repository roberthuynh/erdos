import AllHThirdTwoQuota.Tiny

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHThirdTwoQuota
open QB4 B5 L34 H3Unequal
open AllHThirdFragileFree (Parameters offset constant)
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Data
variable {h q a₀ j : ℕ} {A B : Finset V} (d : Data h q a₀ j G A B)
include d

lemma scar_intersection_lower {T U : Finset V}
    (hT : T ⊆ B) (hTl : q - 1 ≤ #T) (hTp : 0 < thetaJ q j G A B T)
    (hU : U ⊆ B) (hUl : q - 1 ≤ #U) (hUp : 0 < thetaJ q j G A B U) :
    (q : ℤ) - a₀ - 4 * h ≤ deficiency (2 * (q : ℤ) - 2) G B
      (canonical q G A B T ∩ canonical q G A B U) := by
  have ht := d.outside_scar_le (strict_optimizer q A B T) hT hTl hTp
  have hu := d.outside_scar_le (strict_optimizer q A B U) hU hUl hUp
  have hst := d.scar_split (canonical_subset (G := G) q A B T)
  have hsu := d.scar_split (canonical_subset (G := G) q A B U)
  have hl := d.scar_le (union_subset (canonical_subset (G := G) q A B T)
    (canonical_subset (G := G) q A B U))
  have hi : deficiency (2 * (q : ℤ) - 2) G B
      (canonical q G A B T ∪ canonical q G A B U) +
      deficiency (2 * (q : ℤ) - 2) G B
      (canonical q G A B T ∩ canonical q G A B U) =
      deficiency (2 * (q : ℤ) - 2) G B (canonical q G A B T) +
      deficiency (2 * (q : ℤ) - 2) G B (canonical q G A B U) := sum_union_inter
  have hdelta := d.parameters.scar_lower
  omega

/-- The original shared-row convex gap excludes all tiny intersections at every height. -/
lemma large_intersection {T U : Finset V}
    (hT : T ⊆ B) (hTl : q - 1 ≤ #T) (hTp : 0 < thetaJ q j G A B T)
    (hU : U ⊆ B) (hUl : q - 1 ≤ #U) (hUp : 0 < thetaJ q j G A B U) :
    q - 1 ≤ #(T ∩ U) := by
  have hq := d.parameters.q_ge_height
  have hh := d.parameters.height_int
  have hj := d.parameters.j_bounds
  have hn := d.parameters.numeric
  have hcup := d.theta_large_le (union_subset hT hU)
    (hTl.trans (card_le_card subset_union_left))
  by_contra! hbad
  have hsmall : #(T ∩ U) ≤ q - 2 := by omega
  by_cases htiny : #(T ∩ U) < h
  · let M := canonical q G A B T ∩ canonical q G A B U
    have hscarlo := d.scar_intersection_lower hT hTl hTp hU hUl hUp
    change (q : ℤ) - a₀ - 4 * h ≤ deficiency (2 * (q : ℤ) - 2) G B M at hscarlo
    have hdeg : ∀ a ∈ M, 2 * (q : ℤ) - 5 * h ≤ dg G B a := by
      intro a ha
      obtain ⟨hat, hau⟩ := mem_inter.mp ha
      have hdt := d.optimizer_internal_min_coarse (strict_optimizer q A B T) hT hTl hTp hat
      have hdu := d.optimizer_internal_min_coarse (strict_optimizer q A B U) hU hUl hUp hau
      have hid := dg_union_add_dg_inter (G := G) T U a
      have hd := dg_mono (G := G) (union_subset hT hU) a
      have hdi := dg_le_card (G := G) (T ∩ U) a
      omega
    have hscarhi : deficiency (2 * (q : ℤ) - 2) G B M ≤ 5 * (h : ℤ) * #M := by
      calc
        _ ≤ ∑ _a ∈ M, (5 * (h : ℤ)) := by
          apply sum_le_sum
          intro a ha
          have hd := hdeg a ha
          omega
        _ = _ := by simp [mul_comm]
    have hmany : 10 * (h : ℤ) ≤ #M := by
      by_contra! hbadM
      have hm : 0 ≤ (h : ℤ) * (10 * h - (#M : ℤ)) := mul_nonneg (by omega) (by omega)
      nlinarith
    have hgap : ((#M : ℤ) * ((q : ℤ) - 6 * h)) ≤
        ∑ a ∈ M, max 0 (((dg G B a : ℤ) - q) - dg G (T ∩ U) a) := by
      calc
        _ = ∑ _a ∈ M, ((q : ℤ) - 6 * h) := by simp only [sum_const, nsmul_eq_mul]
        _ ≤ _ := by
          apply sum_le_sum
          intro a ha
          have hd := hdeg a ha
          have hdi := dg_le_card (G := G) (T ∩ U) a
          omega
    have hbudget := intersection_budget (G := G) q A B T U
    have hit := d.theta_tiny_le htiny
    have hbudgetJ : (∑ a ∈ M, max 0 (((dg G B a : ℤ) - q) - dg G (T ∩ U) a)) ≤
        thetaJ q j G A B (T ∪ U) + thetaJ q j G A B (T ∩ U) -
          thetaJ q j G A B T - thetaJ q j G A B U := by
      unfold thetaJ
      change (∑ a ∈ M, max 0 (((dg G B a : ℤ) - q) - dg G (T ∩ U) a)) ≤ _ at hbudget
      linarith
    have hqj : (q : ℤ) * j ≤ (q : ℤ) * h := by
      nlinarith [mul_nonneg (Nat.cast_nonneg q : (0 : ℤ) ≤ q)
        (show 0 ≤ (h : ℤ) - j by omega)]
    have h10 : 10 * (h : ℤ) ≤ q := by nlinarith [sq_nonneg (h : ℤ)]
    have hproduct : 0 ≤ ((q : ℤ) - 6 * h) * ((#M : ℤ) - 10 * h) :=
      mul_nonneg (by omega) (by omega)
    have hqh : 0 ≤ (h : ℤ) * ((q : ℤ) - 10 * h) := mul_nonneg (by omega) (by omega)
    nlinarith
  · have hinter := d.theta_intermediate (by omega) hsmall
    have hsuper := H3Unequal.Input.theta_supermod (G := G) q j A B T U
    omega

end Data
end Erdos585.AllHThirdTwoQuota
