import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
Finite counting and averaging behind §5 of the projective-incidence repair proof.
This module does not assert the projective slot counts; it proves the selection
step from explicitly stated cardinality and total-cost bounds.
-/

open scoped BigOperators

namespace Erdos85.IncidenceRepair

/-- A surviving frame outside the failed-certificate set has low cost whenever
its total budget is smaller than the cost of excluding every survivor. -/
theorem exists_surviving_good_of_budget
    {F : Type*} [Fintype F] [DecidableEq F]
    (surviving failed : Finset F) (cost : F → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hcost : ∀ f, 0 ≤ cost f)
    (hbudget : ε * (failed.card : ℝ) + ∑ f, cost f <
      ε * (surviving.card : ℝ)) :
    ∃ f ∈ surviving, f ∉ failed ∧ cost f ≤ ε := by
  classical
  by_contra h
  have hpoint : ∀ f : F,
      (if f ∈ surviving then ε else 0) ≤
        (if f ∈ failed then ε else 0) + cost f := by
    intro f
    by_cases hs : f ∈ surviving
    · by_cases hb : f ∈ failed
      · simp only [hs, hb, if_true]
        linarith [hcost f]
      · have hc : ε < cost f := by
          by_contra hn
          exact h ⟨f, hs, hb, le_of_not_gt hn⟩
        simp only [hs, hb, if_true, if_false, zero_add]
        exact hc.le
    · simp only [hs, if_false]
      split_ifs <;> linarith [hcost f]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun f _ => hpoint f)
  simp only [Finset.sum_add_distrib] at hs
  have hsum (s : Finset F) :
      (∑ f : F, if f ∈ s then ε else 0) = ε * (s.card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  rw [hsum surviving, hsum failed] at hs
  linarith

/-- The exact constants used in §5. Here x is n²δ times the number of all
frames, so every assumption is an unnormalized finite counting bound. -/
theorem exists_surviving_good_unnormalized
    {F : Type*} [Fintype F] [DecidableEq F]
    (surviving failed : Finset F) (cost : F → ℝ) (x : ℝ)
    (hsurviving : 0 < (surviving.card : ℝ))
    (hcost : ∀ f, 0 ≤ cost f)
    (hfailed : (failed.card : ℝ) ≤ 7 * x)
    (htotal : ∑ f, cost f ≤ 48 * x)
    (hsmall : 1000000000 * x ≤ (surviving.card : ℝ)) :
    ∃ f ∈ surviving, f ∉ failed ∧ cost f ≤ (1 : ℝ) / 10000000 := by
  apply exists_surviving_good_of_budget surviving failed cost (1 / 10000000)
  · positivity
  · exact hcost
  · nlinarith

/-- Normalized form of §5: survival is counted among all frames, before
conditioning, and both certificate failures and cost are bounded on all frames. -/
theorem exists_surviving_good_normalized
    {F : Type*} [Fintype F] [DecidableEq F] [Nonempty F]
    (surviving failed : Finset F) (cost : F → ℝ) (n : ℕ) (ρ δ : ℝ)
    (hn : 2 ≤ n)
    (hρ : ρ = (surviving.card : ℝ) / (Fintype.card F : ℝ))
    (hρpos : 0 < ρ) (hcost : ∀ f, 0 ≤ cost f)
    (hfailed : (failed.card : ℝ) / (Fintype.card F : ℝ) ≤ 7 * (n : ℝ)^2 * δ)
    (htotal : (∑ f, cost f) / (Fintype.card F : ℝ) ≤ 48 * (n : ℝ)^2 * δ)
    (hsmall : δ ≤ ρ / (1000000000 * (n : ℝ)^2)) :
    ∃ f ∈ surviving, f ∉ failed ∧ cost f ≤ (1 : ℝ) / 10000000 := by
  have hF : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hden : (0 : ℝ) < 1000000000 * (n : ℝ)^2 := by positivity
  have hρmul : ρ * (Fintype.card F : ℝ) = (surviving.card : ℝ) := by
    rw [hρ, div_mul_cancel₀ _ hF.ne']
  apply exists_surviving_good_unnormalized surviving failed cost
    ((n : ℝ)^2 * δ * (Fintype.card F : ℝ))
  · rw [← hρmul]
    positivity
  · exact hcost
  · have hb := (div_le_iff₀ hF).mp hfailed
    nlinarith
  · have ht := (div_le_iff₀ hF).mp htotal
    nlinarith
  · have he := (le_div_iff₀ hden).mp hsmall
    have hm := mul_le_mul_of_nonneg_right he hF.le
    rw [hρmul] at hm
    nlinarith

/-- An equally repeated original-flag slot has the exact unconditioned sum.
No assertion about conditioning on surviving frames is used. -/
theorem sum_slot_of_equal_multiplicity
    {F I : Type*} [Fintype F] [Fintype I] [DecidableEq I]
    (slot : F → I) (error : I → ℝ) (k : ℕ)
    (hmult : ∀ i, (Finset.univ.filter (fun f => slot f = i)).card = k) :
    (∑ f, error (slot f)) = (k : ℝ) * ∑ i, error i := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ slot (fun f => error (slot f))]
  calc
    (∑ i, ∑ f ∈ Finset.univ.filter (fun f => slot f = i), error (slot f)) =
        ∑ i, (k : ℝ) * error i := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ f ∈ Finset.univ.filter (fun f => slot f = i), error (slot f)) =
            ∑ _f ∈ Finset.univ.filter (fun f => slot f = i), error i := by
          apply Finset.sum_congr rfl
          intro f hf
          rw [(Finset.mem_filter.mp hf).2]
        _ = (k : ℝ) * error i := by simp [hmult]
    _ = (k : ℝ) * ∑ i, error i := by rw [Finset.mul_sum]

/-- The corresponding exact expectation formula, with denominators explicitly
the cardinalities of the complete source and target spaces. -/
theorem average_slot_of_equal_multiplicity
    {F I : Type*} [Fintype F] [Fintype I] [DecidableEq I]
    [Nonempty F] [Nonempty I]
    (slot : F → I) (error : I → ℝ) (k : ℕ)
    (hmult : ∀ i, (Finset.univ.filter (fun f => slot f = i)).card = k) :
    (∑ f, error (slot f)) / (Fintype.card F : ℝ) =
      (∑ i, error i) / (Fintype.card I : ℝ) := by
  have hcount := sum_slot_of_equal_multiplicity slot (fun _ => (1 : ℝ)) k hmult
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcount
  have hF : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hI : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  rw [sum_slot_of_equal_multiplicity slot error k hmult]
  apply (div_eq_div_iff hF.ne' hI.ne').mpr
  rw [hcount]
  ring

end Erdos85.IncidenceRepair
