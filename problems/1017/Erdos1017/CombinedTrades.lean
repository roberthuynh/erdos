import Erdos1017.HigherTrades
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Simultaneous clique trades with explicit singleton and pair budgets.
The budgets are hypotheses here; the analytic bounds supplying them are separate. -/
namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def tradeSupport : Finset (Finset ι) :=
  Finset.univ.filter (fun T => 3 ≤ T.card ∧ T.card ≤ 6)

noncomputable def tripleDeposit (t : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ T ∈ (tradeSupport : Finset (Finset ι)),
    if T.card = 3 ∧ S ⊆ T then t T else 0

noncomputable def pairWithdrawal (t : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ T ∈ (tradeSupport : Finset (Finset ι)),
    if T.card ≠ 3 ∧ S ⊆ T then ((T.card : ℝ)-3)/((T.card : ℝ)-1) * t T else 0

noncomputable def combinedTrade (w t : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  w S + ∑ T ∈ (tradeSupport : Finset (Finset ι)), t T * cliqueTrade T S

theorem mem_tradeSupport (T : Finset ι) :
    T ∈ (tradeSupport : Finset (Finset ι)) ↔ 3 ≤ T.card ∧ T.card ≤ 6 := by
  simp [tradeSupport]

theorem layerMass_top (T S : Finset ι) :
    layerMass T T.card S = if S = T then 1 else 0 := by
  have h : S ⊆ T ∧ S.card = T.card ↔ S = T := by
    constructor
    · intro h
      exact Finset.eq_of_subset_of_card_le h.1 h.2.ge
    · rintro rfl
      exact ⟨Finset.Subset.refl _, rfl⟩
  simp only [layerMass, Finset.mem_powersetCard, h]

theorem cliqueTrade_empty_nonneg (T : Finset ι)
    (hk : 3 ≤ T.card ∧ T.card ≤ 6) : 0 ≤ cliqueTrade T ∅ := by
  have hc : T.card = 3 ∨ T.card = 4 ∨ T.card = 5 ∨ T.card = 6 := by omega
  rcases hc with hc | hc | hc | hc <;>
    norm_num [cliqueTrade, tripleTrade, higherTrade, layerMass, Finset.mem_powersetCard, hc]

theorem cliqueTrade_singleton_formula (T S : Finset ι)
    (hk : 3 ≤ T.card ∧ T.card ≤ 6) (hs : S.card = 1) :
    cliqueTrade T S = if T.card = 3 ∧ S ⊆ T then -1 else 0 := by
  have hne : S ≠ ∅ := by intro h; simp [h] at hs
  have hc : T.card = 3 ∨ T.card = 4 ∨ T.card = 5 ∨ T.card = 6 := by omega
  rcases hc with hc | hc | hc | hc <;> by_cases hst : S ⊆ T <;>
    norm_num [cliqueTrade, tripleTrade, higherTrade, layerMass, Finset.mem_powersetCard, hc, hs, hst, hne]

theorem cliqueTrade_pair_formula (T S : Finset ι)
    (hk : 3 ≤ T.card ∧ T.card ≤ 6) (hs : S.card = 2) :
    cliqueTrade T S = (if T.card = 3 ∧ S ⊆ T then 1 else 0) -
      (if T.card ≠ 3 ∧ S ⊆ T then ((T.card : ℝ)-3)/((T.card : ℝ)-1) else 0) := by
  have hne : S ≠ ∅ := by intro h; simp [h] at hs
  have hc : T.card = 3 ∨ T.card = 4 ∨ T.card = 5 ∨ T.card = 6 := by omega
  rcases hc with hc | hc | hc | hc <;> by_cases hst : S ⊆ T <;>
    norm_num [cliqueTrade, tripleTrade, higherTrade, layerMass, Finset.mem_powersetCard, hc, hs, hst, hne]

theorem cliqueTrade_large_lower (T S : Finset ι)
    (hk : 3 ≤ T.card ∧ T.card ≤ 6) (hs : 3 ≤ S.card) :
    -(if S = T then (1 : ℝ) else 0) ≤ cliqueTrade T S := by
  have h0 : S.card ≠ 0 := by omega
  have h1 : S.card ≠ 1 := by omega
  have h2 : S.card ≠ 2 := by omega
  have hne : S ≠ ∅ := by intro h; simp [h] at hs
  have hzero : layerMass T 0 S = 0 := by simp [layerMass, hne]
  have hone : layerMass T 1 S = 0 := by simp [layerMass, Finset.mem_powersetCard, h1]
  have htwo : layerMass T 2 S = 0 := by simp [layerMass, Finset.mem_powersetCard, h2]
  have hc : T.card = 3 ∨ T.card = 4 ∨ T.card = 5 ∨ T.card = 6 := by omega
  rcases hc with hc | hc | hc | hc
  · have ht : layerMass T 3 S = if S = T then 1 else 0 := by
      simpa [hc] using layerMass_top T S
    simp only [cliqueTrade, hc, if_pos rfl, tripleTrade]
    rw [hzero, hone, htwo, ht]
    simp
  all_goals
    have ht := layerMass_top T S
    have hnn : 0 ≤ layerMass T 3 S := by unfold layerMass; split_ifs <;> norm_num
    simp only [cliqueTrade, hc, show (4 : ℕ) ≠ 3 by omega,
      show (5 : ℕ) ≠ 3 by omega, show (6 : ℕ) ≠ 3 by omega, if_false, higherTrade]
    simp only [hc] at ht
    rw [ht]
    rw [hzero, htwo]
    norm_num
    linarith

theorem cliqueTrade_outside (T S : Finset ι)
    (hk : 3 ≤ T.card ∧ T.card ≤ 6) (hs : 6 < S.card) : cliqueTrade T S = 0 := by
  have hst : ¬S ⊆ T := by
    intro h
    have := Finset.card_le_card h
    omega
  have hne : S ≠ ∅ := by intro h; simp [h] at hs
  have hneT : S ≠ T := by intro h; subst S; exact hst (Finset.Subset.refl _)
  simp [cliqueTrade, tripleTrade, higherTrade, layerMass, Finset.mem_powersetCard, hst, hne, hneT]

theorem combinedTrade_singleton (w t : Finset ι → ℝ) (S : Finset ι) (hs : S.card = 1) :
    combinedTrade w t S = w S - tripleDeposit t S := by
  unfold combinedTrade tripleDeposit
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  rw [cliqueTrade_singleton_formula T S ((mem_tradeSupport T).mp hT) hs]
  split_ifs <;> ring

theorem combinedTrade_pair (w t : Finset ι → ℝ) (S : Finset ι) (hs : S.card = 2) :
    combinedTrade w t S = w S + tripleDeposit t S - pairWithdrawal t S := by
  unfold combinedTrade tripleDeposit pairWithdrawal
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  rw [cliqueTrade_pair_formula T S ((mem_tradeSupport T).mp hT) hs]
  split_ifs <;> ring

/-- Every exact subset cell remains nonnegative. The pair budget includes all
four-, five-, and six-coordinate withdrawals together. -/
theorem combinedTrade_nonneg (w t : Finset ι → ℝ)
    (hw : ∀ S, 0 ≤ w S) (ht : ∀ T, 0 ≤ t T)
    (hcap : ∀ T, 3 ≤ T.card ∧ T.card ≤ 6 → t T ≤ w T)
    (hsingle : ∀ S, S.card = 1 → tripleDeposit t S ≤ w S)
    (hpair : ∀ S, S.card = 2 → pairWithdrawal t S ≤ w S + tripleDeposit t S)
    (S : Finset ι) : 0 ≤ combinedTrade w t S := by
  by_cases h0 : S.card = 0
  · have hz : S = ∅ := Finset.card_eq_zero.mp h0
    subst S
    apply add_nonneg (hw _)
    exact Finset.sum_nonneg (fun T hT => mul_nonneg (ht T)
      (cliqueTrade_empty_nonneg T ((mem_tradeSupport T).mp hT)))
  by_cases h1 : S.card = 1
  · rw [combinedTrade_singleton w t S h1]
    exact sub_nonneg.mpr (hsingle S h1)
  by_cases h2 : S.card = 2
  · rw [combinedTrade_pair w t S h2]
    exact sub_nonneg.mpr (hpair S h2)
  have h3 : 3 ≤ S.card := by omega
  by_cases h6 : S.card ≤ 6
  · have hS : S ∈ (tradeSupport : Finset (Finset ι)) := (mem_tradeSupport S).mpr ⟨h3, h6⟩
    have hsum : -t S ≤ ∑ T ∈ (tradeSupport : Finset (Finset ι)), t T * cliqueTrade T S := by
      calc
        -t S = ∑ T ∈ (tradeSupport : Finset (Finset ι)), -(if T = S then t S else 0) := by simp [hS]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro T hT
          have h := mul_le_mul_of_nonneg_left (cliqueTrade_large_lower T S ((mem_tradeSupport T).mp hT) h3) (ht T)
          by_cases hst : S = T
          · subst T
            simpa using h
          · simpa [hst, Ne.symm hst] using h
    unfold combinedTrade
    have := hcap S ⟨h3, h6⟩
    linarith
  · have hlarge : 6 < S.card := by omega
    have hz : ∀ T ∈ (tradeSupport : Finset (Finset ι)), t T * cliqueTrade T S = 0 := by
      intro T hT
      rw [cliqueTrade_outside T S ((mem_tradeSupport T).mp hT) hlarge, mul_zero]
    simpa only [combinedTrade, Finset.sum_eq_zero hz, add_zero] using hw S

theorem subsetMoment_finset_sum {α : Type*} (A : Finset α)
    (z : α → Finset ι → ℝ) (B : Finset ι) :
    subsetMoment (fun S => ∑ a ∈ A, z a S) B = ∑ a ∈ A, subsetMoment (z a) B := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [subsetMoment]
  | @insert a A ha ih =>
    simp only [Finset.sum_insert ha]
    rw [subsetMoment_add, ih]

theorem combinedTrade_preserves_moments (w t : Finset ι → ℝ) (B : Finset ι)
    (hB : B.card ≤ 2) : subsetMoment (combinedTrade w t) B = subsetMoment w B := by
  unfold combinedTrade
  rw [subsetMoment_add, subsetMoment_finset_sum]
  have hz : ∀ T ∈ (tradeSupport : Finset (Finset ι)),
      subsetMoment (fun S => t T * cliqueTrade T S) B = 0 := by
    intro T hT
    have h := cliqueTrade_preserves_moments (fun _ => 0) T B (t T) ((mem_tradeSupport T).mp hT) hB
    simpa [subsetMoment] using h
  rw [Finset.sum_eq_zero hz, add_zero]

/-- A single certificate for feasibility and all moments of order at most two. -/
theorem combinedTrade_certificate (w t : Finset ι → ℝ)
    (hw : ∀ S, 0 ≤ w S) (ht : ∀ T, 0 ≤ t T)
    (hcap : ∀ T, 3 ≤ T.card ∧ T.card ≤ 6 → t T ≤ w T)
    (hsingle : ∀ S, S.card = 1 → tripleDeposit t S ≤ w S)
    (hpair : ∀ S, S.card = 2 → pairWithdrawal t S ≤ w S + tripleDeposit t S) :
    (∀ S, 0 ≤ combinedTrade w t S) ∧
    (∀ B, B.card ≤ 2 → subsetMoment (combinedTrade w t) B = subsetMoment w B) :=
  ⟨combinedTrade_nonneg w t hw ht hcap hsingle hpair, combinedTrade_preserves_moments w t⟩

noncomputable def emptyBonus (t : Finset ι → ℝ) : ℝ :=
  ∑ T ∈ (tradeSupport : Finset (Finset ι)),
    (if T.card = 3 then 1 else ((T.card : ℝ)-2)*((T.card : ℝ)-3)/6) * t T

theorem combinedTrade_empty (w t : Finset ι → ℝ) :
    combinedTrade w t ∅ = w ∅ + emptyBonus t := by
  unfold combinedTrade emptyBonus
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  have hk := (mem_tradeSupport T).mp hT
  have hc : T.card = 3 ∨ T.card = 4 ∨ T.card = 5 ∨ T.card = 6 := by omega
  rcases hc with hc | hc | hc | hc <;>
    norm_num [cliqueTrade, tripleTrade, higherTrade, layerMass, Finset.mem_powersetCard, hc] <;> ring

theorem combinedTrade_total (w t : Finset ι → ℝ) :
    (∑ S, combinedTrade w t S) = ∑ S, w S := by
  simpa [subsetMoment] using combinedTrade_preserves_moments w t ∅ (by simp)

theorem combinedTrade_nonempty_cost (w t : Finset ι → ℝ) :
    (∑ S : Finset ι, if S.Nonempty then combinedTrade w t S else 0) =
      (∑ S, w S) - w ∅ - emptyBonus t := by
  have heq (S : Finset ι) :
      combinedTrade w t S = (if S.Nonempty then combinedTrade w t S else 0) +
        (if S = ∅ then combinedTrade w t ∅ else 0) := by
    by_cases h : S = ∅
    · simp [h]
    · simp [Finset.nonempty_iff_ne_empty.mpr h, h]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Finset ι))) rfl (fun S _ => heq S)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  rw [combinedTrade_total, combinedTrade_empty] at hsum
  linarith

/-- The complete finite-cell accounting interface: nonnegative masses, exact
low-order moments, and the precise reduction in mass outside the empty cell. -/
theorem combinedTrade_selector_certificate (w t : Finset ι → ℝ)
    (hw : ∀ S, 0 ≤ w S) (ht : ∀ T, 0 ≤ t T)
    (hcap : ∀ T, 3 ≤ T.card ∧ T.card ≤ 6 → t T ≤ w T)
    (hsingle : ∀ S, S.card = 1 → tripleDeposit t S ≤ w S)
    (hpair : ∀ S, S.card = 2 → pairWithdrawal t S ≤ w S + tripleDeposit t S) :
    (∀ S, 0 ≤ combinedTrade w t S) ∧
    (∀ B, B.card ≤ 2 → subsetMoment (combinedTrade w t) B = subsetMoment w B) ∧
    ((∑ S : Finset ι, if S.Nonempty then combinedTrade w t S else 0) =
      (∑ S, w S) - w ∅ - emptyBonus t) :=
  ⟨combinedTrade_nonneg w t hw ht hcap hsingle hpair,
    combinedTrade_preserves_moments w t, combinedTrade_nonempty_cost w t⟩

end Erdos1017
