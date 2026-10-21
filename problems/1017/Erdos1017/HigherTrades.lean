import Erdos1017.SubsetMoments
import Mathlib.Tactic.NormNum

/-! Signed four-, five-, and six-coordinate trades. These identities preserve
moments; nonnegativity after combining trades is a separate required theorem. -/
namespace Erdos1017
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def higherTrade (T : Finset ι) (S : Finset ι) : ℝ :=
  (((T.card : ℝ)-2)*((T.card : ℝ)-3)/6) * layerMass T 0 S -
  (((T.card : ℝ)-3)/((T.card : ℝ)-1)) * layerMass T 2 S +
  (2/((T.card : ℝ)-1)) * layerMass T 3 S - layerMass T T.card S

theorem higherTrade_moment_expansion (T B : Finset ι) :
    subsetMoment (higherTrade T) B =
      (((T.card : ℝ)-2)*((T.card : ℝ)-3)/6) * subsetMoment (layerMass T 0) B -
      (((T.card : ℝ)-3)/((T.card : ℝ)-1)) * subsetMoment (layerMass T 2) B +
      (2/((T.card : ℝ)-1)) * subsetMoment (layerMass T 3) B -
      subsetMoment (layerMass T T.card) B := by
  unfold higherTrade
  rw [subsetMoment_sub, subsetMoment_add, subsetMoment_sub,
    subsetMoment_mul, subsetMoment_mul, subsetMoment_mul]

/-- Total mass, every individual marginal, and every distinct pair marginal are unchanged. -/
theorem higherTrade_zero_moment (T B : Finset ι)
    (hk : T.card = 4 ∨ T.card = 5 ∨ T.card = 6) (hB : B.card ≤ 2) :
    subsetMoment (higherTrade T) B = 0 := by
  rw [higherTrade_moment_expansion]
  by_cases hBT : B ⊆ T
  · simp_rw [layer_moment_formula T B _ hBT]
    have hb : B.card = 0 ∨ B.card = 1 ∨ B.card = 2 := by omega
    rcases hk with hk | hk | hk <;> rcases hb with hb | hb | hb <;> norm_num [hk, hb, Nat.choose]
  · simp [layer_moment_zero_of_not_subset T B _ hBT]

theorem higherTrade_preserves_moments (w : Finset ι → ℝ) (T B : Finset ι) (t : ℝ)
    (hk : T.card = 4 ∨ T.card = 5 ∨ T.card = 6) (hB : B.card ≤ 2) :
    subsetMoment (fun S => w S + t * higherTrade T S) B = subsetMoment w B := by
  rw [subsetMoment_add, subsetMoment_mul, higherTrade_zero_moment T B hk hB]
  simp

noncomputable def tripleTrade (T : Finset ι) (S : Finset ι) : ℝ :=
  layerMass T 0 S - layerMass T 1 S + layerMass T 2 S - layerMass T 3 S

theorem tripleTrade_zero_moment (T B : Finset ι) (hk : T.card = 3) (hB : B.card ≤ 2) :
    subsetMoment (tripleTrade T) B = 0 := by
  unfold tripleTrade
  rw [subsetMoment_sub, subsetMoment_add, subsetMoment_sub]
  by_cases hBT : B ⊆ T
  · simp_rw [layer_moment_formula T B _ hBT]
    have hb : B.card = 0 ∨ B.card = 1 ∨ B.card = 2 := by omega
    rcases hb with hb | hb | hb <;> norm_num [hk, hb, Nat.choose]
  · simp [layer_moment_zero_of_not_subset T B _ hBT]

/-- The three-coordinate and larger-coordinate switches in one interface. -/
noncomputable def cliqueTrade (T : Finset ι) (S : Finset ι) : ℝ :=
  if T.card = 3 then tripleTrade T S else higherTrade T S

theorem cliqueTrade_preserves_moments (w : Finset ι → ℝ) (T B : Finset ι) (t : ℝ)
    (hk : 3 ≤ T.card ∧ T.card ≤ 6) (hB : B.card ≤ 2) :
    subsetMoment (fun S => w S + t * cliqueTrade T S) B = subsetMoment w B := by
  rw [subsetMoment_add, subsetMoment_mul]
  have hz : subsetMoment (cliqueTrade T) B = 0 := by
    by_cases h3 : T.card = 3
    · have ht : cliqueTrade T = tripleTrade T := by funext S; simp [cliqueTrade, h3]
      rw [ht]
      exact tripleTrade_zero_moment T B h3 hB
    · have h456 : T.card = 4 ∨ T.card = 5 ∨ T.card = 6 := by omega
      have ht : cliqueTrade T = higherTrade T := by funext S; simp [cliqueTrade, h3]
      rw [ht]
      exact higherTrade_zero_moment T B h456 hB
  rw [hz]
  simp

end Erdos1017
