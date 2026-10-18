import Openmath.IncidenceRepair.TargetBounds
import Openmath.IncidenceRepair.SourceNumerics

noncomputable section
namespace Erdos85.IncidenceRepair
variable {K L : Type*} [Field K] [Field L] [Finite K] [Finite L] {n : ℕ}

theorem pointCount_split : pointCount K n = Nat.card K ^ n + flagDegree K n := by
  unfold pointCount flagDegree
  simpa using source_degree_split (Nat.card K) (n+1) Finite.one_lt_card (by omega)

theorem affineCount_le_pointCount : Nat.card K ^ n ≤ pointCount K n := by
  rw [pointCount_split]
  omega

theorem flagDegree_pos (hn : 2 ≤ n) : 0 < flagDegree K n := by
  have hs := source_degree_split (Nat.card K) n Finite.one_lt_card (show 1 ≤ n by omega)
  have ha := source_gap_ge_two (Nat.card K) n Finite.one_lt_card hn
  unfold flagDegree
  rw [hs]
  exact lt_of_lt_of_le (show 0 < Nat.card K ^ (n-1) by omega) (Nat.le_add_right _ _)

theorem pointCount_pos (hn : 2 ≤ n) : 0 < pointCount K n := by
  rw [pointCount_split]
  have := flagDegree_pos (K := K) hn
  omega

theorem errorDensity_identity (hn : 2 ≤ n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) :
    errorDensity φ ψ * (pointCount K n : ℝ) * (flagDegree K n : ℝ) = brokenFlags φ ψ := by
  have hN : (pointCount K n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (pointCount_pos (K := K) hn))
  have hd : (flagDegree K n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (flagDegree_pos (K := K) hn))
  unfold errorDensity
  field_simp

theorem error_over_gap_bound (hn : 2 ≤ n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) :
    (brokenFlags φ ψ : ℝ) / (Nat.card K : ℝ)^(n-1) ≤
      2 * errorDensity φ ψ * (pointCount K n : ℝ) := by
  have ha : (2 : ℝ) ≤ (Nat.card K : ℝ)^(n-1) := by
    exact_mod_cast source_gap_ge_two (Nat.card K) n Finite.one_lt_card hn
  have hd : (flagDegree K n : ℝ) ≤ 2 * (Nat.card K : ℝ)^(n-1) := by
    exact_mod_cast source_degree_le_twice_gap (Nat.card K) n Finite.one_lt_card (show 1 ≤ n by omega)
  have hm := mul_le_mul_of_nonneg_left hd
    (mul_nonneg (errorDensity_nonneg φ ψ) (show (0 : ℝ) ≤ pointCount K n by positivity))
  have hi := errorDensity_identity hn φ ψ
  apply (div_le_iff₀ (show (0 : ℝ) < (Nat.card K : ℝ)^(n-1) by linarith)).2
  nlinarith

end Erdos85.IncidenceRepair
