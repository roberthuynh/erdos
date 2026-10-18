import Openmath.IncidenceRepair.Target

noncomputable section
namespace Erdos85.IncidenceRepair
variable {K L : Type*} [Field K] [Field L] [Finite K] [Finite L] {n : ℕ}

theorem frameSurvival_nonneg (φ : Point K n → Point L n) :
    0 ≤ frameSurvival φ := by unfold frameSurvival; positivity

theorem frameSurvival_le_one (φ : Point K n → Point L n) :
    frameSurvival φ ≤ 1 := by
  have hcard : Nat.card {F : Frame K n // IsFrame (φ ∘ F.1)} ≤ Nat.card (Frame K n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  unfold frameSurvival
  by_cases hzero : Nat.card (Frame K n) = 0
  · simp [hzero]
  · have hpos : (0 : ℝ) < Nat.card (Frame K n) := by exact_mod_cast Nat.pos_of_ne_zero hzero
    apply (div_le_one hpos).2
    exact_mod_cast hcard

theorem errorDensity_nonneg (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) : 0 ≤ errorDensity φ ψ := by
  unfold errorDensity
  positivity

theorem errorDensity_le_numeric_threshold (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) (hn : 2 ≤ n)
    (hsmall : errorDensity φ ψ ≤ frameSurvival φ / (10^9 * (n : ℝ)^2)) :
    errorDensity φ ψ ≤ 1 / 4000000000 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0 : ℝ) < 10^9 * (n : ℝ)^2 := by positivity
  have hsurv := frameSurvival_le_one φ
  have hmul := (le_div_iff₀ hden).1 hsmall
  have hdelta := errorDensity_nonneg φ ψ
  have hprod := mul_nonneg hdelta (show 0 ≤ (n : ℝ)^2 - 4 by nlinarith)
  nlinarith

end Erdos85.IncidenceRepair
