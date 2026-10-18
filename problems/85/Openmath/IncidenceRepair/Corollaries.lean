import Openmath.IncidenceRepair.Main

noncomputable section
namespace Erdos85.IncidenceRepair
variable {K L : Type*} [Field K] [Field L] [Finite K] [Finite L] {n : ℕ}

/-- The unconditional dichotomy (1.3) from the published statement. -/
theorem repair_dichotomy (hn : 2 ≤ n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) :
    (∃ (σ : K →+* L) (A : Coordinates L n ≃ₗ[L] Coordinates L n)
      (Gh : Hyperplane K n → Hyperplane L n),
      Coupled σ A Gh ∧
      (repairDistance φ (pointEmbedding σ A) ψ Gh : ℝ) ≤
        10 * (brokenFlags φ ψ : ℝ) / (flagDegree K n : ℝ)) ∨
    frameSurvival φ ≤ 10^9 * (n : ℝ)^2 * errorDensity φ ψ := by
  by_cases h : frameSurvival φ ≤ 10^9 * (n : ℝ)^2 * errorDensity φ ψ
  · exact Or.inr h
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hden : (0 : ℝ) < 10^9 * (n : ℝ)^2 := by positivity
    have hδ := errorDensity_nonneg φ ψ
    have hρ : 0 < frameSurvival φ :=
      lt_of_le_of_lt (mul_nonneg (le_of_lt hden) hδ) (lt_of_not_ge h)
    have hsmall : errorDensity φ ψ ≤ frameSurvival φ / (10^9 * (n : ℝ)^2) := by
      apply (le_div_iff₀ hden).2
      nlinarith [lt_of_not_ge h]
    obtain ⟨σ, A, Gh, hc, hb, hd⟩ := projective_incidence_repair K L n hn φ ψ hρ hsmall
    exact Or.inl ⟨σ, A, Gh, hc, hb.trans hd⟩

/-- When no source-field embedding exists, the second alternative always holds. -/
theorem frameSurvival_bound_of_no_field_embedding (hn : 2 ≤ n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (hno : ¬ Nonempty (K →+* L)) :
    frameSurvival φ ≤ 10^9 * (n : ℝ)^2 * errorDensity φ ψ := by
  rcases repair_dichotomy hn φ ψ with ⟨σ, A, Gh, hc, hb⟩ | h
  · exact (hno ⟨σ⟩).elim
  · exact h

end Erdos85.IncidenceRepair
