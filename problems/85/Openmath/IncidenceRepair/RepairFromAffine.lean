import Openmath.IncidenceRepair.ProjectiveCoarseRepair
import Openmath.IncidenceRepair.ProjectiveLocalRepair

noncomputable section
namespace Erdos85.IncidenceRepair

/-- Actual global affine agreement and the protected infinity hyperplane imply
the complete paired repair estimate. The global construction is separate. -/
theorem repair_from_affine
    {K L : Type*} [Field K] [Field L] [Finite K] [Finite L] {n : ℕ}
    (hn : 2 ≤ n) (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (hInfinity : ψ infinityHyperplane = hyperplaneEmbedding σ A infinityHyperplane)
    (hZ : (affineErrors φ σ A : ℝ) ≤
      (971 : ℝ) / 10000000 * (Nat.card K : ℝ)^n)
    (hδ : errorDensity φ ψ ≤ 1 / 4000000000) :
    (repairDistance φ (pointEmbedding σ A) ψ (hyperplaneEmbedding σ A) : ℝ) ≤
      5 * (brokenFlags φ ψ : ℝ) / (Nat.card K : ℝ)^(n-1) ∧
    5 * (brokenFlags φ ψ : ℝ) / (Nat.card K : ℝ)^(n-1) ≤
      10 * (brokenFlags φ ψ : ℝ) / (flagDegree K n : ℝ) := by
  have hcard : (Nat.card K : ℝ)^n ≤ (pointCount K n : ℝ) := by
    exact_mod_cast affineCount_le_pointCount (K := K) (n := n)
  have hZ' : (affineErrors φ σ A : ℝ) ≤
      (971 : ℝ) / 10000000 * (pointCount K n : ℝ) :=
    hZ.trans (mul_le_mul_of_nonneg_left hcard (by norm_num))
  have hc := projective_coarse_repair hn σ A φ ψ hInfinity hZ' hδ
  exact projective_local_repair hn σ A φ ψ hc.2

end Erdos85.IncidenceRepair
