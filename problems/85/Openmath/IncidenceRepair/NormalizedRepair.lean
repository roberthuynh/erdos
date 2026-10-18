import Openmath.IncidenceRepair.SelectedFrameCosts
import Openmath.IncidenceRepair.RepairFromAffine
import Openmath.IncidenceRepair.NormalizationUndo
import Openmath.IncidenceRepair.TargetBounds

noncomputable section
namespace Erdos85.IncidenceRepair

/-- The selected actual frame produces the full paired repair estimate in
normalized coordinates, with no affine reconstruction assumption. -/
theorem exists_normalized_repair
    {K L : Type*} [Field K] [Field L] [Fintype K] [Finite L] {n : ℕ}
    (hn : 2 ≤ n) (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n)
    (hρ : 0 < frameSurvival φ)
    (hsmall : errorDensity φ ψ ≤ frameSurvival φ / (1000000000 * (n : ℝ)^2)) :
    ∃ (F : Frame K n) (hf : IsFrame (φ ∘ F.1)) (σ : K →+* L),
      (repairDistance (normalizedPoints φ F hf)
        (pointEmbedding σ (LinearEquiv.refl L (Coordinates L n)))
        (normalizedHyperplanes φ ψ F hf)
        (hyperplaneEmbedding σ (LinearEquiv.refl L (Coordinates L n))) : ℝ) ≤
        5 * (brokenFlags (normalizedPoints φ F hf)
          (normalizedHyperplanes φ ψ F hf) : ℝ) / (Nat.card K : ℝ)^(n-1) ∧
      5 * (brokenFlags (normalizedPoints φ F hf)
          (normalizedHyperplanes φ ψ F hf) : ℝ) / (Nat.card K : ℝ)^(n-1) ≤
        10 * (brokenFlags (normalizedPoints φ F hf)
          (normalizedHyperplanes φ ψ F hf) : ℝ) / (flagDegree K n : ℝ) := by
  classical
  obtain ⟨F, hf, hcoord, hone, hprotected, hcost⟩ :=
    exists_normalized_protected_frame hn φ ψ hρ hsmall
  have htotal := concreteTotalCost_normalized hn φ ψ F hf
  have hplanes : (∑ j, Plane.cost (concreteMajorant hn φ ψ F j)) ≤ 1/10000000 := by
    have hg := pencilGamma_nonneg (normalizedPoints φ F hf)
      (normalizedHyperplanes φ ψ F hf)
    linarith
  obtain ⟨σ, hσ⟩ := normalized_weighted_reconstruction hn
    (normalizedPoints φ F hf) (normalizedHyperplanes φ ψ F hf)
    (concreteMajorant hn φ ψ F) hprotected
    (concreteMajorant_nonneg hn φ ψ F)
    (concreteMajorant_dominates hn φ ψ F hf hcoord)
    hplanes (1/10000000) (by linarith)
  refine ⟨F, hf, σ, repair_from_affine hn σ
    (LinearEquiv.refl L (Coordinates L n)) _ _ ?_ ?_ ?_⟩
  · rw [hyperplaneEmbedding_infinity]
    exact hcoord 0
  · convert hσ using 1 <;> simp only [Nat.card_eq_fintype_card] <;> ring
  · have hδ := errorDensity_le_numeric_threshold φ ψ hn (by norm_num at *; exact hsmall)
    have heq := errorDensity_normalized (frameNormalization F).symm
      (frameNormalization (imageFrame φ F hf)) φ ψ
    change errorDensity (normalizedPoints φ F hf) (normalizedHyperplanes φ ψ F hf) =
      errorDensity φ ψ at heq
    exact heq.symm ▸ hδ

end Erdos85.IncidenceRepair
