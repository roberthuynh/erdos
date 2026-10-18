import Openmath.IncidenceRepair.NormalizedRepair
import Openmath.IncidenceRepair.NormalizationUndo

/-! Full published projective-incidence repair theorem. All geometric,
counting, protected-frame and reconstruction obligations are discharged by
the imported proofs. The statement is exactly `RepairClaim K L n`. -/

noncomputable section
namespace Erdos85.IncidenceRepair

/-- Arbitrary point and hyperplane maps between finite projective spaces admit
one coupled semilinear repair under the stated frame-survival/error hypothesis.
This is the repair theorem associated with #85, not the original Erdős problem. -/
theorem projective_incidence_repair
    (K L : Type*) [Field K] [Field L] [Finite K] [Finite L] (n : ℕ) :
    RepairClaim K L n := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  intro hn φ ψ hρ hsmall
  have hsmall' : errorDensity φ ψ ≤
      frameSurvival φ / (1000000000 * (n : ℝ)^2) := by
    norm_num at hsmall ⊢
    exact hsmall
  obtain ⟨F, hf, σ, hbound, hdegree⟩ :=
    exists_normalized_repair hn φ ψ hρ hsmall'
  let S := (frameNormalization F).symm
  let B := frameNormalization (imageFrame φ F hf)
  obtain ⟨A, Gh, hcoupled, hrepair⟩ := normalized_repair_undo σ S B
    (LinearEquiv.refl L _) φ ψ
    (hyperplaneEmbedding σ (LinearEquiv.refl L _))
    (hyperplaneEmbedding_coupled _ _) hbound
  refine ⟨σ, A, Gh, hcoupled, hrepair, ?_⟩
  simpa only [normalizedPoints, normalizedHyperplanes, brokenFlags_normalized] using hdegree

end Erdos85.IncidenceRepair
