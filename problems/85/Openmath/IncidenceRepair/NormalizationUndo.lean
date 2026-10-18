import Openmath.IncidenceRepair.SemilinearTransport

noncomputable section
namespace Erdos85.IncidenceRepair
variable {K L : Type*} [Field K] [Field L] {n : ℕ}

lemma pointEquiv_symm_apply (A : Coordinates K n ≃ₗ[K] Coordinates K n) (p : Point K n) :
    pointEquiv A.symm (pointEquiv A p) = p := projective_map_symm_apply A p

lemma dualCoordinates_symm_apply (A : Coordinates K n ≃ₗ[K] Coordinates K n)
    (v : Coordinates K n) : dualCoordinates A.symm (dualCoordinates A v) = v := by
  apply (dotProductEquiv K (Fin (n + 1))).injective
  apply LinearMap.ext
  intro w
  change dualCoordinates A.symm (dualCoordinates A v) ⬝ᵥ w = v ⬝ᵥ w
  rw [dualCoordinates_eval, LinearEquiv.symm_symm, dualCoordinates_eval, A.symm_apply_apply]

lemma hyperplaneEquiv_symm_apply (A : Coordinates K n ≃ₗ[K] Coordinates K n)
    (H : Hyperplane K n) : hyperplaneEquiv A.symm (hyperplaneEquiv A H) = H := by
  induction H using Projectivization.ind with
  | h h hh =>
    simp only [hyperplaneEquiv, pointEquiv, Equiv.coe_fn_mk, Projectivization.map_mk,
      LinearEquiv.coe_coe, dualCoordinates_symm_apply]

lemma pointEquiv_apply_symm (A : Coordinates K n ≃ₗ[K] Coordinates K n) (p : Point K n) :
    pointEquiv A (pointEquiv A.symm p) = p := by
  simpa only [LinearEquiv.symm_symm] using pointEquiv_symm_apply A.symm p

lemma hyperplaneEquiv_apply_symm (A : Coordinates K n ≃ₗ[K] Coordinates K n)
    (H : Hyperplane K n) : hyperplaneEquiv A (hyperplaneEquiv A.symm H) = H := by
  simpa only [LinearEquiv.symm_symm] using hyperplaneEquiv_symm_apply A.symm H

lemma coupled_eq_hyperplaneEmbedding (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n) (Gh : Hyperplane K n → Hyperplane L n)
    (h : Coupled σ A Gh) : Gh = hyperplaneEmbedding σ A := by
  funext H
  apply hyperplane_determined_by_embedded_incidence
  intro p hp
  exact Coupled.preserves_incidence σ A Gh h p H hp

def undoMatrix (σ : K →+* L)
    (S : Coordinates K n ≃ₗ[K] Coordinates K n)
    (B C : Coordinates L n ≃ₗ[L] Coordinates L n) :
    Coordinates L n ≃ₗ[L] Coordinates L n :=
  ((scalarExtend σ S.symm).trans C).trans B.symm

/-- Exact paired-distance invariance when a normalized repair is pulled back.
S is the source precomposition and B the target postcomposition. -/
lemma repairDistance_undo [Finite K] [Finite L] (σ : K →+* L)
    (S : Coordinates K n ≃ₗ[K] Coordinates K n)
    (B C : Coordinates L n ≃ₗ[L] Coordinates L n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) :
    repairDistance φ (pointEmbedding σ (undoMatrix σ S B C))
      ψ (hyperplaneEmbedding σ (undoMatrix σ S B C)) =
    repairDistance (pointEquiv B ∘ φ ∘ pointEquiv S) (pointEmbedding σ C)
      (hyperplaneEquiv B ∘ ψ ∘ hyperplaneEquiv S) (hyperplaneEmbedding σ C) := by
  let φN := pointEquiv B ∘ φ ∘ pointEquiv S
  let ψN := hyperplaneEquiv B ∘ ψ ∘ hyperplaneEquiv S
  have hφ : (pointEquiv B.symm ∘ φN) ∘ pointEquiv S.symm = φ := by
    funext p
    simp only [φN, Function.comp_apply, pointEquiv_symm_apply,
      pointEquiv_apply_symm]
  have hψ : (hyperplaneEquiv B.symm ∘ ψN) ∘ hyperplaneEquiv S.symm = ψ := by
    funext H
    simp only [ψN, Function.comp_apply, hyperplaneEquiv_symm_apply,
      hyperplaneEquiv_apply_symm]
  have hGp : (pointEquiv B.symm ∘ pointEmbedding σ C) ∘ pointEquiv S.symm =
      pointEmbedding σ (undoMatrix σ S B C) := by
    funext p
    exact (congrArg (pointEquiv B.symm) (embedding_precompose σ S.symm C p)).trans
      (embedding_postcompose σ ((scalarExtend σ S.symm).trans C) B.symm p)
  have hGh : (hyperplaneEquiv B.symm ∘ hyperplaneEmbedding σ C) ∘ hyperplaneEquiv S.symm =
      hyperplaneEmbedding σ (undoMatrix σ S B C) := by
    funext H
    exact hyperplaneEmbedding_transport σ S.symm C B.symm H
  calc
    _ = repairDistance ((pointEquiv B.symm ∘ φN) ∘ pointEquiv S.symm)
        ((pointEquiv B.symm ∘ pointEmbedding σ C) ∘ pointEquiv S.symm)
        ((hyperplaneEquiv B.symm ∘ ψN) ∘ hyperplaneEquiv S.symm)
        ((hyperplaneEquiv B.symm ∘ hyperplaneEmbedding σ C) ∘ hyperplaneEquiv S.symm) := by
          rw [hφ, hψ, hGp, hGh]
    _ = repairDistance (pointEquiv B.symm ∘ φN) (pointEquiv B.symm ∘ pointEmbedding σ C)
        (hyperplaneEquiv B.symm ∘ ψN) (hyperplaneEquiv B.symm ∘ hyperplaneEmbedding σ C) :=
          repairDistance_precompose S.symm _ _ _ _
    _ = _ := repairDistance_postcompose B.symm _ _ _ _

lemma brokenFlags_normalized [Finite K] [Finite L]
    (S : Coordinates K n ≃ₗ[K] Coordinates K n)
    (B : Coordinates L n ≃ₗ[L] Coordinates L n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) :
    brokenFlags (pointEquiv B ∘ φ ∘ pointEquiv S) (hyperplaneEquiv B ∘ ψ ∘ hyperplaneEquiv S) =
      brokenFlags φ ψ := by
  rw [← Function.comp_assoc (pointEquiv B), ← Function.comp_assoc (hyperplaneEquiv B),
    brokenFlags_precompose, brokenFlags_postcompose]

lemma errorDensity_normalized [Finite K] [Finite L]
    (S : Coordinates K n ≃ₗ[K] Coordinates K n)
    (B : Coordinates L n ≃ₗ[L] Coordinates L n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) :
    errorDensity (pointEquiv B ∘ φ ∘ pointEquiv S) (hyperplaneEquiv B ∘ ψ ∘ hyperplaneEquiv S) =
      errorDensity φ ψ := by
  unfold errorDensity
  rw [brokenFlags_normalized]

lemma frameSurvival_normalized [Finite K] [Finite L]
    (S : Coordinates K n ≃ₗ[K] Coordinates K n)
    (B : Coordinates L n ≃ₗ[L] Coordinates L n) (φ : Point K n → Point L n) :
    frameSurvival (pointEquiv B ∘ φ ∘ pointEquiv S) = frameSurvival φ := by
  rw [← Function.comp_assoc (pointEquiv B), frameSurvival_precompose, frameSurvival_postcompose]

/-- A full normalized repair bound transfers back with exactly the same number
of original broken flags and the same source-field degree scale. -/
lemma normalized_repair_undo [Finite K] [Finite L] (σ : K →+* L)
    (S : Coordinates K n ≃ₗ[K] Coordinates K n)
    (B C : Coordinates L n ≃ₗ[L] Coordinates L n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (Gh : Hyperplane K n → Hyperplane L n) (hC : Coupled σ C Gh)
    (hbound : (repairDistance (pointEquiv B ∘ φ ∘ pointEquiv S) (pointEmbedding σ C)
      (hyperplaneEquiv B ∘ ψ ∘ hyperplaneEquiv S) Gh : ℝ) ≤
      5 * (brokenFlags (pointEquiv B ∘ φ ∘ pointEquiv S)
        (hyperplaneEquiv B ∘ ψ ∘ hyperplaneEquiv S) : ℝ) / (Nat.card K : ℝ) ^ (n - 1)) :
    ∃ (A : Coordinates L n ≃ₗ[L] Coordinates L n) (G : Hyperplane K n → Hyperplane L n),
      Coupled σ A G ∧ (repairDistance φ (pointEmbedding σ A) ψ G : ℝ) ≤
        5 * (brokenFlags φ ψ : ℝ) / (Nat.card K : ℝ) ^ (n - 1) := by
  refine ⟨undoMatrix σ S B C, hyperplaneEmbedding σ (undoMatrix σ S B C),
    hyperplaneEmbedding_coupled _ _, ?_⟩
  rw [repairDistance_undo]
  rwa [coupled_eq_hyperplaneEmbedding σ C Gh hC, brokenFlags_normalized] at hbound

end Erdos85.IncidenceRepair
