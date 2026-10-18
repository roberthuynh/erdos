import Openmath.IncidenceRepair.CoordinateTransport
import Openmath.IncidenceRepair.GeometryIntersection

noncomputable section
open scoped Matrix
namespace Erdos85.IncidenceRepair
variable {K L : Type*} [Field K] [Field L] {n : ℕ}

def linearEquivMatrix (B : Coordinates K n ≃ₗ[K] Coordinates K n) :
    Matrix.GeneralLinearGroup (Fin (n + 1)) K :=
  Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv B)

def scalarExtend (σ : K →+* L) (B : Coordinates K n ≃ₗ[K] Coordinates K n) :
    Coordinates L n ≃ₗ[L] Coordinates L n :=
  (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.map σ (linearEquivMatrix B))).toLinearEquiv

lemma linearEquivMatrix_mulVec (B : Coordinates K n ≃ₗ[K] Coordinates K n)
    (v : Coordinates K n) : (linearEquivMatrix B : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *ᵥ v = B v := by
  change (Matrix.GeneralLinearGroup.toLin (linearEquivMatrix B)).toLinearEquiv v = B v
  simp only [linearEquivMatrix, MulEquiv.apply_symm_apply]
  rfl

lemma scalarExtend_coordinateMap (σ : K →+* L)
    (B : Coordinates K n ≃ₗ[K] Coordinates K n) (v : Coordinates K n) :
    scalarExtend σ B (coordinateMap σ v) = coordinateMap σ (B v) := by
  rw [← linearEquivMatrix_mulVec B v]
  change ((linearEquivMatrix B : Matrix (Fin (n + 1)) (Fin (n + 1)) K).map σ) *ᵥ
    coordinateMap σ v = coordinateMap σ ((linearEquivMatrix B : Matrix _ _ K) *ᵥ v)
  ext i
  simp [Matrix.mulVec, dotProduct, coordinateMap, map_sum, map_mul]

lemma embedding_precompose (σ : K →+* L)
    (B : Coordinates K n ≃ₗ[K] Coordinates K n)
    (C : Coordinates L n ≃ₗ[L] Coordinates L n) (p : Point K n) :
    pointEmbedding σ C (pointEquiv B p) =
      pointEmbedding σ ((scalarExtend σ B).trans C) p := by
  induction p using Projectivization.ind with
  | h v hv =>
    simp only [pointEquiv, Equiv.coe_fn_mk, pointEmbedding, Projectivization.map_mk]
    apply (Projectivization.mk_eq_mk_iff' L _ _ _ _).2
    refine ⟨1, ?_⟩
    change 1 • C (scalarExtend σ B (coordinateMap σ v)) = C (coordinateMap σ (B v))
    rw [one_smul, scalarExtend_coordinateMap]

lemma embedding_postcompose (σ : K →+* L)
    (C A : Coordinates L n ≃ₗ[L] Coordinates L n) (p : Point K n) :
    pointEquiv A (pointEmbedding σ C p) = pointEmbedding σ (C.trans A) p := by
  induction p using Projectivization.ind with
  | h v hv => rfl

lemma hyperplane_determined_by_embedded_incidence (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n) (H : Hyperplane K n) (J : Hyperplane L n)
    (hJ : ∀ p, Incident p H → Incident (pointEmbedding σ A p) J) :
    J = hyperplaneEmbedding σ A H := by
  by_contra hne
  apply source_hyperplane_not_le_pulled_kernel σ A H J hne
  intro v hv
  by_cases hz : v = 0
  · simp [hz]
  · have hi := hJ (Projectivization.mk K v hz) ((incident_mk_iff v hz H).2 hv)
    simp only [pointEmbedding, Projectivization.map_mk, incident_mk_iff,
      hyperplaneSubspace_eq_ker] at hi
    exact hi

/-- Undoing independent source and target coordinate changes retains one actual
field embedding and one invertible target matrix for BOTH projective actions. -/
lemma hyperplaneEmbedding_transport (σ : K →+* L)
    (B : Coordinates K n ≃ₗ[K] Coordinates K n)
    (C A : Coordinates L n ≃ₗ[L] Coordinates L n) (H : Hyperplane K n) :
    hyperplaneEquiv A (hyperplaneEmbedding σ C (hyperplaneEquiv B H)) =
      hyperplaneEmbedding σ (((scalarExtend σ B).trans C).trans A) H := by
  apply hyperplane_determined_by_embedded_incidence
  intro p hp
  rw [← embedding_postcompose, ← embedding_precompose]
  apply (transport_incident_iff A _ _).2
  apply (embedding_incident_iff σ C _ _).2
  exact (transport_incident_iff B p H).2 hp

end Erdos85.IncidenceRepair
