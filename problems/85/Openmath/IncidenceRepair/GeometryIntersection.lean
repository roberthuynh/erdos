import Openmath.IncidenceRepair.GeometryCounts
import Openmath.IncidenceRepair.GeometryCoupling

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

variable {K L : Type*} [Field K] [Field L] {n : ℕ}

/-- Pull a target hyperplane equation back to a source-field semilinear equation. -/
def pulledFunctional (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n) (J : Hyperplane L n) :
    Coordinates K n →ₛₗ[σ] L :=
  (coefficientFunctional J).comp (semilinearVector σ A)

lemma incident_pointEmbedding_iff (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (p : Point K n) (J : Hyperplane L n) :
    Incident (pointEmbedding σ A p) J ↔ p.rep ∈ (pulledFunctional σ A J).ker := by
  conv_lhs => rw [← Projectivization.mk_rep p]
  rw [pointEmbedding, Projectivization.map_mk, incident_mk_iff,
    hyperplaneSubspace_eq_ker]
  rfl

lemma source_hyperplane_not_le_pulled_kernel (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (H : Hyperplane K n) (J : Hyperplane L n)
    (hne : J ≠ hyperplaneEmbedding σ A H) :
    ¬ hyperplaneSubspace H ≤ (pulledFunctional σ A J).ker := by
  intro hle
  have hs : hyperplaneSubspace (hyperplaneEmbedding σ A H) ≤ hyperplaneSubspace J := by
    rw [hyperplaneEmbedding_coupled σ A H]
    apply Submodule.span_le.2
    rintro _ ⟨v, hv, rfl⟩
    have hz := hle hv
    change coefficientFunctional J (semilinearVector σ A v) = 0 at hz
    change semilinearVector σ A v ∈ hyperplaneSubspace J
    rw [hyperplaneSubspace_eq_ker]
    exact hz
  have he := Submodule.eq_of_le_of_finrank_eq hs
    (by rw [hyperplane_finrank, hyperplane_finrank])
  exact hne (hyperplaneSubspace_injective he).symm

/-- A wrong target hyperplane cuts the embedded source hyperplane in a source
subspace of vector dimension at most n-1, even over a proper field extension. -/
lemma wrong_hyperplane_intersection_finrank (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (H : Hyperplane K n) (J : Hyperplane L n)
    (hne : J ≠ hyperplaneEmbedding σ A H) :
    Module.finrank K ↥(hyperplaneSubspace H ⊓ (pulledFunctional σ A J).ker) ≤ n - 1 := by
  have hn := source_hyperplane_not_le_pulled_kernel σ A H J hne
  have hs : hyperplaneSubspace H ⊓ (pulledFunctional σ A J).ker < hyperplaneSubspace H := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    apply hn
    intro v hv
    have hm : v ∈ hyperplaneSubspace H ⊓ (pulledFunctional σ A J).ker := by
      rw [he]
      exact hv
    exact hm.2
  have hd := Submodule.finrank_lt_finrank_of_lt hs
  rw [hyperplane_finrank] at hd
  omega

/-- The exact Section 7 projective intersection bound on original source points. -/
lemma wrong_hyperplane_intersection_card [Finite K] (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (H : Hyperplane K n) (J : Hyperplane L n)
    (hne : J ≠ hyperplaneEmbedding σ A H) :
    Nat.card {p : Point K n // Incident p H ∧ Incident (pointEmbedding σ A p) J} ≤
      (Nat.card K ^ (n - 1) - 1) / (Nat.card K - 1) := by
  let S := hyperplaneSubspace H ⊓ (pulledFunctional σ A J).ker
  let e : {p : Point K n // Incident p H ∧ Incident (pointEmbedding σ A p) J} ≃
      {p : Point K n // p.rep ∈ S} := Equiv.subtypeEquivRight (fun p => by
        rw [incident_iff_rep_mem, incident_pointEmbedding_iff]
        rfl)
  rw [Nat.card_congr e, ← Nat.card_congr (submodulePointEquiv S),
    Projectivization.card_of_finrank K S rfl]
  rw [← Nat.geomSum_eq (Finite.one_lt_card (α := K)) (n - 1)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (wrong_hyperplane_intersection_finrank σ A H J hne)
  · intro i _ _
    exact Nat.zero_le _

lemma dualCoordinates_involutive (A : Coordinates L n ≃ₗ[L] Coordinates L n) :
    dualCoordinates (dualCoordinates A) = A := by
  apply LinearEquiv.ext
  intro h
  apply (dotProductEquiv L (Fin (n + 1))).injective
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := (dualCoordinates A).surjective w
  change dualCoordinates (dualCoordinates A) h ⬝ᵥ dualCoordinates A v =
    A h ⬝ᵥ dualCoordinates A v
  rw [dualCoordinates_eval, (dualCoordinates A).symm_apply_apply,
    dotProduct_comm (A h), dualCoordinates_eval, A.symm_apply_apply, dotProduct_comm v]

/-- The dual wrong-point intersection bound, counting original source hyperplanes. -/
lemma wrong_point_intersection_card [Finite K] (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (p : Point K n) (x : Point L n)
    (hne : x ≠ pointEmbedding σ A p) :
    Nat.card {H : Hyperplane K n // Incident p H ∧ Incident x (hyperplaneEmbedding σ A H)} ≤
      (Nat.card K ^ (n - 1) - 1) / (Nat.card K - 1) := by
  have hn : x ≠ hyperplaneEmbedding σ (dualCoordinates A) p := by
    simpa only [hyperplaneEmbedding, dualCoordinates_involutive] using hne
  have hb := wrong_hyperplane_intersection_card σ (dualCoordinates A) p x hn
  let e : {H : Hyperplane K n // Incident p H ∧ Incident x (hyperplaneEmbedding σ A H)} ≃
      {H : Point K n // Incident H p ∧ Incident (pointEmbedding σ (dualCoordinates A) H) x} :=
    Equiv.subtypeEquivRight (fun H => by
      rw [incident_symm p H, incident_symm x]
      rfl)
  rwa [Nat.card_congr e]

end Erdos85.IncidenceRepair
