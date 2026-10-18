import Openmath.IncidenceRepair.Geometry

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

variable {K L : Type*} [Field K] [Field L] {n : ℕ}

/-- The inverse-transpose coordinate action, expressed through the canonical dual. -/
def dualCoordinates (A : Coordinates L n ≃ₗ[L] Coordinates L n) :
    Coordinates L n ≃ₗ[L] Coordinates L n :=
  ((dotProductEquiv L (Fin (n + 1))).trans A.symm.dualMap).trans
    (dotProductEquiv L (Fin (n + 1))).symm

lemma dualCoordinates_eval (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (h v : Coordinates L n) :
    (dualCoordinates A h) ⬝ᵥ v = h ⬝ᵥ (A.symm v) := by
  change (dotProductEquiv L (Fin (n + 1)) (dualCoordinates A h)) v = _
  simp [dualCoordinates, LinearEquiv.dualMap_apply]

/-- The single hyperplane action paired with the point action. -/
def hyperplaneEmbedding (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n) : Hyperplane K n → Hyperplane L n :=
  pointEmbedding σ (dualCoordinates A)

lemma hyperplaneEmbedding_injective (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n) :
    Function.Injective (hyperplaneEmbedding σ A) :=
  pointEmbedding_injective σ (dualCoordinates A)

lemma coordinateMap_dot (σ : K →+* L) (u v : Coordinates K n) :
    coordinateMap σ u ⬝ᵥ coordinateMap σ v = σ (u ⬝ᵥ v) := by
  simp [coordinateMap, dotProduct, map_sum, map_mul]

/-- The point action and its inverse-transpose hyperplane action preserve AND
reflect incidence, including over a proper field extension. -/
lemma embedding_incident_iff (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (p : Point K n) (H : Hyperplane K n) :
    Incident (pointEmbedding σ A p) (hyperplaneEmbedding σ A H) ↔ Incident p H := by
  induction p using Projectivization.ind with
  | h v hv =>
    induction H using Projectivization.ind with
    | h h hh =>
      simp only [hyperplaneEmbedding, pointEmbedding, Projectivization.map_mk,
        Incident, Projectivization.orthogonal_mk]
      change A (coordinateMap σ v) ⬝ᵥ dualCoordinates A (coordinateMap σ h) = 0 ↔
        v ⬝ᵥ h = 0
      rw [dotProduct_comm, dualCoordinates_eval, A.symm_apply_apply, coordinateMap_dot,
        map_eq_zero, dotProduct_comm]

lemma mem_hyperplaneSubspace_mk (h : Coordinates K n) (hh : h ≠ 0)
    (v : Coordinates K n) :
    v ∈ hyperplaneSubspace (Projectivization.mk K h hh) ↔ v ⬝ᵥ h = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K h hh
  change v ⬝ᵥ (Projectivization.mk K h hh).rep = 0 ↔ v ⬝ᵥ h = 0
  rw [← ha, dotProduct_smul]
  exact smul_eq_zero_iff_eq a

lemma coordinateMap_single (σ : K →+* L) (i : Fin (n + 1)) :
    coordinateMap σ (Pi.single i 1) = Pi.single i 1 := by
  ext j
  by_cases h : j = i
  · subst j; simp [coordinateMap]
  · simp [coordinateMap, h]

lemma sum_pivot (w k : Coordinates L n) (j : Fin (n + 1))
    (hz : ∑ i, w i * k i = 0) :
    ∑ i, w i • (Pi.single i 1 - k i • Pi.single j 1) = w := by
  simp_rw [smul_sub, smul_smul]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hz, zero_smul, sub_zero]
  ext i
  simp [Pi.single_apply, Finset.sum_apply]

/-- Scalar extension of one linear kernel is its target-field span, proved by
explicit elimination at a nonzero source coordinate, without a rank assumption. -/
lemma coordinate_kernel_span (σ : K →+* L) (h : Coordinates K n) (hh : h ≠ 0)
    (w : Coordinates L n) (hw : w ⬝ᵥ coordinateMap σ h = 0) :
    w ∈ Submodule.span L (coordinateMap σ '' {v : Coordinates K n | v ⬝ᵥ h = 0}) := by
  obtain ⟨j, hj⟩ : ∃ j, h j ≠ 0 := by
    by_contra! hz
    exact hh (funext hz)
  let v : Fin (n + 1) → Coordinates K n :=
    fun i => Pi.single i 1 - (h i / h j) • Pi.single j 1
  have hv (i : Fin (n + 1)) : v i ⬝ᵥ h = 0 := by
    simp [v, sub_dotProduct, smul_dotProduct, hj]
  have hm (i : Fin (n + 1)) : coordinateMap σ (v i) =
      Pi.single i 1 - σ (h i / h j) • Pi.single j 1 := by
    simp only [v, map_sub, map_smulₛₗ, coordinateMap_single]
  have hz : ∑ i, w i * σ (h i / h j) = 0 := by
    simp_rw [map_div₀, ← mul_div_assoc]
    rw [← Finset.sum_div]
    change (w ⬝ᵥ coordinateMap σ h) / σ (h j) = 0
    rw [hw, zero_div]
  have heq : ∑ i, w i • coordinateMap σ (v i) = w := by
    simp_rw [hm]
    exact sum_pivot w (fun i => σ (h i / h j)) j hz
  rw [← heq]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨v i, hv i, rfl⟩

lemma mem_hyperplaneEmbedding_mk (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (h : Coordinates K n) (hh : h ≠ 0) (w : Coordinates L n) :
    w ∈ hyperplaneSubspace (hyperplaneEmbedding σ A (Projectivization.mk K h hh)) ↔
      A.symm w ⬝ᵥ coordinateMap σ h = 0 := by
  simp only [hyperplaneEmbedding, pointEmbedding, Projectivization.map_mk,
    mem_hyperplaneSubspace_mk]
  change w ⬝ᵥ dualCoordinates A (coordinateMap σ h) = 0 ↔ _
  rw [dotProduct_comm, dualCoordinates_eval, dotProduct_comm]

/-- The explicit inverse-transpose hyperplane embedding has exactly the required
target-field span. This includes arbitrary proper finite-field embeddings. -/
lemma hyperplaneEmbedding_coupled (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n) :
    Coupled σ A (hyperplaneEmbedding σ A) := by
  intro H
  induction H using Projectivization.ind with
  | h h hh =>
    let U := Submodule.span L (semilinearVector σ A ''
      (hyperplaneSubspace (Projectivization.mk K h hh) : Set (Coordinates K n)))
    apply le_antisymm
    · intro w hw
      rw [mem_hyperplaneEmbedding_mk] at hw
      have hspan := coordinate_kernel_span σ h hh (A.symm w) hw
      have hs : Submodule.span L (coordinateMap σ ''
          {v : Coordinates K n | v ⬝ᵥ h = 0}) ≤ U.comap A.toLinearMap := by
        apply Submodule.span_le.2
        rintro _ ⟨v, hv, rfl⟩
        change A (coordinateMap σ v) ∈ U
        exact Submodule.subset_span ⟨v, (mem_hyperplaneSubspace_mk h hh v).2 hv, rfl⟩
      have hm := hs hspan
      change A (A.symm w) ∈ U at hm
      simpa only [A.apply_symm_apply] using hm
    · apply Submodule.span_le.2
      rintro _ ⟨v, hv, rfl⟩
      change semilinearVector σ A v ∈
        hyperplaneSubspace (hyperplaneEmbedding σ A (Projectivization.mk K h hh))
      rw [mem_hyperplaneEmbedding_mk]
      change A.symm (A (coordinateMap σ v)) ⬝ᵥ coordinateMap σ h = 0
      rw [A.symm_apply_apply, coordinateMap_dot]
      rw [(mem_hyperplaneSubspace_mk h hh v).1 hv, map_zero]

end Erdos85.IncidenceRepair
