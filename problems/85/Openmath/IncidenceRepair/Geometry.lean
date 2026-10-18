import Mathlib

/-! Actual canonical projective spaces for the incidence-repair theorem.
Points and hyperplanes are projective nonzero vectors. For hyperplanes the vector
is a coefficient vector, and incidence is vanishing of the ordinary dot product.
No approximate-rigidity or correction assertion is assumed here. -/

noncomputable section
open scoped BigOperators

namespace Erdos85.IncidenceRepair

abbrev Coordinates (K : Type*) (n : ℕ) := Fin (n + 1) → K
abbrev Point (K : Type*) [Field K] (n : ℕ) := Projectivization K (Coordinates K n)
/-- A projective coefficient vector represents its kernel hyperplane. -/
abbrev Hyperplane (K : Type*) [Field K] (n : ℕ) := Projectivization K (Coordinates K n)

variable {K L : Type*} [Field K] [Field L] {n : ℕ}

/-- Original source incidence, independent of representative choices. -/
def Incident (p : Point K n) (H : Hyperplane K n) : Prop :=
  Projectivization.orthogonal p H

/-- An ordered full projective frame has n+2 points and every n+1 are independent. -/
def IsFrame (f : Fin (n + 2) → Point K n) : Prop :=
  ∀ i : Fin (n + 2), Projectivization.Independent (fun j : {j // j ≠ i} => f j)

abbrev Frame (K : Type*) [Field K] (n : ℕ) :=
  {f : Fin (n + 2) → Point K n // IsFrame f}

instance pointFinite [Finite K] : Finite (Point K n) := inferInstance
instance frameFinite [Finite K] : Finite (Frame K n) := inferInstance

/-- Coordinatewise application of a field embedding. -/
def coordinateMap (σ : K →+* L) : Coordinates K n →ₛₗ[σ] Coordinates L n where
  toFun v := fun i => σ (v i)
  map_add' v w := by ext i; exact map_add σ (v i) (w i)
  map_smul' c v := by ext i; exact map_mul σ c (v i)

lemma coordinateMap_injective (σ : K →+* L) :
    Function.Injective (coordinateMap (n := n) σ) := by
  intro v w h
  funext i
  exact σ.injective (congr_fun h i)

/-- The coordinate representative v ↦ A σ(v), with A invertible over the target. -/
def semilinearVector (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n) :
    Coordinates K n →ₛₗ[σ] Coordinates L n :=
  A.toLinearMap.comp (coordinateMap σ)

lemma semilinearVector_injective (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n) :
    Function.Injective (semilinearVector σ A) :=
  A.injective.comp (coordinateMap_injective σ)

/-- The induced, actual projective point map. -/
def pointEmbedding (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n) : Point K n → Point L n :=
  Projectivization.map (semilinearVector σ A) (semilinearVector_injective σ A)

/-- The vector hyperplane belonging to a coefficient-vector projective point. -/
def hyperplaneSubspace (H : Hyperplane K n) : Submodule K (Coordinates K n) where
  carrier := {v | ∑ i, v i * H.rep i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change ∑ i, v i * H.rep i = 0 at hv
    change ∑ i, w i * H.rep i = 0 at hw
    change ∑ i, (v i + w i) * H.rep i = 0
    simp only [add_mul, Finset.sum_add_distrib, hv, hw, add_zero]
  smul_mem' := by
    intro c v hv
    change ∑ i, v i * H.rep i = 0 at hv
    change ∑ i, (c * v i) * H.rep i = 0
    simp only [mul_assoc, ← Finset.mul_sum, hv, mul_zero]

/-- The hyperplane action must use the SAME σ and A as the point action.
The image is exactly the target-field span of the embedded source hyperplane. -/
def Coupled (σ : K →+* L) (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (G : Hyperplane K n → Hyperplane L n) : Prop :=
  ∀ H, hyperplaneSubspace (G H) =
    Submodule.span L (semilinearVector σ A '' (hyperplaneSubspace H : Set (Coordinates K n)))

lemma incident_iff_rep_mem (p : Point K n) (H : Hyperplane K n) :
    Incident p H ↔ p.rep ∈ hyperplaneSubspace H := by
  change Projectivization.orthogonal p H ↔ ∑ i, p.rep i * H.rep i = 0
  have h := Projectivization.orthogonal_mk p.rep_nonzero H.rep_nonzero
  simpa only [Projectivization.mk_rep, dotProduct] using h

lemma point_card [Finite K] :
    Nat.card (Point K n) = (Nat.card K ^ (n + 1) - 1) / (Nat.card K - 1) := by
  rw [Projectivization.card'']
  simp [Coordinates, Nat.card_fun]

/-- Projective injectivity also holds for proper field embeddings: target scalars
relating two embedded source vectors descend to the source using one nonzero coordinate. -/
lemma pointEmbedding_injective (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n) :
    Function.Injective (pointEmbedding σ A) := by
  intro p q
  induction p using Projectivization.ind with
  | h u hu =>
    induction q using Projectivization.ind with
    | h v hv =>
      intro h
      simp only [pointEmbedding, Projectivization.map_mk,
        Projectivization.mk_eq_mk_iff'] at h ⊢
      obtain ⟨a, ha⟩ := h
      change a • A (coordinateMap σ v) = A (coordinateMap σ u) at ha
      rw [← A.map_smul] at ha
      have hc := A.injective ha
      obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
        by_contra! hzero
        apply hv
        funext i
        exact hzero i
      have hj' : σ (v j) ≠ 0 := (map_ne_zero σ).2 hj
      have haj : a = σ (u j) / σ (v j) := by
        apply (eq_div_iff hj').2
        exact congr_fun hc j
      refine ⟨u j / v j, ?_⟩
      funext i
      apply σ.injective
      change σ ((u j / v j) * v i) = σ (u i)
      rw [map_mul, map_div₀, ← haj]
      exact congr_fun hc i

lemma incident_mk_iff (v : Coordinates K n) (hv : v ≠ 0) (H : Hyperplane K n) :
    Incident (Projectivization.mk K v hv) H ↔ v ∈ hyperplaneSubspace H := by
  change Projectivization.orthogonal (Projectivization.mk K v hv) H ↔
    ∑ i, v i * H.rep i = 0
  have h := Projectivization.orthogonal_mk hv H.rep_nonzero
  simpa only [Projectivization.mk_rep, dotProduct] using h

/-- The exact coupled span action preserves every original source flag. -/
lemma Coupled.preserves_incidence (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (G : Hyperplane K n → Hyperplane L n) (hG : Coupled σ A G)
    (p : Point K n) (H : Hyperplane K n) (hp : Incident p H) :
    Incident (pointEmbedding σ A p) (G H) := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [incident_mk_iff] at hp
    unfold pointEmbedding
    rw [Projectivization.map_mk, incident_mk_iff, hG H]
    exact Submodule.subset_span ⟨v, hp, rfl⟩

end Erdos85.IncidenceRepair
