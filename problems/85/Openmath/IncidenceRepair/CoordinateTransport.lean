import Openmath.IncidenceRepair.Target
import Openmath.IncidenceRepair.GeometryCoupling
import Openmath.IncidenceRepair.FrameTransport

noncomputable section
namespace Erdos85.IncidenceRepair
variable {K L : Type*} [Field K] [Field L] {n : ℕ}

def pointEquiv (A : Coordinates K n ≃ₗ[K] Coordinates K n) : Point K n ≃ Point K n where
  toFun := Projectivization.map A.toLinearMap A.injective
  invFun := Projectivization.map A.symm.toLinearMap A.symm.injective
  left_inv := projective_map_symm_apply A
  right_inv := projective_map_symm_apply A.symm

def hyperplaneEquiv (A : Coordinates K n ≃ₗ[K] Coordinates K n) :
    Hyperplane K n ≃ Hyperplane K n := pointEquiv (dualCoordinates A)

lemma pointEquiv_eq_embedding (A : Coordinates K n ≃ₗ[K] Coordinates K n) (p : Point K n) :
    pointEquiv A p = pointEmbedding (RingHom.id K) A p := by
  induction p using Projectivization.ind with
  | h v hv => rfl

lemma hyperplaneEquiv_eq_embedding (A : Coordinates K n ≃ₗ[K] Coordinates K n)
    (H : Hyperplane K n) : hyperplaneEquiv A H = hyperplaneEmbedding (RingHom.id K) A H :=
  pointEquiv_eq_embedding (dualCoordinates A) H

lemma transport_incident_iff (A : Coordinates K n ≃ₗ[K] Coordinates K n)
    (p : Point K n) (H : Hyperplane K n) :
    Incident (pointEquiv A p) (hyperplaneEquiv A H) ↔ Incident p H := by
  rw [pointEquiv_eq_embedding, hyperplaneEquiv_eq_embedding, embedding_incident_iff]

lemma transport_isFrame_iff (A : Coordinates K n ≃ₗ[K] Coordinates K n)
    (f : Fin (n + 2) → Point K n) : IsFrame (pointEquiv A ∘ f) ↔ IsFrame f := by
  constructor
  · intro hf i
    have h := independent_projective_map (hf i) A.symm
    simpa only [Function.comp_apply, pointEquiv, Equiv.coe_fn_mk,
      projective_map_symm_apply] using h
  · intro hf i
    exact independent_projective_map (hf i) A

def frameEquiv (A : Coordinates K n ≃ₗ[K] Coordinates K n) : Frame K n ≃ Frame K n where
  toFun := mapFrame A
  invFun := mapFrame A.symm
  left_inv F := by
    apply Subtype.ext
    funext i
    exact projective_map_symm_apply A (F.val i)
  right_inv F := by
    apply Subtype.ext
    funext i
    exact projective_map_symm_apply A.symm (F.val i)

lemma brokenFlags_postcompose [Finite K] [Finite L]
    (B : Coordinates L n ≃ₗ[L] Coordinates L n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) :
    brokenFlags (pointEquiv B ∘ φ) (hyperplaneEquiv B ∘ ψ) = brokenFlags φ ψ := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun pH => by
    simp only [Function.comp_apply, transport_incident_iff])

lemma brokenFlags_precompose [Finite K] [Finite L]
    (A : Coordinates K n ≃ₗ[K] Coordinates K n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) :
    brokenFlags (φ ∘ pointEquiv A) (ψ ∘ hyperplaneEquiv A) = brokenFlags φ ψ := by
  apply Nat.card_congr
  exact Equiv.subtypeEquiv ((pointEquiv A).prodCongr (hyperplaneEquiv A)) (fun pH => by
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      Function.comp_apply, transport_incident_iff])

lemma frameSurvival_postcompose [Finite K] [Finite L]
    (B : Coordinates L n ≃ₗ[L] Coordinates L n) (φ : Point K n → Point L n) :
    frameSurvival (pointEquiv B ∘ φ) = frameSurvival φ := by
  unfold frameSurvival
  congr 2
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun F => by
    simpa only [Function.comp_assoc] using transport_isFrame_iff B (φ ∘ F.val))

lemma frameSurvival_precompose [Finite K] [Finite L]
    (A : Coordinates K n ≃ₗ[K] Coordinates K n) (φ : Point K n → Point L n) :
    frameSurvival (φ ∘ pointEquiv A) = frameSurvival φ := by
  unfold frameSurvival
  congr 2
  apply Nat.card_congr
  exact Equiv.subtypeEquiv (frameEquiv A) (fun _ => Iff.rfl)

lemma repairDistance_postcompose [Finite K] [Finite L]
    (B : Coordinates L n ≃ₗ[L] Coordinates L n)
    (φ Gp : Point K n → Point L n) (ψ Gh : Hyperplane K n → Hyperplane L n) :
    repairDistance (pointEquiv B ∘ φ) (pointEquiv B ∘ Gp)
      (hyperplaneEquiv B ∘ ψ) (hyperplaneEquiv B ∘ Gh) = repairDistance φ Gp ψ Gh := by
  unfold repairDistance
  congr 1
  · apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun p => not_congr (pointEquiv B).injective.eq_iff)
  · apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun H => not_congr (hyperplaneEquiv B).injective.eq_iff)

lemma repairDistance_precompose [Finite K] [Finite L]
    (A : Coordinates K n ≃ₗ[K] Coordinates K n)
    (φ Gp : Point K n → Point L n) (ψ Gh : Hyperplane K n → Hyperplane L n) :
    repairDistance (φ ∘ pointEquiv A) (Gp ∘ pointEquiv A)
      (ψ ∘ hyperplaneEquiv A) (Gh ∘ hyperplaneEquiv A) = repairDistance φ Gp ψ Gh := by
  unfold repairDistance
  congr 1
  · apply Nat.card_congr
    exact Equiv.subtypeEquiv (pointEquiv A) (fun _ => Iff.rfl)
  · apply Nat.card_congr
    exact Equiv.subtypeEquiv (hyperplaneEquiv A) (fun _ => Iff.rfl)

end Erdos85.IncidenceRepair
