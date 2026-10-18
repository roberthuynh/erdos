import Openmath.IncidenceRepair.CoordinateTransport
import Openmath.IncidenceRepair.CertificateGeometry
import Openmath.IncidenceRepair.ChartSlots

noncomputable section
namespace Erdos85.IncidenceRepair
variable {K L : Type*} [Field K] [Field L] {n : ℕ}

def imageFrame (φ : Point K n → Point L n) (F : Frame K n)
    (hf : IsFrame (φ ∘ F.1)) : Frame L n := ⟨φ ∘ F.1, hf⟩

def normalizedPoints (φ : Point K n → Point L n) (F : Frame K n)
    (hf : IsFrame (φ ∘ F.1)) : Point K n → Point L n :=
  pointEquiv (frameNormalization (imageFrame φ F hf)) ∘ φ ∘
    pointEquiv (frameNormalization F).symm

def normalizedHyperplanes (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) (F : Frame K n)
    (hf : IsFrame (φ ∘ F.1)) : Hyperplane K n → Hyperplane L n :=
  hyperplaneEquiv (frameNormalization (imageFrame φ F hf)) ∘ ψ ∘
    hyperplaneEquiv (frameNormalization F).symm

theorem normalization_inverse_coordinatePoint (F : Frame K n) (i : Fin (n + 1)) :
    pointEquiv (frameNormalization F).symm (coordinatePoint i) = F.1 i.castSucc := by
  change Projectivization.map (frameNormalization F).symm.toLinearMap
    (frameNormalization F).symm.injective (coordinatePoint i) = _
  rw [show coordinatePoint i = Projectivization.map (frameNormalization F).toLinearMap
    (frameNormalization F).injective (F.1 i.castSucc) from (frameNormalization_first F i).symm]
  exact projective_map_symm_apply _ _

theorem normalization_inverse_onesPoint (F : Frame K n) :
    pointEquiv (frameNormalization F).symm (onesPoint (K := K) (n := n)) =
      F.1 (Fin.last (n + 1)) := by
  change Projectivization.map (frameNormalization F).symm.toLinearMap
    (frameNormalization F).symm.injective onesPoint = _
  rw [show onesPoint = Projectivization.map (frameNormalization F).toLinearMap
    (frameNormalization F).injective (F.1 (Fin.last (n + 1))) from
      (frameNormalization_final F).symm]
  exact projective_map_symm_apply _ _

theorem normalizedPoints_coordinatePoint (φ : Point K n → Point L n) (F : Frame K n)
    (hf : IsFrame (φ ∘ F.1)) (i : Fin (n + 1)) :
    normalizedPoints φ F hf (coordinatePoint i) = coordinatePoint i := by
  simp only [normalizedPoints, Function.comp_apply, normalization_inverse_coordinatePoint]
  exact frameNormalization_first (imageFrame φ F hf) i

theorem normalizedPoints_onesPoint (φ : Point K n → Point L n) (F : Frame K n)
    (hf : IsFrame (φ ∘ F.1)) :
    normalizedPoints φ F hf (onesPoint (K := K) (n := n)) = onesPoint := by
  simp only [normalizedPoints, Function.comp_apply, normalization_inverse_onesPoint]
  exact frameNormalization_final (imageFrame φ F hf)

theorem normalized_incident_iff (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) (F : Frame K n)
    (hf : IsFrame (φ ∘ F.1)) (p : Point K n) (H : Hyperplane K n) :
    Incident (normalizedPoints φ F hf p) (normalizedHyperplanes φ ψ F hf H) ↔
      Incident (φ (pointEquiv (frameNormalization F).symm p))
        (ψ (hyperplaneEquiv (frameNormalization F).symm H)) := by
  exact transport_incident_iff _ _ _

theorem normalized_flag_error (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) (F : Frame K n)
    (hf : IsFrame (φ ∘ F.1)) (c : SourceFlag K n) :
    originalFlagError (normalizedPoints φ F hf) (normalizedHyperplanes φ ψ F hf) c =
      originalFlagError φ ψ ((frameNormalization F).symm • c) := by
  classical
  unfold originalFlagError
  rw [normalized_incident_iff]
  rfl

end Erdos85.IncidenceRepair
