import Openmath.IncidenceRepair.GlobalFrameSelection
import Openmath.IncidenceRepair.GlobalReconstruction

noncomputable section
open scoped BigOperators Classical
namespace Erdos85.IncidenceRepair
variable {K L : Type*} [Field K] [Field L] [Fintype K] {n : ℕ}

def concreteMajorant (hn : 2 ≤ n) (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) (F : Frame K n)
    (j : Fin (n-1)) : Point K 2 → Hyperplane K 2 → ℝ :=
  rawChartMajorant (concreteChartSlot hn j) (originalFlagError φ ψ) F

theorem concreteMajorant_nonneg (hn : 2 ≤ n) (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) (F : Frame K n) (j : Fin (n-1))
    (p : Point K 2) (H : Hyperplane K 2) : 0 ≤ concreteMajorant hn φ ψ F j p H := by
  unfold concreteMajorant rawChartMajorant
  split_ifs
  · exact Finset.sum_nonneg (fun s _ => originalFlagError_nonneg φ ψ _)
  · exact le_refl 0

theorem concreteMajorant_dominates (hn : 2 ≤ n) (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) (F : Frame K n) (hf : IsFrame (φ ∘ F.1))
    (hhyperplanes : ∀ i, normalizedHyperplanes φ ψ F hf (coordinateHyperplane i) = coordinateHyperplane i)
    (j : Fin (n-1)) (p : Point K 2) (H : Hyperplane K 2) (hinc : Incident p H)
    (hbad : ¬ Incident (normalizedChartPoints hn (normalizedPoints φ F hf) j p)
      (inducedHyperplanes (canonicalChart n hn j) (normalizedHyperplanes φ ψ F hf) H)) :
    1 ≤ concreteMajorant hn φ ψ F j p H := by
  have h := chart_error_majorant (canonicalChart n hn j)
    (normalizedPoints φ F hf) (normalizedHyperplanes φ ψ F hf)
    (fun k _ => normalizedPoints_coordinatePoint φ F hf k)
    (fun k _ => hhyperplanes k) ⟨(p,H),hinc⟩
  have hbad' : ¬ Incident
      (chartRestrictPoint (canonicalChart n hn j) (normalizedPoints φ F hf (chartPoint (canonicalChart n hn j) p)))
      (chartRestrictHyperplane (canonicalChart n hn j) (normalizedHyperplanes φ ψ F hf (chartHyperplane (canonicalChart n hn j) H))) := hbad
  simp only [hbad', if_false] at h
  unfold concreteMajorant rawChartMajorant
  rw [dif_pos hinc]
  let e := Fintype.equivFinOfCardEq (chartSlotIndex_card (canonicalChart n hn j) hn)
  have he : (∑ s : Fin (2*n-3), originalFlagError φ ψ (concreteChartSlot hn j ⟨(p,H),hinc⟩ s F)) =
      ∑ s : ChartSlotIndex (canonicalChart n hn j),
        originalFlagError (normalizedPoints φ F hf) (normalizedHyperplanes φ ψ F hf)
          (chartOriginalSlot (canonicalChart n hn j) ⟨(p,H),hinc⟩ s) := by
    simp only [concreteChartSlot, canonicalSourceFlagSlot, ← normalized_flag_error φ ψ F hf]
    exact e.symm.sum_comp (fun s : ChartSlotIndex (canonicalChart n hn j) =>
      originalFlagError (normalizedPoints φ F hf) (normalizedHyperplanes φ ψ F hf)
        (chartOriginalSlot (canonicalChart n hn j) ⟨(p,H),hinc⟩ s))
  rw [he]
  exact h

theorem concreteGamma_normalized (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) (F : Frame K n) (hf : IsFrame (φ ∘ F.1)) :
    rawGamma concreteGammaSlot (originalFlagError φ ψ) F =
      pencilGamma (normalizedPoints φ F hf) (normalizedHyperplanes φ ψ F hf) := by
  unfold rawGamma pencilGamma pencilFlagSum
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro i hi
  change originalFlagError φ ψ ((frameNormalization F).symm • gammaCanonicalFlag i x) = _
  rw [← normalized_flag_error φ ψ F hf]
  rfl

theorem concreteTotalCost_normalized (hn : 2 ≤ n) (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) (F : Frame K n) (hf : IsFrame (φ ∘ F.1)) :
    pencilGamma (normalizedPoints φ F hf) (normalizedHyperplanes φ ψ F hf) +
      (∑ j, Plane.cost (concreteMajorant hn φ ψ F j)) = concreteTotalCost hn φ ψ F := by
  unfold concreteTotalCost rawTotalCost
  rw [concreteGamma_normalized φ ψ F hf]
  rfl

end Erdos85.IncidenceRepair
