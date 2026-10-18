import Openmath.IncidenceRepair.NormalizedMaps
import Openmath.IncidenceRepair.InitialCertificate
import Openmath.IncidenceRepair.ProtectedCertificate
import Openmath.IncidenceRepair.CanonicalCharts
import Openmath.IncidenceRepair.SharedPencil
import Openmath.IncidenceRepair.ChartBaseFromInitial
import Openmath.IncidenceRepair.ChartCost
import Openmath.IncidenceRepair.FrameEquivariance
import Openmath.IncidenceRepair.FlagCounts
import Openmath.IncidenceRepair.AffineGeometry

noncomputable section
open scoped BigOperators Classical
namespace Erdos85.IncidenceRepair
variable {K L : Type*} [Field K] [Field L] {n : ℕ}

def concreteChartSlot (hn : 2 ≤ n) (j : Fin (n - 1)) (ph : PlaneFlag K)
    (s : Fin (2 * n - 3)) (F : Frame K n) : SourceFlag K n :=
  canonicalSourceFlagSlot (chartOriginalSlot (canonicalChart n hn j) ph
    ((Fintype.equivFinOfCardEq (chartSlotIndex_card (canonicalChart n hn j) hn)).symm s)) F

def gammaCanonicalFlag (i : Fin n) (x : Fin n → K) : SourceFlag K n :=
  ⟨(affinePoint x, pencilHyperplane i.succ (Fin.succ_ne_zero i) (x i)), by
    unfold Incident affinePoint pencilHyperplane
    rw [Projectivization.orthogonal_mk]
    rw [dotProduct_sub, dotProduct_smul, dotProduct_single, dotProduct_single]
    simp [affineVector]⟩

def concreteGammaSlot (i : Fin n) (x : Fin n → K) (F : Frame K n) : SourceFlag K n :=
  canonicalSourceFlagSlot (gammaCanonicalFlag i x) F

def concreteCertificateFlag (hn : 2 ≤ n) : CertificateSlots n → SourceFlag K n
  | .inl s => initialCertificateFlag
      ((Fintype.equivFinOfCardEq (by
        simpa [pow_two, mul_assoc] using initialCertificateSlot_card n hn)).symm s)
  | .inr js => extraCertificateFlag (canonicalChart n hn js.1)
      ((Fintype.equivFinOfCardEq (by
        rw [Fintype.card_eq_nat_card]
        exact extraCertificateSlot_card _ hn)).symm js.2)

def concreteCertificateSlot (hn : 2 ≤ n) (s : CertificateSlots n) (F : Frame K n) : SourceFlag K n :=
  canonicalSourceFlagSlot (concreteCertificateFlag hn s) F

variable [Fintype K] [Finite L]

def concreteTotalCost (hn : 2 ≤ n) (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) (F : Frame K n) : ℝ :=
  rawTotalCost (concreteChartSlot hn) concreteGammaSlot (originalFlagError φ ψ) F

theorem concreteTotalCost_nonneg (hn : 2 ≤ n) (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) (F : Frame K n) : 0 ≤ concreteTotalCost hn φ ψ F := by
  letI : Fintype (Frame K n) := Fintype.ofFinite _
  letI : Fintype (SourceFlag K n) := Fintype.ofFinite _
  letI : Nonempty (Frame K n) := ⟨F⟩
  letI : Nonempty (SourceFlag K n) := sourceFlag_nonempty (by omega)
  exact rawTotalCost_nonneg _ _ _ (originalFlagError_nonneg φ ψ) F

theorem originalFlagError_average [Fintype (SourceFlag K n)]
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) :
    (∑ f : SourceFlag K n, originalFlagError φ ψ f) / Fintype.card (SourceFlag K n) =
      errorDensity φ ψ := by
  simpa only [originalFlagError, sourceFlagError, ite_not] using sourceFlagError_average φ ψ

theorem concreteTotalCost_average [Fintype (Frame K n)] [Nonempty (Frame K n)]
    [Fintype (SourceFlag K n)] [Nonempty (SourceFlag K n)]
    (hn : 2 ≤ n) (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) :
    (∑ F, concreteTotalCost hn φ ψ F) / Fintype.card (Frame K n) ≤
      48 * (n : ℝ)^2 * errorDensity φ ψ := by
  rw [← originalFlagError_average φ ψ]
  apply average_total_cost_le (G := Coordinates K n ≃ₗ[K] Coordinates K n) hn
  · intro j ph s A F
    exact canonicalSourceFlagSlot_equivariant _ A F
  · intro i x A F
    exact canonicalSourceFlagSlot_equivariant _ A F
  · exact originalFlagError_nonneg φ ψ

/-- Select one actual surviving frame using costs counted on ALL source frames.
The concrete certificate slots and chart/gamma slots have no free suppliers. -/
theorem exists_selected_raw_frame (hn : 2 ≤ n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (hρ : 0 < frameSurvival φ)
    (hsmall : errorDensity φ ψ ≤ frameSurvival φ / (1000000000 * (n : ℝ)^2)) :
    ∃ F : Frame K n, IsFrame (φ ∘ F.1) ∧
      (∀ s : CertificateSlots n,
        Incident (φ (concreteCertificateSlot hn s F).1.1)
          (ψ (concreteCertificateSlot hn s F).1.2)) ∧
      concreteTotalCost hn φ ψ F ≤ (1 : ℝ) / 10000000 := by
  classical
  letI : Fintype (Frame K n) := Fintype.ofFinite _
  letI : Fintype (SourceFlag K n) := Fintype.ofFinite _
  letI : Nonempty (Frame K n) := by
    by_contra hnemp
    haveI : IsEmpty (Frame K n) := not_nonempty_iff.mp hnemp
    simpa [frameSurvival] using hρ
  letI : Nonempty (SourceFlag K n) := sourceFlag_nonempty (by omega)
  let surviving : Finset (Frame K n) := Finset.univ.filter (fun F => IsFrame (φ ∘ F.1))
  let bad : SourceFlag K n → Prop := fun f => ¬ Incident (φ f.1.1) (ψ f.1.2)
  let failed : Finset (Frame K n) := Finset.univ.filter
    (fun F => ∃ s : CertificateSlots n, bad (concreteCertificateSlot hn s F))
  have hmean : ((Finset.univ.filter bad).card : ℝ) / Fintype.card (SourceFlag K n) =
      errorDensity φ ψ := by
    rw [← sourceFlagError_average φ ψ]
    congr 1
    exact Finset.natCast_card_filter bad Finset.univ
  have hfailed : (failed.card : ℝ) / Fintype.card (Frame K n) ≤
      7 * (n : ℝ)^2 * errorDensity φ ψ := by
    rw [← hmean]
    exact certificate_failure_bound (G := Coordinates K n ≃ₗ[K] Coordinates K n) hn
      (concreteCertificateSlot hn)
      (fun s A F => canonicalSourceFlagSlot_equivariant _ A F) bad
  obtain ⟨F,hFs,hFgood,hcost⟩ := exists_surviving_good_normalized
    surviving failed (concreteTotalCost hn φ ψ) n (frameSurvival φ) (errorDensity φ ψ) hn
    (by simp [frameSurvival, surviving, Nat.card_eq_fintype_card, Fintype.card_subtype])
    hρ (concreteTotalCost_nonneg hn φ ψ) hfailed (concreteTotalCost_average hn φ ψ) hsmall
  refine ⟨F, (Finset.mem_filter.mp hFs).2, ?_, hcost⟩
  have hnot : ¬ ∃ s : CertificateSlots n, bad (concreteCertificateSlot hn s F) := by
    simpa [failed] using hFgood
  intro s
  by_contra h
  exact hnot ⟨s,h⟩

theorem normalized_initial_good (hn : 2 ≤ n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (F : Frame K n) (hf : IsFrame (φ ∘ F.1))
    (hgood : ∀ s : CertificateSlots n,
      Incident (φ (concreteCertificateSlot hn s F).1.1)
        (ψ (concreteCertificateSlot hn s F).1.2)) :
    ∀ t : InitialCertificateSlot n,
      Incident (normalizedPoints φ F hf (initialCertificateFlag t).1.1)
        (normalizedHyperplanes φ ψ F hf (initialCertificateFlag t).1.2) := by
  intro t
  let e := Fintype.equivFinOfCardEq (show Fintype.card (InitialCertificateSlot n) = 2*n*n+n by
    simpa [pow_two, mul_assoc] using initialCertificateSlot_card n hn)
  have h := hgood (.inl (e t))
  have hz : originalFlagError φ ψ (concreteCertificateSlot hn (.inl (e t)) F) = 0 := by simp [originalFlagError, h]
  have heq := normalized_flag_error φ ψ F hf (initialCertificateFlag t)
  have hz' : originalFlagError (normalizedPoints φ F hf) (normalizedHyperplanes φ ψ F hf) (initialCertificateFlag t) = 0 := by
    rw [heq]
    simpa only [concreteCertificateSlot, concreteCertificateFlag, e, Equiv.symm_apply_apply, canonicalSourceFlagSlot] using hz
  simpa [originalFlagError] using hz'

theorem normalized_extra_good (hn : 2 ≤ n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (F : Frame K n) (hf : IsFrame (φ ∘ F.1))
    (hgood : ∀ s : CertificateSlots n,
      Incident (φ (concreteCertificateSlot hn s F).1.1)
        (ψ (concreteCertificateSlot hn s F).1.2))
    (j : Fin (n - 1)) :
    ∀ t : ExtraCertificateSlot (canonicalChart n hn j),
      Incident (normalizedPoints φ F hf (extraCertificatePair (canonicalChart n hn j) t).1)
        (normalizedHyperplanes φ ψ F hf (extraCertificatePair (canonicalChart n hn j) t).2) := by
  intro t
  let e := Fintype.equivFinOfCardEq (show Fintype.card (ExtraCertificateSlot (canonicalChart n hn j)) = 5*n by
    rw [Fintype.card_eq_nat_card]; exact extraCertificateSlot_card _ hn)
  have h := hgood (.inr (j, e t))
  have hz : originalFlagError φ ψ (concreteCertificateSlot hn (.inr (j,e t)) F) = 0 := by simp [originalFlagError, h]
  have heq := normalized_flag_error φ ψ F hf (extraCertificateFlag (canonicalChart n hn j) t)
  have hz' : originalFlagError (normalizedPoints φ F hf) (normalizedHyperplanes φ ψ F hf) (extraCertificateFlag (canonicalChart n hn j) t) = 0 := by
    rw [heq]
    simpa only [concreteCertificateSlot, concreteCertificateFlag, e, Equiv.symm_apply_apply, canonicalSourceFlagSlot] using hz
  by_contra hbad
  simp [originalFlagError, extraCertificateFlag, hbad] at hz'

/-- The actual selected frame supplies all normalized protected charts and the
published 10^-7 total-cost budget. No abstract geometric or averaging inputs remain. -/
theorem exists_normalized_protected_frame (hn : 2 ≤ n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (hρ : 0 < frameSurvival φ)
    (hsmall : errorDensity φ ψ ≤ frameSurvival φ / (1000000000 * (n : ℝ)^2)) :
    ∃ (F : Frame K n) (hf : IsFrame (φ ∘ F.1)),
      (∀ i, normalizedHyperplanes φ ψ F hf (coordinateHyperplane i) = coordinateHyperplane i) ∧
      (∀ (i : Fin (n+1)) (hi : i ≠ 0),
        normalizedHyperplanes φ ψ F hf (pencilHyperplane i hi 1) = pencilHyperplane i hi 1) ∧
      (∀ j : Fin (n-1), Plane.Protected
        (inducedPointMap (canonicalChart n hn j) (normalizedPoints φ F hf))
        (inducedHyperplaneMap (canonicalChart n hn j) (normalizedHyperplanes φ ψ F hf))) ∧
      concreteTotalCost hn φ ψ F ≤ (1 : ℝ) / 10000000 := by
  obtain ⟨F,hf,hgood,hcost⟩ := exists_selected_raw_frame hn φ ψ hρ hsmall
  have hinit := initial_certificate_forces (normalizedPoints φ F hf)
    (normalizedHyperplanes φ ψ F hf) (normalizedPoints_coordinatePoint φ F hf)
    (normalizedPoints_onesPoint φ F hf) (normalized_initial_good hn φ ψ F hf hgood)
  refine ⟨F,hf,hinit.1,hinit.2,?_,hcost⟩
  intro j
  apply protected_of_good_extra_slots
  · exact chartBase_from_initial (canonicalChart n hn j) (canonicalChart_two n hn j)
      _ _ (normalizedPoints_coordinatePoint φ F hf) hinit.1 hinit.2
  · exact normalized_extra_good hn φ ψ F hf hgood j

end Erdos85.IncidenceRepair
