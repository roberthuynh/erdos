import Openmath.IncidenceRepair.FrameAction
import Openmath.IncidenceRepair.CertificateGeometry
import Openmath.IncidenceRepair.GeometryCoupling
import Openmath.IncidenceRepair.FlagAction

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

variable {K : Type*} [Field K] {n : ℕ}

/-- Fixing the standard projective frame forces one common nonzero scalar. -/
theorem scalar_of_fixes_standard_frame
    (A : Coordinates K n ≃ₗ[K] Coordinates K n)
    (hb : ∀ i : Fin (n + 1), A • coordinatePoint (K := K) i = coordinatePoint (K := K) i)
    (ho : A • (onesPoint (K := K) (n := n)) = onesPoint) :
    ∃ c : Kˣ, ∀ v : Coordinates K n, A v = c • v := by
  classical
  have hb' (i : Fin (n + 1)) : ∃ c : Kˣ,
      c • (Pi.single i (1 : K)) = A (Pi.single i 1) := by
    have h := hb i
    change Projectivization.map A.toLinearMap A.injective (coordinatePoint i) = _ at h
    simp only [coordinatePoint, Projectivization.map_mk, LinearEquiv.coe_coe] at h
    exact (Projectivization.mk_eq_mk_iff K _ _ _ _).mp h
  choose d hd using hb'
  have ho' : ∃ c : Kˣ, c • (fun _ : Fin (n + 1) => (1 : K)) =
      A (fun _ => 1) := by
    change Projectivization.map A.toLinearMap A.injective onesPoint = _ at ho
    simp only [onesPoint, Projectivization.map_mk, LinearEquiv.coe_coe] at ho
    exact (Projectivization.mk_eq_mk_iff K _ _ _ _).mp ho
  obtain ⟨c, hc⟩ := ho'
  have hsum : (fun _ : Fin (n + 1) => (1 : K)) = ∑ i, Pi.single i 1 := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hd' (i : Fin (n + 1)) : (d i : K) = (c : K) := by
    have h := congr_fun hc i
    rw [hsum, map_sum] at h
    simp only [← hd, Finset.sum_apply, Pi.smul_apply, Units.smul_def] at h
    simpa [Pi.single_apply] using h.symm
  refine ⟨c, fun v => ?_⟩
  have hv : v = ∑ i, v i • Pi.single i 1 := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    A v = ∑ i, v i • A (Pi.single i 1) := by
      simpa only [map_sum, map_smul] using congrArg A hv
    _ = ∑ i, v i • (c • Pi.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hd]
      simp only [Units.smul_def, hd']
    _ = c • v := by
      calc
        _ = c • ∑ i, v i • Pi.single i 1 := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact smul_comm (v i) c (Pi.single i 1)
        _ = c • v := by rw [← hv]

/-- A projectivity fixing the standard frame fixes every projective point. -/
theorem fixes_standard_frame_pointwise
    (A : Coordinates K n ≃ₗ[K] Coordinates K n)
    (hb : ∀ i : Fin (n + 1), A • coordinatePoint (K := K) i = coordinatePoint (K := K) i)
    (ho : A • (onesPoint (K := K) (n := n)) = onesPoint) :
    ∀ p : Point K n, A • p = p := by
  obtain ⟨c, hc⟩ := scalar_of_fixes_standard_frame A hb ho
  intro p
  induction p using Projectivization.ind with
  | h v hv =>
    change Projectivization.map A.toLinearMap A.injective (Projectivization.mk K v hv) = _
    rw [Projectivization.map_mk]
    exact (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr ⟨c, (hc v).symm⟩

theorem scalar_fixes_sourceFlag (A : Coordinates K n ≃ₗ[K] Coordinates K n)
    (c : Kˣ) (hc : ∀ v : Coordinates K n, A v = c • v) :
    ∀ f : SourceFlag K n, A • f = f := by
  have hinv (v : Coordinates K n) : A.symm v = c⁻¹ • v := by
    apply A.injective
    rw [A.apply_symm_apply, hc]
    simp
  have hdual (v : Coordinates K n) : dualCoordinates A v = c⁻¹ • v := by
    funext i
    have h := dualCoordinates_eval A v (Pi.single i 1)
    rw [hinv] at h
    simpa [dotProduct, Pi.smul_apply, Units.smul_def, Pi.single_apply, mul_comm] using h
  have hpoint (p : Point K n) : A • p = p := by
    induction p using Projectivization.ind with
    | h v hv =>
      rw [Projectivization.smul_mk]
      exact (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr ⟨c, (hc v).symm⟩
  have hhyper (p : Hyperplane K n) : dualCoordinates A • p = p := by
    induction p using Projectivization.ind with
    | h v hv =>
      rw [Projectivization.smul_mk]
      exact (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr ⟨c⁻¹, (hdual v).symm⟩
  intro f
  apply Subtype.ext
  change (A • f.1.1, dualCoordinates A • f.1.2) = f.1
  rw [hpoint, hhyper]

def canonicalSourceFlagSlot (c : SourceFlag K n) (F : Frame K n) : SourceFlag K n :=
  (frameNormalization F).symm • c

/-- The source-coordinate slot is equivariant even though representative and
basis choices in frame normalization need not be literally equivariant. -/
theorem canonicalSourceFlagSlot_equivariant (c : SourceFlag K n)
    (A : Coordinates K n ≃ₗ[K] Coordinates K n) (F : Frame K n) :
    canonicalSourceFlagSlot c (A • F) = A • canonicalSourceFlagSlot c F := by
  let NF := frameNormalization F
  let NG := frameNormalization (A • F)
  let B := NG * A * NF⁻¹
  have hb (i : Fin (n+1)) : B • coordinatePoint (K := K) i = coordinatePoint i := by
    have hf : NF • F.1 i.castSucc = coordinatePoint i := frameNormalization_first F i
    have hi : NF⁻¹ • coordinatePoint i = F.1 i.castSucc := by rw [← hf, inv_smul_smul]
    dsimp [B]
    rw [mul_smul, mul_smul, hi]
    exact frameNormalization_first (A • F) i
  have ho : B • (onesPoint (K := K) (n := n)) = onesPoint := by
    have hf : NF • F.1 (Fin.last (n+1)) = onesPoint := frameNormalization_final F
    have hi : NF⁻¹ • onesPoint = F.1 (Fin.last (n+1)) := by rw [← hf, inv_smul_smul]
    dsimp [B]
    rw [mul_smul, mul_smul, hi]
    exact frameNormalization_final (A • F)
  obtain ⟨s, hs⟩ := scalar_of_fixes_standard_frame B hb ho
  have hfix := scalar_fixes_sourceFlag B s hs c
  change (NG * A * NF⁻¹) • c = c at hfix
  simp only [mul_smul] at hfix
  change NG⁻¹ • c = A • (NF⁻¹ • c)
  calc
    NG⁻¹ • c = NG⁻¹ • (NG • (A • (NF⁻¹ • c))) := congrArg (fun x => NG⁻¹ • x) hfix.symm
    _ = A • (NF⁻¹ • c) := inv_smul_smul NG _

end Erdos85.IncidenceRepair
