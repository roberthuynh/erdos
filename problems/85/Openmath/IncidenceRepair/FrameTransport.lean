import Openmath.IncidenceRepair.FrameGeometry

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

variable {K : Type*} [Field K] {n : ℕ}

lemma independent_projective_map {ι : Type*} {f : ι → Point K n}
    (hf : Projectivization.Independent f)
    (A : Coordinates K n ≃ₗ[K] Coordinates K n) :
    Projectivization.Independent (fun i => Projectivization.map A.toLinearMap A.injective (f i)) := by
  obtain ⟨v, hv, hi⟩ := hf
  simpa only [Projectivization.map_mk, LinearEquiv.coe_coe] using
    (Projectivization.Independent.mk (fun i => A (v i))
      (fun i => map_ne_zero_iff A A.injective |>.2 (hv i))
      (hi.map' A.toLinearMap (LinearMap.ker_eq_bot.mpr A.injective)))

/-- Invertible linear maps act on actual full ordered frames. -/
def mapFrame (A : Coordinates K n ≃ₗ[K] Coordinates K n) (F : Frame K n) : Frame K n :=
  ⟨fun i => Projectivization.map A.toLinearMap A.injective (F.1 i),
    fun i => independent_projective_map (F.2 i) A⟩

lemma frame_normalizations_equal (F G : Frame K n) (i : Fin (n + 2)) :
    (mapFrame (frameNormalization F) F).1 i =
      (mapFrame (frameNormalization G) G).1 i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact (frameNormalization_final F).trans (frameNormalization_final G).symm
  · exact (frameNormalization_first F j).trans (frameNormalization_first G j).symm

lemma projective_map_trans (A B : Coordinates K n ≃ₗ[K] Coordinates K n) (p : Point K n) :
    Projectivization.map (A.trans B).toLinearMap (A.trans B).injective p =
      Projectivization.map B.toLinearMap B.injective
        (Projectivization.map A.toLinearMap A.injective p) := by
  induction p using Projectivization.ind with
  | h v hv => rfl

lemma projective_map_symm_apply (A : Coordinates K n ≃ₗ[K] Coordinates K n) (p : Point K n) :
    Projectivization.map A.symm.toLinearMap A.symm.injective
      (Projectivization.map A.toLinearMap A.injective p) = p := by
  induction p using Projectivization.ind with
  | h v hv =>
    simp only [Projectivization.map_mk, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- Any two actual ordered full frames are related by one invertible linear map. -/
theorem exists_frame_transport (F G : Frame K n) :
    ∃ A : Coordinates K n ≃ₗ[K] Coordinates K n, mapFrame A F = G := by
  refine ⟨(frameNormalization F).trans (frameNormalization G).symm, ?_⟩
  apply Subtype.ext
  funext i
  change Projectivization.map ((frameNormalization F).trans (frameNormalization G).symm).toLinearMap
    ((frameNormalization F).trans (frameNormalization G).symm).injective (F.1 i) = G.1 i
  rw [projective_map_trans]
  have h := frame_normalizations_equal F G i
  change Projectivization.map (frameNormalization F).toLinearMap (frameNormalization F).injective (F.1 i) =
    Projectivization.map (frameNormalization G).toLinearMap (frameNormalization G).injective (G.1 i) at h
  rw [h, projective_map_symm_apply]

end Erdos85.IncidenceRepair
