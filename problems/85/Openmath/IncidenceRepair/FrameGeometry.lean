import Openmath.IncidenceRepair.Geometry

noncomputable section
open scoped BigOperators
open Module
namespace Erdos85.IncidenceRepair

variable {K : Type*} [Field K] {n : ℕ}

lemma frame_first_independent (F : Frame K n) :
    LinearIndependent K (fun i : Fin (n + 1) => (F.1 i.castSucc).rep) := by
  have h := Projectivization.independent_iff.mp (F.2 (Fin.last (n + 1)))
  let e : Fin (n + 1) → {j : Fin (n + 2) // j ≠ Fin.last (n + 1)} :=
    fun i => ⟨i.castSucc, Fin.castSucc_ne_last i⟩
  exact h.comp e (by intro i j hij; exact Fin.castSucc_injective _ (congrArg Subtype.val hij))

/-- The first n+1 representatives of an actual full frame form a vector basis. -/
def frameBasis (F : Frame K n) : Basis (Fin (n + 1)) K (Coordinates K n) :=
  by classical exact basisOfPiSpaceOfLinearIndependent (frame_first_independent F)

@[simp] lemma frameBasis_apply (F : Frame K n) (i : Fin (n + 1)) :
    frameBasis F i = (F.1 i.castSucc).rep := by
  simp [frameBasis]

/-- Every coordinate of the last frame point in that basis is nonzero. -/
lemma frame_last_coordinate_ne_zero (F : Frame K n) (i : Fin (n + 1)) :
    (frameBasis F).repr (F.1 (Fin.last (n + 1))).rep i ≠ 0 := by
  classical
  intro hz
  let v := (F.1 (Fin.last (n + 1))).rep
  let J := {j : Fin (n + 2) // j ≠ i.castSucc}
  let z : J := ⟨Fin.last (n + 1), (Fin.castSucc_ne_last i).symm⟩
  let w : J → Coordinates K n := fun j => (F.1 j).rep
  have hw : LinearIndependent K w :=
    Projectivization.independent_iff.mp (F.2 i.castSucc)
  apply hw.notMem_span z
  change v ∈ Submodule.span K (w '' {z}ᶜ)
  rw [← (frameBasis F).sum_repr v]
  apply Submodule.sum_mem
  intro j hj
  by_cases heq : j = i
  · subst j
    rw [hz, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨⟨j.castSucc, ?_⟩, ?_, ?_⟩
    · intro he
      exact heq (Fin.castSucc_injective _ he)
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro he
      exact Fin.castSucc_ne_last j (congrArg Subtype.val he)
    · simp [w, frameBasis_apply]

/-- Rescaled basis whose sum is precisely the final frame representative. -/
def normalizedFrameBasis (F : Frame K n) : Basis (Fin (n + 1)) K (Coordinates K n) :=
  (frameBasis F).unitsSMul (fun i => Units.mk0
    ((frameBasis F).repr (F.1 (Fin.last (n + 1))).rep i)
    (frame_last_coordinate_ne_zero F i))

lemma normalizedFrameBasis_sum (F : Frame K n) :
    ∑ i, normalizedFrameBasis F i = (F.1 (Fin.last (n + 1))).rep := by
  simpa [normalizedFrameBasis, Basis.unitsSMul_apply, Units.smul_def]
    using (frameBasis F).sum_repr (F.1 (Fin.last (n + 1))).rep

/-- Actual invertible linear normalization determined by the ordered frame. -/
def frameNormalization (F : Frame K n) : Coordinates K n ≃ₗ[K] Coordinates K n :=
  (normalizedFrameBasis F).equivFun

lemma frameNormalization_basis (F : Frame K n) (i : Fin (n + 1)) :
    frameNormalization F (normalizedFrameBasis F i) = Pi.single i 1 := by
  classical
  ext j
  simp [frameNormalization, Basis.equivFun_self, Pi.single_apply, eq_comm]

lemma frameNormalization_last (F : Frame K n) :
    frameNormalization F (F.1 (Fin.last (n + 1))).rep = (fun _ => 1) := by
  classical
  rw [← normalizedFrameBasis_sum F, map_sum]
  simp only [frameNormalization_basis]
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

lemma normalizedFrameBasis_projective (F : Frame K n) (i : Fin (n + 1)) :
    Projectivization.mk K (normalizedFrameBasis F i) ((normalizedFrameBasis F).ne_zero i) =
      F.1 i.castSucc := by
  rw [← Projectivization.mk_rep (F.1 i.castSucc)]
  apply (Projectivization.mk_eq_mk_iff K _ _ _ _).2
  refine ⟨Units.mk0 ((frameBasis F).repr (F.1 (Fin.last (n + 1))).rep i)
    (frame_last_coordinate_ne_zero F i), ?_⟩
  simp [normalizedFrameBasis, Basis.unitsSMul_apply]

lemma frameNormalization_first (F : Frame K n) (i : Fin (n + 1)) :
    Projectivization.map (frameNormalization F).toLinearMap (frameNormalization F).injective
      (F.1 i.castSucc) =
      Projectivization.mk K (Pi.single i 1) (by
        classical
        intro h
        have := congr_fun h i
        simp at this) := by
  rw [← normalizedFrameBasis_projective F i, Projectivization.map_mk]
  congr 1
  exact frameNormalization_basis F i

lemma frameNormalization_final (F : Frame K n) :
    Projectivization.map (frameNormalization F).toLinearMap (frameNormalization F).injective
      (F.1 (Fin.last (n + 1))) =
      Projectivization.mk K (fun _ : Fin (n + 1) => 1) (by
        intro h
        have := congr_fun h 0
        simp at this) := by
  rw [← Projectivization.mk_rep (F.1 (Fin.last (n + 1))), Projectivization.map_mk]
  congr 1
  exact frameNormalization_last F

end Erdos85.IncidenceRepair
