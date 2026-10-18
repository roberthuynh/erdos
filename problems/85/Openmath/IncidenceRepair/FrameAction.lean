import Openmath.IncidenceRepair.FrameTransport

noncomputable section
namespace Erdos85.IncidenceRepair
variable {K : Type*} [Field K] {n : ℕ}

/-- The actual linear group action on ordered projective frames. -/
instance frameMulAction : MulAction (Coordinates K n ≃ₗ[K] Coordinates K n) (Frame K n) where
  smul := mapFrame
  one_smul F := by
    apply Subtype.ext
    funext i
    change (1 : Coordinates K n ≃ₗ[K] Coordinates K n) • F.1 i = F.1 i
    exact one_smul _ _
  mul_smul A B F := by
    apply Subtype.ext
    funext i
    change (A * B) • F.1 i = A • (B • F.1 i)
    exact mul_smul _ _ _

instance framePretransitive :
    MulAction.IsPretransitive (Coordinates K n ≃ₗ[K] Coordinates K n) (Frame K n) where
  exists_smul_eq F G := exists_frame_transport F G

end Erdos85.IncidenceRepair
