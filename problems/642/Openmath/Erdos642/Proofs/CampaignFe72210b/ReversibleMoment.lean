import Openmath.Erdos642.Proofs.CampaignFe72210b.PathMoment

/-! Weighted similarity converts actual finite path moments to Euclidean matrix moments. -/
open scoped Matrix
namespace Erdos642.FiniteMarkov.Chain

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (C : Erdos642.FiniteMarkov.Chain V)

/-- Similarity by multiplication with nonzero vertex weights. -/
noncomputable def similarTransition (u : V → ℝ) : Matrix V V ℝ :=
  fun x y => u x * C.transition x y / u y

/-- Diagonal tilt after the weighted similarity. -/
noncomputable def similarTilt (u d : V → ℝ) : Matrix V V ℝ :=
  fun x y => d x * C.similarTransition u x y * d y

omit [DecidableEq V] in
/-- One-step intertwining, proved directly in each finite summand. -/
theorem similarTilt_mulVec (u d f : V → ℝ) (hu : ∀ x, u x ≠ 0) (x : V) :
    (C.similarTilt u d *ᵥ (fun y => u y * f y)) x =
      u x * (C.tilted d *ᵥ f) x := by
  simp only [Matrix.mulVec, dotProduct, similarTilt, similarTransition, tilted]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  field_simp [hu y]

/-- The intertwining holds for every finite matrix power. -/
theorem similarTilt_pow_mulVec (u d f : V → ℝ) (hu : ∀ x, u x ≠ 0)
    (n : ℕ) (x : V) :
    ((C.similarTilt u d ^ n) *ᵥ (fun y => u y * f y)) x =
      u x * ((C.tilted d ^ n) *ᵥ f) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', ← Matrix.mulVec_mulVec]
    have heq : (C.similarTilt u d ^ n) *ᵥ (fun y => u y * f y) =
        fun y => u y * ((C.tilted d ^ n) *ᵥ f) y := by
      funext y
      exact ih y
    rw [heq]
    exact C.similarTilt_mulVec u d _ hu x

/-- Actual path moments expressed in the Euclidean inner product after similarity. -/
theorem weighted_path_moment (u d : V → ℝ) (hu : ∀ x, u x ≠ 0) (n : ℕ) :
    (∑ x, u x ^ 2 * ∑ p : Erdos642.FiniteMarkov.Path V n,
      C.weight x p * vertexProduct d x p) =
      dotProduct (fun x => u x * d x)
        ((C.similarTilt u d ^ n) *ᵥ (fun x => u x * d x)) := by
  rw [C.initial_path_moment]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro x _
  rw [C.similarTilt_pow_mulVec u d d hu n x]
  ring

end Erdos642.FiniteMarkov.Chain
