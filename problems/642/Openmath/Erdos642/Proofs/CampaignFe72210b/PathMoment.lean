import Openmath.Erdos642.Proofs.CampaignFe72210b.FiniteMarkov

/-! Exact finite path sums for diagonal matrix tilts. -/
open scoped Matrix

namespace Erdos642.FiniteMarkov

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

namespace Chain
variable (C : Chain V)

/-- The two-sided diagonal tilt of a transition matrix. -/
def tilted (d : V → ℝ) : Matrix V V ℝ := fun x y =>
  d x * C.transition x y * d y

/-- The product over all observed vertices, including the initial vertex. -/
def vertexProduct (d : V → ℝ) : {n : ℕ} → V → Path V n → ℝ
  | 0, x, _ => d x ^ 2
  | _ + 1, x, (y, p) => d x ^ 2 * vertexProduct d y p

/-- An exact algebraic identity for actual finite paths. -/
theorem path_moment (d : V → ℝ) (n : ℕ) (x : V) :
    (∑ p : Path V n, C.weight x p * vertexProduct d x p) =
      d x * (((C.tilted d) ^ n) *ᵥ d) x := by
  induction n generalizing x with
  | zero =>
    rw [Fintype.sum_unique]
    simp [weight, vertexProduct, pow_two]
  | succ n ih =>
    change (∑ p : V × Path V n,
      (C.transition x p.1 * C.weight p.1 p.2) *
        (d x ^ 2 * vertexProduct d p.1 p.2)) = _
    rw [Fintype.sum_prod_type]
    conv_rhs => rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, tilted]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    calc
      (∑ p : Path V n, (C.transition x y * C.weight y p) *
          (d x ^ 2 * vertexProduct d y p)) =
          (d x ^ 2 * C.transition x y) *
            ∑ p : Path V n, C.weight y p * vertexProduct d y p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ = _ := by
        rw [ih]
        simp only [Matrix.mulVec, dotProduct]
        ring

/-- The corresponding weighted inner form for any initial coefficients. -/
theorem initial_path_moment (d pi : V → ℝ) (n : ℕ) :
    (∑ x, pi x * ∑ p : Path V n, C.weight x p * vertexProduct d x p) =
      ∑ x, pi x * d x * (((C.tilted d) ^ n) *ᵥ d) x := by
  apply Finset.sum_congr rfl
  intro x _
  rw [C.path_moment]
  ring

/-- Additive potential over every observed vertex, with multiplicity. -/
def vertexSum (f : V → ℝ) : {n : ℕ} → V → Path V n → ℝ
  | 0, x, _ => f x
  | _ + 1, x, (y, p) => f x + vertexSum f y p

noncomputable def exponentialTilt (theta : ℝ) (f : V → ℝ) (x : V) : ℝ :=
  Real.exp (-theta * f x / 2)

omit [Fintype V] [DecidableEq V] in
theorem exponentialTilt_sq (theta : ℝ) (f : V → ℝ) (x : V) :
    exponentialTilt theta f x ^ 2 = Real.exp (-theta * f x) := by
  rw [exponentialTilt, pow_two, ← Real.exp_add]
  congr 1
  ring

omit [Fintype V] [DecidableEq V] in
theorem vertexProduct_exponential (theta : ℝ) (f : V → ℝ)
    {n : ℕ} (x : V) (p : Path V n) :
    vertexProduct (exponentialTilt theta f) x p =
      Real.exp (-theta * vertexSum f x p) := by
  induction n generalizing x with
  | zero => exact exponentialTilt_sq theta f x
  | succ n ih =>
    change exponentialTilt theta f x ^ 2 *
      vertexProduct (exponentialTilt theta f) p.1 p.2 =
        Real.exp (-theta * (f x + vertexSum f p.1 p.2))
    rw [exponentialTilt_sq, ih, ← Real.exp_add]
    congr 1
    ring

/-- Exact exponential moment identity; this asserts no moment bound. -/
theorem exponential_path_moment (theta : ℝ) (f : V → ℝ) (n : ℕ) (x : V) :
    (∑ p : Path V n, C.weight x p * Real.exp (-theta * vertexSum f x p)) =
      exponentialTilt theta f x *
        (((C.tilted (exponentialTilt theta f)) ^ n) *ᵥ exponentialTilt theta f) x := by
  simpa only [vertexProduct_exponential] using C.path_moment (exponentialTilt theta f) n x

end Chain
end Erdos642.FiniteMarkov
