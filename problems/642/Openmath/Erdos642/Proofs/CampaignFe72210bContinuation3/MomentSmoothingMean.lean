import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentSmoothing

/-! Retention of the actual stationary root and exact projected means. -/
namespace Erdos642.CampaignFe72210bContinuation3.MomentSmoothingMean
open Matrix Erdos642.CampaignFe72210b Erdos642.FiniteMarkov
open Erdos642.CampaignFe72210bContinuation3.MomentSmoothing
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem fixed_vector_mem_slowSpace (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (w : EuclideanSpace ℝ V) (hw : A.toEuclideanLin w = w) :
    w ∈ slowSpace A hA := by
  classical
  have hs : A.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hc (j : V) (hj : j ∉ slowIndices A hA) : inner ℝ (hA.eigenvectorBasis j) w = 0 := by
    have hj' : hA.eigenvalues j < (1 : ℝ) / 4 := by simpa [slowIndices] using hj
    have he := hermitian_canonical_eigen_equation A hA j
    have hh : inner ℝ (hA.eigenvectorBasis j) w =
        hA.eigenvalues j * inner ℝ (hA.eigenvectorBasis j) w := by
      nth_rw 1 [← hw]
      rw [← hs, he, inner_smul_left]
      rfl
    nlinarith
  rw [← hA.eigenvectorBasis.sum_repr' w]
  apply Submodule.sum_mem
  intro j _
  by_cases hj : j ∈ slowIndices A hA
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  · rw [hc j hj, zero_smul]
    exact Submodule.zero_mem _

omit [DecidableEq V] in
theorem similarTransition_fixes_root (C : Chain V) (u : V → ℝ) (hu : ∀ x, 0 < u x) :
    C.similarTransition u *ᵥ u = u := by
  funext x
  change (∑ y, (u x * C.transition x y / u y) * u y) = u x
  simp_rw [div_mul_cancel₀ _ (ne_of_gt (hu _))]
  rw [← Finset.mul_sum, C.row_sum, mul_one]

theorem stationary_root_mem_slowSpace (C : Chain V) (u : V → ℝ) (hu : ∀ x, 0 < u x)
    (hA : (C.similarTransition u).IsHermitian) :
    WithLp.toLp 2 u ∈ slowSpace (C.similarTransition u) hA := by
  apply fixed_vector_mem_slowSpace
  apply PiLp.ext
  intro x
  exact congrFun (similarTransition_fixes_root C u hu) x

omit [DecidableEq V] in
private theorem root_inner_weightedVec (u f : V → ℝ) :
    inner ℝ (WithLp.toLp 2 u) (CoordinateGrid.weightedVec u f) = ∑ x, u x ^ 2 * f x := by
  change (∑ x, (u x * f x) * u x) = _
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [DecidableEq V] in
theorem transition_stationary_mean (C : Chain V) (u f : V → ℝ)
    (hstat : ∀ y, ∑ x, u x ^ 2 * C.transition x y = u y ^ 2) :
    (∑ x, u x ^ 2 * (C.transition *ᵥ f) x) = ∑ x, u x ^ 2 * f x := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [hstat]

theorem power_stationary_mean (C : Chain V) (u : V → ℝ)
    (hstat : ∀ y, ∑ x, u x ^ 2 * C.transition x y = u y ^ 2)
    (r : ℕ) (f : V → ℝ) :
    (∑ x, u x ^ 2 * ((C.transition ^ r) *ᵥ f) x) = ∑ x, u x ^ 2 * f x := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, transition_stationary_mean C u _ hstat, ih]

theorem projectedFunction_mean (C : Chain V) (u : V → ℝ) (hu : ∀ x, 0 < u x)
    (hA : (C.similarTransition u).IsHermitian) (r : ℕ) (f : V → ℝ) :
    (∑ x, u x ^ 2 * CoordinateGrid.projectedFunction C u
      (slowSpace (C.similarTransition u) hA) r f x) = ∑ x, u x ^ 2 * f x := by
  let E := slowSpace (C.similarTransition u) hA
  have hr := stationary_root_mem_slowSpace C u hu hA
  have hh := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (⟨WithLp.toLp 2 u, hr⟩ : E) (CoordinateGrid.weightedVec u ((C.transition ^ r) *ᵥ f))
  change inner ℝ (WithLp.toLp 2 u)
    ((E.orthogonalProjectionOnto (CoordinateGrid.weightedVec u ((C.transition ^ r) *ᵥ f)) :
      EuclideanSpace ℝ V)) =
    inner ℝ (WithLp.toLp 2 u) (CoordinateGrid.weightedVec u ((C.transition ^ r) *ᵥ f)) at hh
  rw [← CoordinateGrid.weightedVec_projectedFunction C u hu] at hh
  simp only [root_inner_weightedVec] at hh
  exact hh.trans (power_stationary_mean C u (C.similarTransition_stationary u hu hA) r f)

theorem projectedFunction_residual_mean (C : Chain V) (u : V → ℝ) (hu : ∀ x, 0 < u x)
    (hA : (C.similarTransition u).IsHermitian) (r : ℕ) (f : V → ℝ) :
    (∑ x, u x ^ 2 * (((C.transition ^ r) *ᵥ f) x -
      CoordinateGrid.projectedFunction C u (slowSpace (C.similarTransition u) hA) r f x)) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, projectedFunction_mean C u hu hA,
    power_stationary_mean C u (C.similarTransition_stationary u hu hA) r f, sub_self]

section Graph
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (s : Set V) [DecidablePred (· ∈ s)] [Nonempty s]

theorem shore_projectedFunction_mean (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) (r : ℕ) (f : s → ℝ) :
    (∑ x, shoreRoot G s x ^ 2 * CoordinateGrid.projectedFunction
      (shoreChain G s t hbi hdeg) (shoreRoot G s)
      (slowSpace _ (shore_similarity_hermitian G s t hbi hdeg)) r f x) =
      ∑ x, shoreRoot G s x ^ 2 * f x := by
  exact projectedFunction_mean _ _ (shoreRoot_pos G s t hbi hdeg) _ r f
end Graph
end Erdos642.CampaignFe72210bContinuation3.MomentSmoothingMean
