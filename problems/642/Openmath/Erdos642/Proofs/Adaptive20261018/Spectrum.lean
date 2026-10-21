import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentSmoothingMean

/-! Adaptive spectral cutoff, rank and diagonal residual on actual chains. -/
namespace Erdos642.Adaptive20261018.Spectrum
open Matrix Erdos642.CampaignFe72210b Erdos642.FiniteMarkov
open Erdos642.CampaignFe72210bContinuation3
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def slowIndices (A : Matrix V V ℝ) (hA : A.IsHermitian) (θ : ℝ) : Finset V :=
  Finset.univ.filter (fun j => θ ≤ hA.eigenvalues j)
noncomputable def slowSpace (A : Matrix V V ℝ) (hA : A.IsHermitian) (θ : ℝ) :
    Submodule ℝ (EuclideanSpace ℝ V) :=
  Submodule.span ℝ (↑((slowIndices A hA θ).image hA.eigenvectorBasis) : Set _)
noncomputable def slowBasis (A : Matrix V V ℝ) (hA : A.IsHermitian) (θ : ℝ) :
    OrthonormalBasis (slowIndices A hA θ) ℝ (slowSpace A hA θ) :=
  OrthonormalBasis.span hA.eigenvectorBasis.orthonormal (slowIndices A hA θ)
@[simp] theorem slowBasis_apply (A : Matrix V V ℝ) (hA : A.IsHermitian) (θ : ℝ)
    (j : slowIndices A hA θ) : (slowBasis A hA θ j : EuclideanSpace ℝ V) =
      hA.eigenvectorBasis j := by
  exact OrthonormalBasis.span_apply _ _ _
theorem slowSpace_finrank (A : Matrix V V ℝ) (hA : A.IsHermitian) (θ : ℝ) :
    Module.finrank ℝ (slowSpace A hA θ) = (slowIndices A hA θ).card := by
  rw [Module.finrank_eq_card_basis (slowBasis A hA θ).toBasis]
  simp
noncomputable def slowFinBasis (A : Matrix V V ℝ) (hA : A.IsHermitian) (θ : ℝ) :
    OrthonormalBasis (Fin (slowIndices A hA θ).card) ℝ (slowSpace A hA θ) :=
  (slowBasis A hA θ).reindex (slowIndices A hA θ).equivFin
theorem slowSpace_finrank_le (A : Matrix V V ℝ) (hA : A.IsHermitian) (θ : ℝ) :
    Module.finrank ℝ (slowSpace A hA θ) ≤ Fintype.card V := by
  rw [slowSpace_finrank]
  exact Finset.card_le_univ _
theorem slow_projection_eq_sum (A : Matrix V V ℝ) (hA : A.IsHermitian) (θ : ℝ)
    (z : EuclideanSpace ℝ V) :
    ((slowSpace A hA θ).orthogonalProjectionOnto z : EuclideanSpace ℝ V) =
      ∑ j ∈ slowIndices A hA θ, inner ℝ (hA.eigenvectorBasis j) z • hA.eigenvectorBasis j := by
  have hh := (slowBasis A hA θ).orthogonalProjectionOnto_apply_eq_sum z
  have hc := congrArg (fun y : slowSpace A hA θ => (y : EuclideanSpace ℝ V)) hh
  simp only [Submodule.coe_sum, Submodule.coe_smul, slowBasis_apply] at hc
  exact hc.trans (Finset.sum_coe_sort (slowIndices A hA θ)
    (fun j => inner ℝ (hA.eigenvectorBasis j) z • hA.eigenvectorBasis j))

theorem squared_trace_eq_eigen_energy (A : Matrix V V ℝ) (hA : A.IsHermitian) (θ : ℝ) :
    (∑ x, (A ^ 2) x x) = ∑ j, hA.eigenvalues j ^ 2 := by
  simp_rw [hermitian_pow_entry A hA 2]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hn := hA.eigenvectorBasis.orthonormal.norm_eq_one j
  have he : (∑ x, (hA.eigenvectorBasis j x) ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hn]
    norm_num
  calc
    _ = hA.eigenvalues j ^ 2 * ∑ x, hA.eigenvectorBasis j x ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [he, mul_one]

theorem slow_rank_trace_bound (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (θ : ℝ) (hθ : 0 < θ) :
    (Module.finrank ℝ (slowSpace A hA θ) : ℝ) * θ^2 ≤ ∑ x, (A^2) x x := by
  rw [slowSpace_finrank A hA θ, squared_trace_eq_eigen_energy A hA θ]
  have hl : (slowIndices A hA θ).card * θ^2 ≤
      ∑ j ∈ slowIndices A hA θ, hA.eigenvalues j ^ 2 := by
    calc
      _ = ∑ _j ∈ slowIndices A hA θ, θ^2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hh : θ ≤ hA.eigenvalues j := by simpa [slowIndices] using hj
        nlinarith
  exact hl.trans (Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg (hA.eigenvalues j)))

theorem slow_rank_diagonal_bound (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (θ : ℝ) (hθ : 0 < θ) (d Λ : ℝ)
    (hdiag : ∀ x, (A^2) x x ≤ Λ / d^2) :
    (Module.finrank ℝ (slowSpace A hA θ) : ℝ) ≤
      Λ * (Fintype.card V : ℝ) / (d^2 * θ^2) := by
  have hh := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset V)) => hdiag x)
  have ht := slow_rank_trace_bound A hA θ hθ
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  have hb : (Module.finrank ℝ (slowSpace A hA θ) : ℝ) ≤
      ((Fintype.card V : ℝ) * (Λ/d^2)) / θ^2 :=
    (le_div_iff₀ (sq_pos_of_pos hθ)).mpr (ht.trans hh)
  convert hb using 1 <;> ring

theorem power_complement_entry (A : Matrix V V ℝ) (hA : A.IsHermitian) (θ : ℝ)
    (F : EuclideanSpace ℝ V) (r : ℕ) (x : V) :
    ((A ^ r).toEuclideanLin F -
      ((slowSpace A hA θ).orthogonalProjectionOnto ((A ^ r).toEuclideanLin F) :
        EuclideanSpace ℝ V)) x =
      ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j < θ),
        hA.eigenvalues j ^ r * inner ℝ (hA.eigenvectorBasis j) F * hA.eigenvectorBasis j x := by
  classical
  let z := (A ^ r).toEuclideanLin F
  have hs : (A ^ r).toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.pow r)
  have hc (j : V) : inner ℝ (hA.eigenvectorBasis j) z =
      hA.eigenvalues j ^ r * inner ℝ (hA.eigenvectorBasis j) F := by
    have he : (A ^ r).toEuclideanLin (hA.eigenvectorBasis j) =
        hA.eigenvalues j ^ r • hA.eigenvectorBasis j := by
      apply PiLp.ext
      intro y
      exact congrFun (Erdos642.QuadraticPower.power_eigenvector A hA r j) y
    rw [show z = (A ^ r).toEuclideanLin F by rfl, ← hs, he, inner_smul_left]
    rfl
  have hsplit : z =
      (∑ j ∈ slowIndices A hA θ, inner ℝ (hA.eigenvectorBasis j) z • hA.eigenvectorBasis j) +
      ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j < θ),
        inner ℝ (hA.eigenvectorBasis j) z • hA.eigenvectorBasis j := by
    nth_rw 1 [← hA.eigenvectorBasis.sum_repr' z]
    simpa only [slowIndices, not_le] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j => θ ≤ hA.eigenvalues j)
        (fun j => inner ℝ (hA.eigenvectorBasis j) z • hA.eigenvectorBasis j)).symm
  have he : z - ((slowSpace A hA θ).orthogonalProjectionOnto z : EuclideanSpace ℝ V) =
      ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j < θ),
        inner ℝ (hA.eigenvectorBasis j) z • hA.eigenvectorBasis j := by
    rw [slow_projection_eq_sum]
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hsplit)
  have hx := congrArg (fun w : EuclideanSpace ℝ V => w x) he
  simpa only [PiLp.sub_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, hc] using hx

theorem power_complement_bound (A : Matrix V V ℝ) (hA : A.IsHermitian) (θ : ℝ) (hθ : 0 < θ)
    (hpos : A.PosSemidef) (F : EuclideanSpace ℝ V) (hF : ‖F‖ ^ 2 ≤ 1)
    (r : ℕ) (hr : 1 ≤ r) (x : V) :
    |((A ^ r).toEuclideanLin F -
      ((slowSpace A hA θ).orthogonalProjectionOnto ((A ^ r).toEuclideanLin F) :
        EuclideanSpace ℝ V)) x| ≤
      θ ^ (r - 1) * Real.sqrt ((A ^ 2) x x) := by
  classical
  rw [power_complement_entry]
  let K := Finset.univ.filter (fun j => hA.eigenvalues j < θ)
  have hc : (∑ j ∈ K, (inner ℝ (hA.eigenvectorBasis j) F) ^ 2) ≤ 1 := by
    apply le_trans (Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg
      (inner ℝ (hA.eigenvectorBasis j) F)))
    rw [hA.eigenvectorBasis.sum_sq_inner_right]
    exact hF
  have he : (∑ j ∈ K, (hA.eigenvalues j * hA.eigenvectorBasis j x) ^ 2) ≤
      (A ^ 2) x x := by
    rw [← hermitian_eigenbasis_energy_eq_diagonal A hA x]
    exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg
      (hA.eigenvalues j * hA.eigenvectorBasis j x))
  have ht (j : V) (hj : j ∈ K) :
      |hA.eigenvalues j ^ r * inner ℝ (hA.eigenvectorBasis j) F * hA.eigenvectorBasis j x| ≤
      θ ^ (r - 1) *
        (|inner ℝ (hA.eigenvectorBasis j) F| * |hA.eigenvalues j * hA.eigenvectorBasis j x|) := by
    have hj0 : 0 ≤ hA.eigenvalues j := by
      simpa only using hpos.eigenvalues_nonneg j
    have hj1 : hA.eigenvalues j ≤ θ := (Finset.mem_filter.mp hj).2.le
    calc
      _ = hA.eigenvalues j ^ (r - 1) *
          (|inner ℝ (hA.eigenvectorBasis j) F| * |hA.eigenvalues j * hA.eigenvectorBasis j x|) := by
        rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hj0,
          show hA.eigenvalues j ^ r = hA.eigenvalues j ^ (r - 1) * hA.eigenvalues j by
            rw [← pow_succ, Nat.sub_add_cancel hr]]
        rw [abs_mul, abs_of_nonneg hj0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hj0 hj1 _)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc
    _ ≤ ∑ j ∈ K, |hA.eigenvalues j ^ r * inner ℝ (hA.eigenvectorBasis j) F * hA.eigenvectorBasis j x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ K, θ ^ (r - 1) *
        (|inner ℝ (hA.eigenvectorBasis j) F| * |hA.eigenvalues j * hA.eigenvectorBasis j x|) :=
      Finset.sum_le_sum ht
    _ = θ ^ (r - 1) * (∑ j ∈ K,
        |inner ℝ (hA.eigenvectorBasis j) F| * |hA.eigenvalues j * hA.eigenvectorBasis j x|) := by
      rw [Finset.mul_sum]
    _ ≤ θ ^ (r - 1) *
        (Real.sqrt (∑ j ∈ K, (inner ℝ (hA.eigenvectorBasis j) F) ^ 2) *
          Real.sqrt (∑ j ∈ K, (hA.eigenvalues j * hA.eigenvectorBasis j x) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (sum_abs_mul_abs_le_sqrt_sum_sq K _ _) (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ 1 * Real.sqrt ((A ^ 2) x x) := mul_le_mul
          (by simpa using Real.sqrt_le_sqrt hc) (Real.sqrt_le_sqrt he)
          (Real.sqrt_nonneg _) (by norm_num)
        _ = _ := one_mul _

theorem similar_square_diagonal (C : Chain V) (u : V → ℝ)
    (hu : ∀ x, 0 < u x) (x : V) :
    (C.similarTransition u ^ 2) x x = (C.transition ^ 2) x x := by
  simp only [pow_two, Matrix.mul_apply, Chain.similarTransition]
  apply Finset.sum_congr rfl
  intro y _
  field_simp [ne_of_gt (hu x), ne_of_gt (hu y)]

theorem similar_power_weightedVec (C : Chain V) (u : V → ℝ)
    (hu : ∀ x, 0 < u x) (r : ℕ) (f : V → ℝ) :
    CoordinateGrid.weightedVec u ((C.transition ^ r) *ᵥ f) =
      (C.similarTransition u ^ r).toEuclideanLin (CoordinateGrid.weightedVec u f) := by
  have ht : C.similarTilt u (fun _ => 1) = C.similarTransition u := by
    ext x y; simp [Chain.similarTilt]
  have hd : C.tilted (fun _ => 1) = C.transition := by
    ext x y; simp [Chain.tilted]
  apply PiLp.ext
  intro x
  have hh := C.similarTilt_pow_mulVec u (fun _ => 1) f
    (fun y => ne_of_gt (hu y)) r x
  rw [ht, hd] at hh
  exact hh.symm

private theorem sqrt_diagonal_atom_bound (a u d Λ : ℝ) (N : ℕ)
    (ha : 0 ≤ a) (hu : 0 < u) (hd : 0 < d) (hΛ : 0 ≤ Λ) (hN : 0 < N)
    (hdiag : a ≤ Λ / d ^ 2) (hatom : 1 / (50 * (N : ℝ)) ≤ u ^ 2) :
    Real.sqrt a / u ≤ Real.sqrt (50 * Λ * (N : ℝ)) / d := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have h50 : 0 < 50 * (N : ℝ) := by positivity
  have hdu : 0 < u ^ 2 := sq_pos_of_pos hu
  have hdd : 0 < d ^ 2 := sq_pos_of_pos hd
  have hat : 1 ≤ u ^ 2 * (50 * (N : ℝ)) := (div_le_iff₀ h50).mp hatom
  have hm := mul_le_mul_of_nonneg_left hat (div_nonneg hΛ hdd.le)
  have hb : a ≤ (50 * Λ * (N : ℝ) / d ^ 2) * u ^ 2 := by
    calc
      a ≤ Λ / d ^ 2 := hdiag
      _ ≤ (Λ / d ^ 2) * (u ^ 2 * (50 * (N : ℝ))) := by simpa using hm
      _ = _ := by ring
  have hdiv := (div_le_iff₀ hdu).mpr hb
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, div_pow, Real.sq_sqrt ha, Real.sq_sqrt (by positivity)]
  exact hdiv

theorem chain_projectedFunction_tail (C : Chain V) (u : V → ℝ)
    (hu : ∀ x, 0 < u x) (hunit : (∑ x, u x ^ 2) = 1)
    (hA : (C.similarTransition u).IsHermitian) (θ : ℝ) (hθ : 0 < θ)
    (hpos : (C.similarTransition u).PosSemidef)
    (N : ℕ) (hN : 0 < N) (d Λ : ℝ) (hd : 0 < d) (hΛ : 0 ≤ Λ)
    (hatom : ∀ x, 1 / (50 * (N : ℝ)) ≤ u x ^ 2)
    (hdiag : ∀ x, (C.similarTransition u ^ 2) x x ≤ Λ / d ^ 2)
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (r : ℕ) (hr : 1 ≤ r) (x : V) :
    |((C.transition ^ r) *ᵥ f) x -
      CoordinateGrid.projectedFunction C u (slowSpace (C.similarTransition u) hA θ) r f x| ≤
      Real.sqrt (50 * Λ * (N : ℝ)) / d * θ ^ (r - 1) := by
  have hF : ‖CoordinateGrid.weightedVec u f‖ ^ 2 ≤ 1 := by
    rw [CoordinateGrid.weightedVec_norm_sq, ← hunit]
    apply Finset.sum_le_sum
    intro y _
    have hh : f y ^ 2 ≤ 1 := by nlinarith [(hf y).1, (hf y).2]
    nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg (u y))]
  have hb := power_complement_bound (C.similarTransition u) hA θ hθ hpos
    (CoordinateGrid.weightedVec u f) hF r hr x
  rw [← similar_power_weightedVec C u hu r f,
    ← CoordinateGrid.weightedVec_projectedFunction C u hu] at hb
  change |u x * ((C.transition ^ r) *ᵥ f) x -
      u x * CoordinateGrid.projectedFunction C u (slowSpace (C.similarTransition u) hA θ) r f x| ≤ _ at hb
  rw [← mul_sub, abs_mul, abs_of_pos (hu x)] at hb
  have ha : 0 ≤ (C.similarTransition u ^ 2) x x := by
    rw [← hermitian_eigenbasis_energy_eq_diagonal _ hA x]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := sqrt_diagonal_atom_bound _ (u x) d Λ N ha (hu x) hd hΛ hN
    (hdiag x) (hatom x)
  calc
    _ ≤ θ ^ (r - 1) * Real.sqrt ((C.similarTransition u ^ 2) x x) / u x := by
      apply (le_div_iff₀ (hu x)).mpr
      simpa only [mul_comm] using hb
    _ = (Real.sqrt ((C.similarTransition u ^ 2) x x) / u x) * θ ^ (r - 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hs (by positivity)

theorem fixed_vector_mem_slowSpace (A : Matrix V V ℝ) (hA : A.IsHermitian) (θ : ℝ) (hθ1 : θ < 1)
    (w : EuclideanSpace ℝ V) (hw : A.toEuclideanLin w = w) :
    w ∈ slowSpace A hA θ := by
  classical
  have hs : A.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hc (j : V) (hj : j ∉ slowIndices A hA θ) : inner ℝ (hA.eigenvectorBasis j) w = 0 := by
    have hj' : hA.eigenvalues j < θ := by simpa [slowIndices] using hj
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
  by_cases hj : j ∈ slowIndices A hA θ
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
    (hA : (C.similarTransition u).IsHermitian) (θ : ℝ) (hθ1 : θ < 1) :
    WithLp.toLp 2 u ∈ slowSpace (C.similarTransition u) hA θ := by
  apply fixed_vector_mem_slowSpace _ _ θ hθ1
  apply PiLp.ext
  intro x
  exact congrFun (similarTransition_fixes_root C u hu) x


end Erdos642.Adaptive20261018.Spectrum
