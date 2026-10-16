import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.CoordinateGrid
import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralEntries
import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralSum
import Openmath.Erdos642.Proofs.CampaignFe72210b.ShoreOccupation
import Openmath.Erdos642.Proofs.CampaignFe72210b.ShoreDensity

/-! Actual slow spectral subspace and fourth-return shore transport. -/
namespace Erdos642.CampaignFe72210bContinuation3.MomentSmoothing
open Matrix Erdos642.CampaignFe72210b Erdos642.FiniteMarkov
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def slowIndices (A : Matrix V V ℝ) (hA : A.IsHermitian) : Finset V :=
  Finset.univ.filter (fun j => (1 : ℝ) / 4 ≤ hA.eigenvalues j)
noncomputable def slowSpace (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    Submodule ℝ (EuclideanSpace ℝ V) :=
  Submodule.span ℝ (↑((slowIndices A hA).image hA.eigenvectorBasis) : Set _)
noncomputable def slowBasis (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    OrthonormalBasis (slowIndices A hA) ℝ (slowSpace A hA) :=
  OrthonormalBasis.span hA.eigenvectorBasis.orthonormal (slowIndices A hA)
@[simp] theorem slowBasis_apply (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (j : slowIndices A hA) : (slowBasis A hA j : EuclideanSpace ℝ V) =
      hA.eigenvectorBasis j := by
  exact OrthonormalBasis.span_apply _ _ _
theorem slowSpace_finrank (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    Module.finrank ℝ (slowSpace A hA) = (slowIndices A hA).card := by
  rw [Module.finrank_eq_card_basis (slowBasis A hA).toBasis]
  simp
noncomputable def slowFinBasis (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    OrthonormalBasis (Fin (slowIndices A hA).card) ℝ (slowSpace A hA) :=
  (slowBasis A hA).reindex (slowIndices A hA).equivFin
theorem slowSpace_finrank_le (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    Module.finrank ℝ (slowSpace A hA) ≤ Fintype.card V := by
  rw [slowSpace_finrank]
  exact Finset.card_le_univ _
theorem slow_projection_eq_sum (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (z : EuclideanSpace ℝ V) :
    ((slowSpace A hA).orthogonalProjectionOnto z : EuclideanSpace ℝ V) =
      ∑ j ∈ slowIndices A hA, inner ℝ (hA.eigenvectorBasis j) z • hA.eigenvectorBasis j := by
  have hh := (slowBasis A hA).orthogonalProjectionOnto_apply_eq_sum z
  have hc := congrArg (fun y : slowSpace A hA => (y : EuclideanSpace ℝ V)) hh
  simp only [Submodule.coe_sum, Submodule.coe_smul, slowBasis_apply] at hc
  exact hc.trans (Finset.sum_coe_sort (slowIndices A hA)
    (fun j => inner ℝ (hA.eigenvectorBasis j) z • hA.eigenvectorBasis j))

theorem squared_trace_eq_eigen_energy (A : Matrix V V ℝ) (hA : A.IsHermitian) :
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

theorem slow_rank_trace_bound (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    (Module.finrank ℝ (slowSpace A hA) : ℝ) ≤ 16 * ∑ x, (A ^ 2) x x := by
  rw [slowSpace_finrank A hA, squared_trace_eq_eigen_energy A hA]
  have hl : (slowIndices A hA).card * (1 / 16 : ℝ) ≤
      ∑ j ∈ slowIndices A hA, hA.eigenvalues j ^ 2 := by
    calc
      _ = ∑ _j ∈ slowIndices A hA, (1 / 16 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hh : (1 : ℝ) / 4 ≤ hA.eigenvalues j := by simpa [slowIndices] using hj
        nlinarith
  have hu : (∑ j ∈ slowIndices A hA, hA.eigenvalues j ^ 2) ≤
      ∑ j, hA.eigenvalues j ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg (hA.eigenvalues j))
  linarith only [hl, hu]

theorem slow_rank_diagonal_bound (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (d Λ : ℝ) (hdiag : ∀ x, (A ^ 2) x x ≤ Λ / d ^ 2) :
    (Module.finrank ℝ (slowSpace A hA) : ℝ) ≤
      16 * Λ * (Fintype.card V : ℝ) / d ^ 2 := by
  have hh := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset V)) => hdiag x)
  have ht := slow_rank_trace_bound A hA
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  calc
    _ ≤ 16 * (∑ x, (A ^ 2) x x) := ht
    _ ≤ 16 * ((Fintype.card V : ℝ) * (Λ / d ^ 2)) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring

theorem power_complement_entry (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (F : EuclideanSpace ℝ V) (r : ℕ) (x : V) :
    ((A ^ r).toEuclideanLin F -
      ((slowSpace A hA).orthogonalProjectionOnto ((A ^ r).toEuclideanLin F) :
        EuclideanSpace ℝ V)) x =
      ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j < 1 / 4),
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
      (∑ j ∈ slowIndices A hA, inner ℝ (hA.eigenvectorBasis j) z • hA.eigenvectorBasis j) +
      ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j < 1 / 4),
        inner ℝ (hA.eigenvectorBasis j) z • hA.eigenvectorBasis j := by
    nth_rw 1 [← hA.eigenvectorBasis.sum_repr' z]
    simpa only [slowIndices, not_le] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j => (1 : ℝ) / 4 ≤ hA.eigenvalues j)
        (fun j => inner ℝ (hA.eigenvectorBasis j) z • hA.eigenvectorBasis j)).symm
  have he : z - ((slowSpace A hA).orthogonalProjectionOnto z : EuclideanSpace ℝ V) =
      ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j < 1 / 4),
        inner ℝ (hA.eigenvectorBasis j) z • hA.eigenvectorBasis j := by
    rw [slow_projection_eq_sum]
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hsplit)
  have hx := congrArg (fun w : EuclideanSpace ℝ V => w x) he
  simpa only [PiLp.sub_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, hc] using hx

theorem power_complement_bound (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (hpos : A.PosSemidef) (F : EuclideanSpace ℝ V) (hF : ‖F‖ ^ 2 ≤ 1)
    (r : ℕ) (hr : 1 ≤ r) (x : V) :
    |((A ^ r).toEuclideanLin F -
      ((slowSpace A hA).orthogonalProjectionOnto ((A ^ r).toEuclideanLin F) :
        EuclideanSpace ℝ V)) x| ≤
      (1 / 4 : ℝ) ^ (r - 1) * Real.sqrt ((A ^ 2) x x) := by
  classical
  rw [power_complement_entry]
  let K := Finset.univ.filter (fun j => hA.eigenvalues j < (1 : ℝ) / 4)
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
      (1 / 4 : ℝ) ^ (r - 1) *
        (|inner ℝ (hA.eigenvectorBasis j) F| * |hA.eigenvalues j * hA.eigenvectorBasis j x|) := by
    have hj0 : 0 ≤ hA.eigenvalues j := by
      simpa only using hpos.eigenvalues_nonneg j
    have hj1 : hA.eigenvalues j ≤ (1 : ℝ) / 4 := (Finset.mem_filter.mp hj).2.le
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
    _ ≤ ∑ j ∈ K, (1 / 4 : ℝ) ^ (r - 1) *
        (|inner ℝ (hA.eigenvectorBasis j) F| * |hA.eigenvalues j * hA.eigenvectorBasis j x|) :=
      Finset.sum_le_sum ht
    _ = (1 / 4 : ℝ) ^ (r - 1) * (∑ j ∈ K,
        |inner ℝ (hA.eigenvectorBasis j) F| * |hA.eigenvalues j * hA.eigenvectorBasis j x|) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / 4 : ℝ) ^ (r - 1) *
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
    (hA : (C.similarTransition u).IsHermitian)
    (hpos : (C.similarTransition u).PosSemidef)
    (N : ℕ) (hN : 0 < N) (d Λ : ℝ) (hd : 0 < d) (hΛ : 0 ≤ Λ)
    (hatom : ∀ x, 1 / (50 * (N : ℝ)) ≤ u x ^ 2)
    (hdiag : ∀ x, (C.similarTransition u ^ 2) x x ≤ Λ / d ^ 2)
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (r : ℕ) (hr : 1 ≤ r) (x : V) :
    |((C.transition ^ r) *ᵥ f) x -
      CoordinateGrid.projectedFunction C u (slowSpace (C.similarTransition u) hA) r f x| ≤
      Real.sqrt (50 * Λ * (N : ℝ)) / d * (1 / 4 : ℝ) ^ (r - 1) := by
  have hF : ‖CoordinateGrid.weightedVec u f‖ ^ 2 ≤ 1 := by
    rw [CoordinateGrid.weightedVec_norm_sq, ← hunit]
    apply Finset.sum_le_sum
    intro y _
    have hh : f y ^ 2 ≤ 1 := by nlinarith [(hf y).1, (hf y).2]
    nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg (u y))]
  have hb := power_complement_bound (C.similarTransition u) hA hpos
    (CoordinateGrid.weightedVec u f) hF r hr x
  rw [← similar_power_weightedVec C u hu r f,
    ← CoordinateGrid.weightedVec_projectedFunction C u hu] at hb
  change |u x * ((C.transition ^ r) *ᵥ f) x -
      u x * CoordinateGrid.projectedFunction C u (slowSpace (C.similarTransition u) hA) r f x| ≤ _ at hb
  rw [← mul_sub, abs_mul, abs_of_pos (hu x)] at hb
  have ha : 0 ≤ (C.similarTransition u ^ 2) x x := by
    rw [← hermitian_eigenbasis_energy_eq_diagonal _ hA x]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := sqrt_diagonal_atom_bound _ (u x) d Λ N ha (hu x) hd hΛ hN
    (hdiag x) (hatom x)
  calc
    _ ≤ (1 / 4 : ℝ) ^ (r - 1) * Real.sqrt ((C.similarTransition u ^ 2) x x) / u x := by
      apply (le_div_iff₀ (hu x)).mpr
      simpa only [mul_comm] using hb
    _ = (Real.sqrt ((C.similarTransition u ^ 2) x x) / u x) * (1 / 4 : ℝ) ^ (r - 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hs (by positivity)

section Graph
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (s : Set V) [DecidablePred (· ∈ s)]
theorem shoreTransition_square_diagonal (t : Set V) (hbi : G.IsBipartiteWith s t)
    (x : s) :
    (shoreTransition G s ^ 2) x x = (graphTransition G ^ 4) x.val x.val := by
  have hp : (graphTransition G ^ 4) = (graphTransition G ^ 2) * (graphTransition G ^ 2) := by
    rw [← pow_add]
  rw [hp, Matrix.mul_apply, pow_two, Matrix.mul_apply]
  change (∑ y : s, (graphTransition G ^ 2) x.val y.val *
    (graphTransition G ^ 2) y.val x.val) = _
  calc
    _ = ∑ y ∈ s.toFinset, (graphTransition G ^ 2) x.val y *
        (graphTransition G ^ 2) y x.val :=
      (Finset.sum_subtype s.toFinset (fun _ => Set.mem_toFinset)
        (fun y => (graphTransition G ^ 2) x.val y * (graphTransition G ^ 2) y x.val)).symm
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      have hy' : y ∉ s := by simpa using hy
      rw [graphTransition_sq_zero_outside G hbi x.val y x.property hy', zero_mul]

theorem shore_similarity_square_diagonal [Nonempty s] (t : Set V)
    (hbi : G.IsBipartiteWith s t) (hdeg : ∀ x : V, 0 < G.degree x) (x : s) :
    ((shoreChain G s t hbi hdeg).similarTransition (shoreRoot G s) ^ 2) x x =
      (graphTransition G ^ 4) x.val x.val := by
  rw [similar_square_diagonal _ _ (shoreRoot_pos G s t hbi hdeg)]
  exact shoreTransition_square_diagonal G s t hbi x

/-- Actual graph moment supplies the slow subspace, its rank and uniform tail.
No desired rank, tail, projection or graph normalization hypothesis is inserted. -/
theorem graph_moment_smoothing [Nonempty s] (t : Set V) (hbi : G.IsBipartiteWith s t)
    (d Λ : ℝ) (hd : 0 < d) (hΛ : 1 ≤ Λ)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100 * d)
    (hmoment : ∀ x : V, (graphTransition G ^ 4) x x ≤ Λ / d ^ 2) :
    ∃ (hdeg : ∀ x : V, 0 < G.degree x)
      (E : Submodule ℝ (EuclideanSpace ℝ s)) (D : ℕ),
      Nonempty (OrthonormalBasis (Fin D) ℝ E) ∧
      D ≤ Fintype.card V ∧
      (D : ℝ) ≤ 16 * Λ * (Fintype.card V : ℝ) / d ^ 2 ∧
      ∀ (f : s → ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      ∀ (r : ℕ), 1 ≤ r → ∀ x : s,
      |(((shoreChain G s t hbi hdeg).transition ^ r) *ᵥ f) x -
        CoordinateGrid.projectedFunction (shoreChain G s t hbi hdeg) (shoreRoot G s) E r f x| ≤
        Real.sqrt (50 * Λ * (Fintype.card V : ℝ)) / d * (1 / 4 : ℝ) ^ (r - 1) := by
  classical
  let hdeg : ∀ x : V, 0 < G.degree x := fun x => by exact_mod_cast (hd.trans_le (hmin x))
  let C := shoreChain G s t hbi hdeg
  let u := shoreRoot G s
  let A := C.similarTransition u
  have hA : A.IsHermitian := shore_similarity_hermitian G s t hbi hdeg
  have hp : A.PosSemidef := by
    dsimp [A, C, u]
    rw [shore_similarTransition G s t hbi hdeg]
    exact shore_normalized_posSemidef G s
  have hdiag : ∀ x : s, (A ^ 2) x x ≤ Λ / d ^ 2 := by
    intro x
    rw [show (A ^ 2) x x = (graphTransition G ^ 4) x.val x.val from
      shore_similarity_square_diagonal G s t hbi hdeg x]
    exact hmoment x.val
  let E := slowSpace A hA
  let D := (slowIndices A hA).card
  have hs : Fintype.card s ≤ Fintype.card V := Fintype.card_subtype_le _
  have hN : 0 < Fintype.card V := by
    have hns : 0 < Fintype.card s := Fintype.card_pos
    omega
  refine ⟨hdeg, E, D, ⟨slowFinBasis A hA⟩, ?_, ?_, ?_⟩
  · exact (Finset.card_le_univ _).trans hs
  · have hh := slow_rank_diagonal_bound A hA d Λ hdiag
    rw [slowSpace_finrank] at hh
    apply hh.trans
    have hm := mul_le_mul_of_nonneg_left (show (Fintype.card s : ℝ) ≤ (Fintype.card V : ℝ) by exact_mod_cast hs)
      (show 0 ≤ 16 * Λ / d ^ 2 by positivity)
    convert hm using 1 <;> ring
  · intro f hf r hr x
    exact chain_projectedFunction_tail C u (shoreRoot_pos G s t hbi hdeg)
      (shoreRoot_normalized G s t hbi hdeg) hA hp (Fintype.card V) hN d Λ hd (by linarith)
      (shoreRoot_sq_lower G s t hbi hdeg d hd hmin hmax) hdiag f hf r hr x
end Graph
end Erdos642.CampaignFe72210bContinuation3.MomentSmoothing
