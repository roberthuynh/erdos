import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-! Sign-independent rank-one projectors of simple real eigenspaces.
No graph, transition, or heat-kernel conclusion is assumed. -/

namespace Erdos642.CampaignFe72210b

open Submodule

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Two unit vectors in one simple real eigenspace have the same coordinate
outer product, independently of their signs. -/
theorem simple_eigenspace_outer_eq
    (T : Module.End ℝ (EuclideanSpace ℝ V)) (lam : ℝ)
    (w z : EuclideanSpace ℝ V)
    (hsimple : Module.finrank ℝ (T.eigenspace lam) = 1)
    (hw : T w = lam • w) (hz : T z = lam • z)
    (hwunit : ‖w‖ = 1) (hzunit : ‖z‖ = 1) (x y : V) :
    z x * z y = w x * w y := by
  have hwne : w ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero] at hwunit
    norm_num at hwunit
  have hspan : T.eigenspace lam = ℝ ∙ w :=
    eq_span_singleton_of_mem_of_finrank_eq_one hsimple
      (Module.End.mem_eigenspace_iff.mpr hw) hwne
  have hzmem : z ∈ ℝ ∙ w := by
    rw [← hspan]
    exact Module.End.mem_eigenspace_iff.mpr hz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzmem
  have hcabs : |c| = 1 := by
    rw [← hc, norm_smul, hwunit, mul_one, Real.norm_eq_abs] at hzunit
    exact hzunit
  have hcsq : c ^ 2 = 1 := by
    calc
      c ^ 2 = |c| ^ 2 := (sq_abs c).symm
      _ = 1 := by rw [hcabs]; norm_num
  have hx : c * w x = z x := by
    simpa only [PiLp.smul_apply, smul_eq_mul] using
      congrArg (fun q : EuclideanSpace ℝ V => q x) hc
  have hy : c * w y = z y := by
    simpa only [PiLp.smul_apply, smul_eq_mul] using
      congrArg (fun q : EuclideanSpace ℝ V => q y) hc
  rw [← hx, ← hy]
  calc
    c * w x * (c * w y) = c ^ 2 * (w x * w y) := by ring
    _ = w x * w y := by rw [hcsq, one_mul]

section Matrix

open Matrix

/-- The canonical eigenvector of a Hermitian matrix represents the same
rank-one projector as any unit vector of its simple eigenspace. -/
theorem hermitian_eigenvector_outer_eq (B : Matrix V V ℝ) (hB : B.IsHermitian)
    (lam : ℝ) (w : EuclideanSpace ℝ V)
    (hsimple : Module.finrank ℝ (Module.End.eigenspace B.toEuclideanLin lam) = 1)
    (hw : B.toEuclideanLin w = lam • w) (hwunit : ‖w‖ = 1)
    (j : V) (hj : hB.eigenvalues j = lam) (x y : V) :
    (hB.eigenvectorBasis j) x * (hB.eigenvectorBasis j) y = w x * w y := by
  have hz : B.toEuclideanLin (hB.eigenvectorBasis j) =
      lam • hB.eigenvectorBasis j := by
    apply PiLp.ext
    intro q
    change (B *ᵥ ⇑(hB.eigenvectorBasis j)) q = lam * (hB.eigenvectorBasis j) q
    simpa only [Pi.smul_apply, smul_eq_mul, hj] using
      congrFun (hB.mulVec_eigenvectorBasis j) q
  exact simple_eigenspace_outer_eq B.toEuclideanLin lam w (hB.eigenvectorBasis j)
    hsimple hw hz hwunit (hB.eigenvectorBasis.orthonormal.norm_eq_one j) x y

/-- Canonical matrix eigenvalue multiplicity equals eigenspace dimension,
transporting Mathlib's linear-map count along its public index equivalence. -/
theorem hermitian_eigenvalue_filter_card (B : Matrix V V ℝ) (hB : B.IsHermitian)
    (lam : ℝ) :
    (Finset.univ.filter (fun j => hB.eigenvalues j = lam)).card =
      Module.finrank ℝ (Module.End.eigenspace B.toEuclideanLin lam) := by
  classical
  let hT : B.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  calc
    (Finset.univ.filter (fun j => hB.eigenvalues j = lam)).card =
        (Finset.univ.filter (fun j : Fin (Fintype.card V) =>
          hT.eigenvalues finrank_euclideanSpace j = lam)).card := by
      apply Finset.card_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      intro j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    _ = Module.finrank ℝ (Module.End.eigenspace B.toEuclideanLin lam) :=
      hT.card_filter_eigenvalues_eq finrank_euclideanSpace lam

/-- A simple canonical eigenvalue has exactly one index. -/
theorem hermitian_simple_eigenvalue_filter_singleton (B : Matrix V V ℝ)
    (hB : B.IsHermitian) (lam : ℝ)
    (hsimple : Module.finrank ℝ (Module.End.eigenspace B.toEuclideanLin lam) = 1) :
    ∃ j : V, Finset.univ.filter (fun k => hB.eigenvalues k = lam) = {j} := by
  apply Finset.card_eq_one.mp
  rw [hermitian_eigenvalue_filter_card B hB lam, hsimple]

/-- The entire canonical spectral sum of a simple eigenvalue is its explicit
unit eigenvector's rank-one outer product. -/
theorem hermitian_simple_eigenprojector_sum (B : Matrix V V ℝ) (hB : B.IsHermitian)
    (lam : ℝ) (w : EuclideanSpace ℝ V)
    (hsimple : Module.finrank ℝ (Module.End.eigenspace B.toEuclideanLin lam) = 1)
    (hw : B.toEuclideanLin w = lam • w) (hwunit : ‖w‖ = 1) (x y : V) :
    (∑ j ∈ Finset.univ.filter (fun k => hB.eigenvalues k = lam),
      (hB.eigenvectorBasis j) x * (hB.eigenvectorBasis j) y) = w x * w y := by
  classical
  obtain ⟨j, hj⟩ := hermitian_simple_eigenvalue_filter_singleton B hB lam hsimple
  have hjmem : j ∈ Finset.univ.filter (fun k => hB.eigenvalues k = lam) := by
    rw [hj]
    simp
  have hjval : hB.eigenvalues j = lam := (Finset.mem_filter.mp hjmem).2
  rw [hj, Finset.sum_singleton]
  exact hermitian_eigenvector_outer_eq B hB lam w hsimple hw hwunit j hjval x y

end Matrix

end Erdos642.CampaignFe72210b
