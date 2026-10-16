import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.GraphDirichlet
import Openmath.Erdos642.Proofs.CampaignFe72210b.BipartiteSigns
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Connectedness and actual adjacency energy prove extremal simplicity.
Bipartite sign conjugation gives an explicit equivalence of opposite eigenspaces. -/
namespace Erdos642.CampaignFe72210bContinuation3.GraphExtremalEigenspaces

open Matrix Submodule Erdos642.CampaignFe72210b
open FiniteCoarea GraphDirichlet
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- Zero actual graph energy forces equality across every actual adjacent pair. -/
theorem eq_of_adj_of_energy_zero (f : V → ℝ)
    (hE : energy (adjWeight G) f = 0) {x y : V} (hxy : G.Adj x y) : f x = f y := by
  have hsum : (∑ a, ∑ b, adjWeight G a b * (f a - f b)^2) = 0 := by
    unfold energy at hE
    linarith
  have hnonneg (a b : V) : 0 ≤ adjWeight G a b * (f a - f b)^2 :=
    mul_nonneg (adjWeight_nonneg G a b) (sq_nonneg _)
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a _ => Finset.sum_nonneg fun b _ => hnonneg a b)).mp hsum x (Finset.mem_univ x)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun b _ => hnonneg x b)).mp hrow y (Finset.mem_univ y)
  have hsquare : (f x - f y)^2 = 0 := by
    simpa [adjWeight, SimpleGraph.adjMatrix_apply, hxy] using hterm
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Edgewise equality propagates along a genuine graph walk. -/
theorem eq_along_walk (f : V → ℝ) (hf : ∀ x y, G.Adj x y → f x = f y)
    {x y : V} (p : G.Walk x y) : f x = f y := by
  induction p with
  | nil => rfl
  | @cons x y z hxy p ih => exact (hf x y hxy).trans ih

/-- Every actual +1 eigenvector is a scalar multiple of the positive degree root. -/
theorem plus_eigenvector_eq_smul (hconn : G.Connected)
    (hdeg : ∀ x : V, 0 < G.degree x) (z : V → ℝ)
    (hz : normalizedAdjacency G *ᵥ z = z) : ∃ c : ℝ, z = c • degreeRoot G := by
  let : Nonempty V := hconn.nonempty
  let v : V := Classical.arbitrary V
  have hE : energy (adjWeight G) (normalizedFunction G z) = 0 := by
    rw [normalized_dirichlet G hdeg, hz, sub_self]
  have hconst (x : V) : normalizedFunction G z x = normalizedFunction G z v := by
    obtain ⟨p⟩ := hconn x v
    exact eq_along_walk G _ (fun a b hab => eq_of_adj_of_energy_zero G _ hE hab) p
  refine ⟨normalizedFunction G z v, ?_⟩
  funext x
  have hx := ne_of_gt (degreeRoot_positive G hdeg x)
  have hc := hconst x
  change z x / degreeRoot G x = normalizedFunction G z v at hc
  exact (div_eq_iff hx).mp hc

noncomputable def rootVector : EuclideanSpace ℝ V := WithLp.toLp 2 (degreeRoot G)

/-- The genuine nonzero positive root eigenvector in Euclidean coordinates. -/
theorem rootVector_eigen (hdeg : ∀ x : V, 0 < G.degree x) :
    (normalizedAdjacency G).toEuclideanLin (rootVector G) = (1 : ℝ) • rootVector G := by
  apply PiLp.ext
  intro x
  change (normalizedAdjacency G *ᵥ degreeRoot G) x = 1 * degreeRoot G x
  simpa only [one_mul] using congrFun (normalizedAdjacency_degreeRoot G hdeg) x

theorem rootVector_ne_zero [Nonempty V] (hdeg : ∀ x : V, 0 < G.degree x) :
    rootVector G ≠ 0 := by
  intro hz
  let x : V := Classical.arbitrary V
  have hx : degreeRoot G x = 0 := by
    have he := congrArg (fun z : EuclideanSpace ℝ V => z x) hz
    simpa [rootVector] using he
  exact (ne_of_gt (degreeRoot_positive G hdeg x)) hx

/-- Exact actual eigenspace identification, proved from connected graph energy. -/
theorem plus_eigenspace_eq_span (hconn : G.Connected)
    (hdeg : ∀ x : V, 0 < G.degree x) :
    Module.End.eigenspace (normalizedAdjacency G).toEuclideanLin (1 : ℝ) =
      ℝ ∙ rootVector G := by
  ext z
  constructor
  · intro hz
    have he := Module.End.mem_eigenspace_iff.mp hz
    have hfun : normalizedAdjacency G *ᵥ ⇑z = ⇑z := by
      funext x
      have hx := congrArg (fun z : EuclideanSpace ℝ V => z x) he
      change (normalizedAdjacency G *ᵥ ⇑z) x = 1 * z x at hx
      simpa only [one_mul] using hx
    obtain ⟨c, hc⟩ := plus_eigenvector_eq_smul G hconn hdeg ⇑z hfun
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    apply PiLp.ext
    intro x
    change c * degreeRoot G x = z x
    exact (congrFun hc x).symm
  · intro hz
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    apply Module.End.mem_eigenspace_iff.mpr
    rw [← hc, map_smul, rootVector_eigen G hdeg]
    simp

/-- Connectedness proves +1 simplicity; no multiplicity premise is supplied. -/
theorem plus_eigenspace_finrank (hconn : G.Connected)
    (hdeg : ∀ x : V, 0 < G.degree x) :
    Module.finrank ℝ (Module.End.eigenspace (normalizedAdjacency G).toEuclideanLin (1 : ℝ)) = 1 := by
  let : Nonempty V := hconn.nonempty
  rw [plus_eigenspace_eq_span G hconn hdeg]
  exact finrank_span_singleton (rootVector_ne_zero G hdeg)

/-- Multiplication by an actual unit sign is a real Euclidean linear equivalence. -/
noncomputable def signEquiv (σ : V → ℝ) (hσ : ∀ x, σ x ^ 2 = 1) :
    EuclideanSpace ℝ V ≃ₗ[ℝ] EuclideanSpace ℝ V where
  toFun z := WithLp.toLp 2 (fun x => σ x * z x)
  invFun z := WithLp.toLp 2 (fun x => σ x * z x)
  left_inv z := by
    apply PiLp.ext
    intro x
    change σ x * (σ x * z x) = z x
    rw [← mul_assoc, ← pow_two, hσ x, one_mul]
  right_inv z := by
    apply PiLp.ext
    intro x
    change σ x * (σ x * z x) = z x
    rw [← mul_assoc, ← pow_two, hσ x, one_mul]
  map_add' z u := by
    apply PiLp.ext
    intro x
    change σ x * (z x + u x) = σ x * z x + σ x * u x
    ring
  map_smul' c z := by
    apply PiLp.ext
    intro x
    change σ x * (c * z x) = c * (σ x * z x)
    ring

omit [DecidableEq V] in
/-- Literal normalized adjacency anticommutes with an actual bipartite edge sign. -/
theorem normalizedAdjacency_sign_mulVec (σ : V → ℝ)
    (hflip : ∀ x y, G.Adj x y → σ y = -σ x) (z : V → ℝ) :
    normalizedAdjacency G *ᵥ (fun x => σ x * z x) =
      fun x => -σ x * (normalizedAdjacency G *ᵥ z) x := by
  funext x
  have hterm (y : V) : normalizedAdjacency G x y * (σ y * z y) =
      -σ x * (normalizedAdjacency G x y * z y) := by
    by_cases hxy : G.Adj x y
    · rw [hflip x y hxy]
      ring
    · simp [normalizedAdjacency, SimpleGraph.adjMatrix_apply, hxy]
  change (∑ y, normalizedAdjacency G x y * (σ y * z y)) =
    -σ x * ∑ y, normalizedAdjacency G x y * z y
  simp_rw [hterm]
  rw [← Finset.mul_sum]

/-- The sign map sends every actual μ eigenvector to a -μ eigenvector. -/
theorem sign_eigen (σ : V → ℝ) (hσ : ∀ x, σ x ^ 2 = 1)
    (hflip : ∀ x y, G.Adj x y → σ y = -σ x) (μ : ℝ)
    (z : EuclideanSpace ℝ V)
    (hz : (normalizedAdjacency G).toEuclideanLin z = μ • z) :
    (normalizedAdjacency G).toEuclideanLin (signEquiv σ hσ z) =
      (-μ) • signEquiv σ hσ z := by
  apply PiLp.ext
  intro x
  change (normalizedAdjacency G *ᵥ (fun y => σ y * z y)) x = (-μ) * (σ x * z x)
  rw [normalizedAdjacency_sign_mulVec G σ hflip]
  have hx := congrArg (fun z : EuclideanSpace ℝ V => z x) hz
  change (normalizedAdjacency G *ᵥ ⇑z) x = μ * z x at hx
  change -σ x * (normalizedAdjacency G *ᵥ ⇑z) x = (-μ) * (σ x * z x)
  rw [hx]
  ring

/-- Explicit linear equivalence between opposite actual eigenspaces. -/
noncomputable def signEigenspaceEquiv (σ : V → ℝ) (hσ : ∀ x, σ x ^ 2 = 1)
    (hflip : ∀ x y, G.Adj x y → σ y = -σ x) (μ : ℝ) :
    Module.End.eigenspace (normalizedAdjacency G).toEuclideanLin μ ≃ₗ[ℝ]
      Module.End.eigenspace (normalizedAdjacency G).toEuclideanLin (-μ) where
  toFun z := ⟨signEquiv σ hσ z, Module.End.mem_eigenspace_iff.mpr
    (sign_eigen G σ hσ hflip μ z (Module.End.mem_eigenspace_iff.mp z.property))⟩
  invFun z := ⟨signEquiv σ hσ z, Module.End.mem_eigenspace_iff.mpr (by
    simpa only [neg_neg] using sign_eigen G σ hσ hflip (-μ) z
      (Module.End.mem_eigenspace_iff.mp z.property))⟩
  left_inv z := by
    apply Subtype.ext
    exact (signEquiv σ hσ).left_inv z
  right_inv z := by
    apply Subtype.ext
    exact (signEquiv σ hσ).right_inv z
  map_add' z u := by
    apply Subtype.ext
    exact (signEquiv σ hσ).map_add z u
  map_smul' c z := by
    apply Subtype.ext
    exact (signEquiv σ hσ).map_smul c z

/-- Genuine bipartiteness and connectedness prove -1 simplicity. -/
theorem minus_eigenspace_finrank (hconn : G.Connected)
    (hdeg : ∀ x : V, 0 < G.degree x) (hbip : G.IsBipartite) :
    Module.finrank ℝ (Module.End.eigenspace (normalizedAdjacency G).toEuclideanLin (-1 : ℝ)) = 1 := by
  obtain ⟨σ, hσ, hflip⟩ := exists_bipartite_sign G hbip
  have hdim := (signEigenspaceEquiv G σ hσ hflip (1 : ℝ)).finrank_eq
  rw [plus_eigenspace_finrank G hconn hdeg] at hdim
  exact hdim.symm

/-- Existence is also supplied, not only a numerical multiplicity equality. -/
theorem plus_hasEigenvalue (hconn : G.Connected) (hdeg : ∀ x : V, 0 < G.degree x) :
    Module.End.HasEigenvalue (normalizedAdjacency G).toEuclideanLin (1 : ℝ) := by
  rw [Module.End.hasEigenvalue_iff]
  intro hbot
  have hd := plus_eigenspace_finrank G hconn hdeg
  rw [hbot] at hd
  simp at hd

theorem minus_hasEigenvalue (hconn : G.Connected) (hdeg : ∀ x : V, 0 < G.degree x)
    (hbip : G.IsBipartite) :
    Module.End.HasEigenvalue (normalizedAdjacency G).toEuclideanLin (-1 : ℝ) := by
  rw [Module.End.hasEigenvalue_iff]
  intro hbot
  have hd := minus_eigenspace_finrank G hconn hdeg hbip
  rw [hbot] at hd
  simp at hd

end Erdos642.CampaignFe72210bContinuation3.GraphExtremalEigenspaces
