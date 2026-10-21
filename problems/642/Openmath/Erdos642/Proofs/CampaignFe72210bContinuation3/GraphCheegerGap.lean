import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.GraphCheegerRayleigh
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.GraphExtremalEigenspaces

/-! Genuine finite graph conductance implies the exact bipartite spectral-gap predicate.
No Rayleigh, simplicity, or remaining-eigenvalue bound is a premise. -/
namespace Erdos642.CampaignFe72210bContinuation3.GraphCheegerGap

open Matrix Erdos642.CampaignFe72210b
open FiniteCoarea GraphDirichlet GraphCheegerRayleigh GraphExtremalEigenspaces
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- Symmetry of the actual normalized adjacency in dot-product form. -/
theorem normalized_dot_swap (z u : V → ℝ) :
    dotProduct (normalizedAdjacency G *ᵥ z) u =
      dotProduct z (normalizedAdjacency G *ᵥ u) := by
  have hsym (x y : V) : normalizedAdjacency G x y = normalizedAdjacency G y x := by
    simp [normalizedAdjacency, SimpleGraph.adjMatrix_apply, G.adj_comm, mul_comm]
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [hsym y x]
  ring

/-- Every actual non-+1 eigenvector is orthogonal to the genuine positive root. -/
theorem eigenvector_root_orthogonal (hdeg : ∀ x : V, 0 < G.degree x)
    (μ : ℝ) (hμ : μ ≠ 1) (z : V → ℝ)
    (hz : normalizedAdjacency G *ᵥ z = μ • z) : dotProduct z (degreeRoot G) = 0 := by
  have he := normalized_dot_swap G z (degreeRoot G)
  rw [hz, normalizedAdjacency_degreeRoot G hdeg] at he
  have hbalance : μ * dotProduct z (degreeRoot G) = dotProduct z (degreeRoot G) := by
    simpa only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum] using he
  have hprod : (μ - 1) * dotProduct z (degreeRoot G) = 0 := by nlinarith only [hbalance]
  rcases mul_eq_zero.mp hprod with hzero | hzero
  · exact False.elim (hμ (by linarith only [hzero]))
  · exact hzero

omit [Fintype V] [DecidableEq V] in
private theorem coe_ne_zero {z : EuclideanSpace ℝ V} (hz : z ≠ 0) : (⇑z : V → ℝ) ≠ 0 := by
  intro he
  apply hz
  apply PiLp.ext
  intro x
  change z x = 0
  exact congrFun he x

/-- The positive-side eigenvalue bound follows from the actual graph cut law. -/
theorem eigenvalue_le_of_ne_one [Nonempty V]
    (hdeg : ∀ x : V, 0 < G.degree x) (η : ℝ) (hη : 0 < η) (hη2 : η ≤ 2)
    (hcut : ∀ S : Finset V, 0 < volume (adjWeight G) S →
      0 < volume (adjWeight G) Sᶜ →
      η * volume (adjWeight G) S * volume (adjWeight G) Sᶜ ≤
        degreeVolume G * cut (adjWeight G) S)
    (μ : ℝ) (hμ : Module.End.HasEigenvalue (normalizedAdjacency G).toEuclideanLin μ)
    (hμ1 : μ ≠ 1) : μ ≤ 1 - η ^ 2 / 8 := by
  obtain ⟨z, hz⟩ := hμ.exists_hasEigenvector
  have he := hz.apply_eq_smul
  have hfun : normalizedAdjacency G *ᵥ ⇑z = μ • ⇑z := by
    funext x
    have hx := congrArg (fun z : EuclideanSpace ℝ V => z x) he
    change (normalizedAdjacency G *ᵥ ⇑z) x = μ * z x at hx
    exact hx
  have horth := eigenvector_root_orthogonal G hdeg μ hμ1 ⇑z hfun
  have hr := graph_cheeger_rayleigh G hdeg η hη hη2 hcut ⇑z horth
  rw [hfun] at hr
  have hnorm : 0 < dotProduct (⇑z : V → ℝ) ⇑z := by
    have hn : 0 ≤ dotProduct (⇑z : V → ℝ) ⇑z :=
      Finset.sum_nonneg fun x _ => mul_self_nonneg (z x)
    have hne : dotProduct (⇑z : V → ℝ) ⇑z ≠ 0 := by
      intro hzero
      exact coe_ne_zero hz.2 (dotProduct_self_eq_zero.mp hzero)
    exact lt_of_le_of_ne hn (Ne.symm hne)
  have hr' : μ * dotProduct (⇑z : V → ℝ) ⇑z ≤
      (1 - η ^ 2 / 8) * dotProduct (⇑z : V → ℝ) ⇑z := by
    simpa only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_left_comm, Finset.mul_sum] using hr
  exact le_of_mul_le_mul_right hr' hnorm

/-- Actual bipartiteness reflects every actual normalized eigenvalue. -/
theorem neg_hasEigenvalue_of_bipartite (hbip : G.IsBipartite) (μ : ℝ)
    (hμ : Module.End.HasEigenvalue (normalizedAdjacency G).toEuclideanLin μ) :
    Module.End.HasEigenvalue (normalizedAdjacency G).toEuclideanLin (-μ) := by
  obtain ⟨σ, hσ, hflip⟩ := exists_bipartite_sign G hbip
  obtain ⟨z, hz⟩ := hμ.exists_hasEigenvector
  have he := sign_eigen G σ hσ hflip μ z hz.apply_eq_smul
  have hne : signEquiv σ hσ z ≠ 0 := by
    intro hzero
    apply hz.2
    have hinv := congrArg (signEquiv σ hσ).symm hzero
    simpa only [LinearEquiv.symm_apply_apply, map_zero] using hinv
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr he, hne⟩

                                                                                          
theorem graph_hasBipartiteSpectralGap_of_conductance
    (hconn : G.Connected) (hbip : G.IsBipartite)
    (hdeg : ∀ x : V, 0 < G.degree x) (η : ℝ) (hη : 0 < η) (hη2 : η ≤ 2)
    (hcut : ∀ S : Finset V, 0 < volume (adjWeight G) S →
      0 < volume (adjWeight G) Sᶜ →
      η * volume (adjWeight G) S * volume (adjWeight G) Sᶜ ≤
        degreeVolume G * cut (adjWeight G) S) :
    HasBipartiteSpectralGap G (η ^ 2 / 8) := by
  let : Nonempty V := hconn.nonempty
  refine ⟨cheeger_gap_pos hη, (cheeger_gap_le_half hη.le hη2).trans (by norm_num),
    plus_hasEigenvalue G hconn hdeg, minus_hasEigenvalue G hconn hdeg hbip,
    plus_eigenspace_finrank G hconn hdeg, minus_eigenspace_finrank G hconn hdeg hbip, ?_⟩
  intro μ hμ hμ1 hμneg1
  have hupper := eigenvalue_le_of_ne_one G hdeg η hη hη2 hcut μ hμ hμ1
  have hneg := neg_hasEigenvalue_of_bipartite G hbip μ hμ
  have hneg1 : -μ ≠ 1 := by intro he; apply hμneg1; linarith
  have hlower := eigenvalue_le_of_ne_one G hdeg η hη hη2 hcut (-μ) hneg hneg1
  exact abs_le.mpr ⟨by linarith only [hlower], hupper⟩

end Erdos642.CampaignFe72210bContinuation3.GraphCheegerGap
