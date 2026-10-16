import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.FourthHeatKernel
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.FourthSpectralSum

/-! Actual diagonal fourth-energy heat kernel with exact similarity cancellation. -/
namespace Erdos642.CampaignFe72210bContinuation3
open Erdos642.CampaignFe72210b

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Genuine uniform fourth-return control smooths the actual residual spectrum. -/
theorem graphTransition_pow_fourth_diagonal_heatKernel (γ d R Λ : ℝ)
    (hgap : HasBipartiteSpectralGap G γ) (hbip : G.IsBipartite)
    (hd : 0 < d) (hR : 1 ≤ R)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ R * d)
    (hmoment : ∀ z : V, (graphTransition G ^ 4) z z ≤ Λ / d ^ 2)
    (t : ℕ) (ht : 4 ≤ t) (x : V) :
    (graphTransition G ^ t) x x ≤
      2 * R / (Fintype.card V : ℝ) + Λ * (1 - γ) ^ (t - 4) / d ^ 2 := by
  classical
  rcases hgap with ⟨_hγpos, hγone, _hOne, _hMinus, hsp, hsm, hrest⟩
  have hρ : 0 ≤ 1 - γ := sub_nonneg.mpr hγone
  have hdeg : ∀ z : V, 0 < G.degree z := by
    intro z
    exact_mod_cast lt_of_lt_of_le hd (hmin z)
  obtain ⟨σ, hσ, hflip⟩ := exists_bipartite_sign G hbip
  let B := normalizedAdjacency G
  let hB : B.IsHermitian := normalizedAdjacency_isHermitian G
  let wplus : EuclideanSpace ℝ V := WithLp.toLp 2 (unitDegreeRoot G)
  let wminus : EuclideanSpace ℝ V := WithLp.toLp 2 (signedUnitDegreeRoot G σ)
  have hwplus : B.toEuclideanLin wplus = (1 : ℝ) • wplus := by
    apply PiLp.ext
    intro z
    change (normalizedAdjacency G *ᵥ unitDegreeRoot G) z = (1 : ℝ) * unitDegreeRoot G z
    simpa only [one_mul] using congrFun (normalizedAdjacency_unitDegreeRoot G hdeg) z
  have hwminus : B.toEuclideanLin wminus = (-1 : ℝ) • wminus := by
    apply PiLp.ext
    intro z
    change (normalizedAdjacency G *ᵥ signedUnitDegreeRoot G σ) z =
      (-1 : ℝ) * signedUnitDegreeRoot G σ z
    simpa using congrFun (normalizedAdjacency_signedUnitDegreeRoot G hdeg σ hflip) z
  have hunitplus : ‖wplus‖ = 1 := unitDegreeRoot_euclidean_norm G hdeg
  have hunitminus : ‖wminus‖ = 1 := signedUnitDegreeRoot_euclidean_norm G hdeg σ hσ
  let K : Finset V := Finset.univ.filter
    (fun j => hB.eigenvalues j ≠ 1 ∧ hB.eigenvalues j ≠ -1)
  let E : ℝ := ∑ j ∈ K, (hB.eigenvalues j) ^ t *
    (hB.eigenvectorBasis j) x * (hB.eigenvectorBasis j) x
  let c : ℝ := Real.sqrt (G.degree x : ℝ) / Real.sqrt (G.degree x : ℝ)
  let m : ℝ := (G.degree x : ℝ) / degreeVolume G
  let coef : ℝ := (-1 : ℝ) ^ t * σ x * σ x
  have hActual (j : V) :
      Module.End.HasEigenvalue B.toEuclideanLin (hB.eigenvalues j) := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    change hB.eigenvalues j ∈ spectrum ℝ (Matrix.toLpLin 2 2 B)
    rw [Matrix.spectrum_toLpLin]
    exact hB.eigenvalues_mem_spectrum_real j
  have hgapK : ∀ j ∈ K, |hB.eigenvalues j| ≤ 1 - γ := by
    intro j hj
    have hjrest := (Finset.mem_filter.mp hj).2
    exact hrest _ (hActual j) hjrest.1 hjrest.2
  have hraw : |E| ≤ (1 - γ) ^ (t - 4) *
      Real.sqrt ((B ^ 4) x x) * Real.sqrt ((B ^ 4) x x) :=
    hermitian_partial_spectral_sum_fourth_step_bound B hB K (1 - γ) hρ t ht hgapK x x
  have hdiag (z : V) : (B ^ 4) z z = (graphTransition G ^ 4) z z := by
    have hh := graphTransition_pow_normalized G hdeg 4 z z
    simpa only [div_self (ne_of_gt (degree_sqrt_pos G hdeg z)), one_mul] using hh.symm
  have hxenergy : (B ^ 4) x x ≤ Λ / d ^ 2 := by rw [hdiag]; exact hmoment x
  have hyenergy : (B ^ 4) x x ≤ Λ / d ^ 2 := by rw [hdiag]; exact hmoment x
  have hΛdiv : 0 ≤ Λ / d ^ 2 := by
    apply le_trans _ hxenergy
    rw [← hermitian_eigenbasis_fourth_energy_eq_diagonal B hB x]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hΛ0 : 0 ≤ Λ := by
    have hh := mul_nonneg hΛdiv (sq_nonneg d)
    rwa [div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hd))] at hh
  have hE : |E| ≤ Λ * (1 - γ) ^ (t - 4) / d ^ 2 := by
    calc
      |E| ≤ (1 - γ) ^ (t - 4) *
          Real.sqrt ((B ^ 4) x x) * Real.sqrt ((B ^ 4) x x) := hraw
      _ ≤ (1 - γ) ^ (t - 4) * Real.sqrt (Λ / d ^ 2) * Real.sqrt (Λ / d ^ 2) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxenergy) (pow_nonneg hρ _))
          (Real.sqrt_le_sqrt hyenergy) (Real.sqrt_nonneg _)
          (mul_nonneg (pow_nonneg hρ _) (Real.sqrt_nonneg _))
      _ = Λ * (1 - γ) ^ (t - 4) / d ^ 2 := by
        rw [mul_assoc, Real.mul_self_sqrt hΛdiv]
        ring
  have hentry : (graphTransition G ^ t) x x = m * (1 + coef) + c * E := by
    have hpow := graphTransition_pow_normalized G hdeg t x x
    have hsplit := hermitian_pow_entry_split_trivial B hB wplus wminus
      hsp hsm hwplus hwminus hunitplus hunitminus t x x
    change (graphTransition G ^ t) x x = c * (B ^ t) x x at hpow
    rw [hpow, hsplit]
    change c * (unitDegreeRoot G x * unitDegreeRoot G x +
      (-1 : ℝ) ^ t * signedUnitDegreeRoot G σ x * signedUnitDegreeRoot G σ x + E) = _
    have hp := degree_root_projector_similarity G hdeg x x
    have hm := signed_degree_root_projector_similarity G hdeg σ x x
    change c * unitDegreeRoot G x * unitDegreeRoot G x = m at hp
    change c * signedUnitDegreeRoot G σ x * signedUnitDegreeRoot G σ x =
      (σ x * σ x) * m at hm
    calc
      _ = c * unitDegreeRoot G x * unitDegreeRoot G x +
          (-1 : ℝ) ^ t * (c * signedUnitDegreeRoot G σ x *
            signedUnitDegreeRoot G σ x) + c * E := by ring
      _ = m * (1 + coef) + c * E := by
        rw [hp, hm]
        dsimp [coef]
        ring
  have hsignAbs (z : V) : |σ z| = 1 := by
    nlinarith [abs_nonneg (σ z), sq_abs (σ z), hσ z]
  have hcoefAbs : |coef| = 1 := by
    simp [coef, abs_mul, abs_pow, hsignAbs]
  have hcoef : coef ≤ 1 := (le_abs_self coef).trans_eq hcoefAbs
  have hmnonneg : 0 ≤ m :=
    div_nonneg (Nat.cast_nonneg _) (degreeVolume_positive G hdeg).le
  have hmle : m ≤ R / (Fintype.card V : ℝ) := degree_mass_le G d R hd hR hmin hmax x
  have htrivial : m * (1 + coef) ≤ 2 * R / (Fintype.card V : ℝ) := by
    have hperiodic : m * (1 + coef) ≤ 2 * m := by
      nlinarith [mul_le_mul_of_nonneg_left hcoef hmnonneg]
    have hmass : 2 * m ≤ 2 * R / (Fintype.card V : ℝ) := by
      calc
        2 * m ≤ 2 * (R / (Fintype.card V : ℝ)) :=
          mul_le_mul_of_nonneg_left hmle (by norm_num : (0 : ℝ) ≤ 2)
        _ = 2 * R / (Fintype.card V : ℝ) := by ring
    exact hperiodic.trans hmass
  have hcOne : c = 1 := by
    dsimp [c]
    exact div_self (ne_of_gt (degree_sqrt_pos G hdeg x))
  have hscaled : c * E ≤ Λ * (1 - γ) ^ (t - 4) / d ^ 2 := by
    rw [hcOne, one_mul]
    exact (le_abs_self E).trans hE
  rw [hentry]
  exact add_le_add htrivial hscaled

end Erdos642.CampaignFe72210bContinuation3
