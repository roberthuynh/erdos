import Openmath.Erdos642.Proofs.CampaignFe72210b.DegreeRatios
import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphEnergy
import Openmath.Erdos642.Proofs.CampaignFe72210b.BipartiteSigns
import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralEntries
import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralSum

/-! The genuine ordinary graph heat kernel from its original bipartite spectral premise. -/

namespace Erdos642.CampaignFe72210b

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The two trivial eigenspaces retain their exact periodic contribution; all
other eigenvalues are smoothed by the genuine two-step degree energy. -/
theorem graphTransition_pow_heatKernel (γ d R : ℝ)
    (hgap : HasBipartiteSpectralGap G γ) (hbip : G.IsBipartite)
    (hd : 0 < d) (hR : 1 ≤ R)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ R * d)
    (t : ℕ) (ht : 2 ≤ t) (x y : V) :
    (graphTransition G ^ t) x y ≤
      2 * R / (Fintype.card V : ℝ) + Real.sqrt R * (1 - γ) ^ (t - 2) / d := by
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
    (hB.eigenvectorBasis j) x * (hB.eigenvectorBasis j) y
  let c : ℝ := Real.sqrt (G.degree y : ℝ) / Real.sqrt (G.degree x : ℝ)
  let m : ℝ := (G.degree y : ℝ) / degreeVolume G
  let coef : ℝ := (-1 : ℝ) ^ t * σ x * σ y
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
  have hraw : |E| ≤ (1 - γ) ^ (t - 2) *
      Real.sqrt ((B ^ 2) x x) * Real.sqrt ((B ^ 2) y y) :=
    hermitian_partial_spectral_sum_two_step_bound B hB K (1 - γ) hρ t ht hgapK x y
  have hxenergy : (B ^ 2) x x ≤ 1 / d := normalizedAdjacency_sq_diag_le G d hd hmin x
  have hyenergy : (B ^ 2) y y ≤ 1 / d := normalizedAdjacency_sq_diag_le G d hd hmin y
  have hE : |E| ≤ (1 - γ) ^ (t - 2) / d := by
    calc
      |E| ≤ (1 - γ) ^ (t - 2) *
          Real.sqrt ((B ^ 2) x x) * Real.sqrt ((B ^ 2) y y) := hraw
      _ ≤ (1 - γ) ^ (t - 2) * Real.sqrt (1 / d) * Real.sqrt (1 / d) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxenergy) (pow_nonneg hρ _))
          (Real.sqrt_le_sqrt hyenergy) (Real.sqrt_nonneg _)
          (mul_nonneg (pow_nonneg hρ _) (Real.sqrt_nonneg _))
      _ = (1 - γ) ^ (t - 2) / d := by
        rw [mul_assoc, Real.mul_self_sqrt (by positivity : 0 ≤ (1 : ℝ) / d)]
        ring
  have hentry : (graphTransition G ^ t) x y = m * (1 + coef) + c * E := by
    have hpow := graphTransition_pow_normalized G hdeg t x y
    have hsplit := hermitian_pow_entry_split_trivial B hB wplus wminus
      hsp hsm hwplus hwminus hunitplus hunitminus t x y
    change (graphTransition G ^ t) x y = c * (B ^ t) x y at hpow
    rw [hpow, hsplit]
    change c * (unitDegreeRoot G x * unitDegreeRoot G y +
      (-1 : ℝ) ^ t * signedUnitDegreeRoot G σ x * signedUnitDegreeRoot G σ y + E) = _
    have hp := degree_root_projector_similarity G hdeg x y
    have hm := signed_degree_root_projector_similarity G hdeg σ x y
    change c * unitDegreeRoot G x * unitDegreeRoot G y = m at hp
    change c * signedUnitDegreeRoot G σ x * signedUnitDegreeRoot G σ y =
      (σ x * σ y) * m at hm
    calc
      _ = c * unitDegreeRoot G x * unitDegreeRoot G y +
          (-1 : ℝ) ^ t * (c * signedUnitDegreeRoot G σ x *
            signedUnitDegreeRoot G σ y) + c * E := by ring
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
  have hmle : m ≤ R / (Fintype.card V : ℝ) := degree_mass_le G d R hd hR hmin hmax y
  have htrivial : m * (1 + coef) ≤ 2 * R / (Fintype.card V : ℝ) := by
    have hperiodic : m * (1 + coef) ≤ 2 * m := by
      nlinarith [mul_le_mul_of_nonneg_left hcoef hmnonneg]
    have hmass : 2 * m ≤ 2 * R / (Fintype.card V : ℝ) := by
      calc
        2 * m ≤ 2 * (R / (Fintype.card V : ℝ)) :=
          mul_le_mul_of_nonneg_left hmle (by norm_num : (0 : ℝ) ≤ 2)
        _ = 2 * R / (Fintype.card V : ℝ) := by ring
    exact hperiodic.trans hmass
  have hc : 0 ≤ c := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hcratio : c ≤ Real.sqrt R := degree_sqrt_ratio_le G d R hd hR hmin hmax x y
  have hscaled : c * E ≤ Real.sqrt R * (1 - γ) ^ (t - 2) / d := by
    calc
      c * E ≤ c * |E| := mul_le_mul_of_nonneg_left (le_abs_self E) hc
      _ ≤ c * ((1 - γ) ^ (t - 2) / d) := mul_le_mul_of_nonneg_left hE hc
      _ ≤ Real.sqrt R * ((1 - γ) ^ (t - 2) / d) :=
        mul_le_mul_of_nonneg_right hcratio (div_nonneg (pow_nonneg hρ _) hd.le)
      _ = Real.sqrt R * (1 - γ) ^ (t - 2) / d := by ring
  rw [hentry]
  exact add_le_add htrivial hscaled

end Erdos642.CampaignFe72210b
