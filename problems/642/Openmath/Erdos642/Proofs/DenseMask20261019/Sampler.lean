import Openmath.Erdos642.Proofs.DenseMask20261019.UpperObstruction
import Openmath.Erdos642.Proofs.DenseMask20261019.SamplingParameters
import Openmath.Erdos642.Proofs.DenseMask20261019.InitialMass

/-! The full avoidance-conditioned iid vertex sampler, with all probability suppliers paid. -/
noncomputable section
namespace Erdos642.DenseMask20261019.Sampler
open Finset SimpleGraph MeasureTheory ProbabilityTheory Real
open OAI.ErdosGallai.Sampling
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.CutExtraction
open Erdos642.DenseMask20261019
open FixedObstruction GlobalObstruction ComponentObstruction AvoidanceOrder InitialMass
attribute [local instance] Classical.propDecidable

/-- Constants depend only on D and a, not on graph order or its sampling rate.
Every event refers to the actual original graph and iid vertex sample. -/
theorem exists_sampler_constants (D a : ℝ) (hD : 1 ≤ D) (ha : 0 < a) :
    ∃ K epsilon : ℝ, 1000000 ≤ K ∧ 0 < epsilon ∧ 16*D*epsilon ≤ 1/10 ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬HasRichCycle G →
    ∀ (p : unitInterval) (d lam L : ℝ),
      2 ≤ Fintype.card V → 0 < (p : ℝ) → 0 < d → 0 < lam → lam ≤ 1 →
      CutEscape.Expands G lam →
      (∀ v, d ≤ (G.degree v : ℝ)) → (∀ v, (G.degree v : ℝ) ≤ D*d) →
      log (2*Fintype.card V) ≤ L → K*L ≤ (p : ℝ)*d →
      a/L^2 ≤ (p : ℝ)*lam →
      (sampleMeasure V p).real (sampledExpansionFailure G (epsilon*(p : ℝ)*lam)) <
        1/(Fintype.card V : ℝ)^4 := by
  obtain ⟨C, hC, hlower⟩ := InitialMass.exists_failure_obstruction_constant
  obtain ⟨K, epsilon, hK, heps, hsmall, hcost, hparameters⟩ :=
    SamplingParameters.exists_sampling_parameters C D a hC hD ha
  refine ⟨K, epsilon, hK, heps, hsmall, ?_⟩
  intro V _ _ G _ havoid p d lam L hn hp hd hlam hlam1 hexp hdeg hmax hL hscale hpl
  classical
  let n := Fintype.card V
  let c : ℝ := 1/(64000*D)
  let m := orderLower C (((p : ℝ)*d)/64)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hLpos : 0 < L := (log_pos (by linarith : (1 : ℝ) < 2*n)).trans_le hL
  have hDpos : 0 < D := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hpl0 : 0 < (p : ℝ)*lam := mul_pos hp hlam
  have hpl1 : (p : ℝ)*lam ≤ 1 := by
    calc
      _ ≤ (p : ℝ)*1 := mul_le_mul_of_nonneg_left hlam1 hp.le
      _ ≤ _ := by simpa using p.property.2
  obtain ⟨hm, _, hentropy, hnormal⟩ := hparameters n L (p : ℝ) d lam hn hL hp
    p.property.2 hd hlam hlam1 hscale hpl
  change 0 < m at hm
  change 2*log (Fintype.card V)/m ≤ c*(p : ℝ)*lam/50 at hentropy
  have hs : 0 ≤ epsilon*(p : ℝ)*lam := by positivity
  have hsmall' : 16*D*(epsilon*(p : ℝ)*lam) ≤ 1/10 := by
    have h := mul_le_mul_of_nonneg_right hsmall hpl0.le
    nlinarith
  have hr : 1000000*log (2*Fintype.card V) ≤ (p : ℝ)*d := by
    calc
      _ ≤ 1000000*L := mul_le_mul_of_nonneg_left hL (by norm_num)
      _ ≤ K*L := mul_le_mul_of_nonneg_right hK hLpos.le
      _ ≤ _ := hscale
  apply lt_of_not_ge
  intro hfailure
  obtain ⟨k, hk1, _, hkN, _, hproblo⟩ := hlower V G havoid p d D
    (epsilon*(p : ℝ)*lam) (by omega) hd.le hD hs hsmall' hdeg hmax hr hfailure
  have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpositive : 0 < (1/(4*(Fintype.card V : ℝ)^5))*
      exp (-(1+16*D)*((epsilon*(p : ℝ)*lam)*(k : ℝ))*log 2) := by positivity
  have hne : (obstructionEvent G C ((p : ℝ)*d) D k).Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    rw [he, measureReal_empty] at hproblo
    linarith
  obtain ⟨x, hx⟩ := hne
  have hmk : m ≤ (k : ℝ) := by
    change Obstruction G C ((p : ℝ)*d) (2*D*((p : ℝ)*d)) k _ _ at hx
    exact ObstructionCollections.obstruction_order_le G C ((p : ℝ)*d)
      (2*D*((p : ℝ)*d)) k _ _ hk hx
  have hnormalized : exp (-(c/4)*(p : ℝ)*lam*k) ≤
      (experiment V p).real (obstructionEvent G C ((p : ℝ)*d) D k) := by
    have h := hnormal (k : ℝ) hmk
    exact h.trans hproblo
  have hupper := UpperObstruction.obstruction_probability_upper G C p d D lam k
    hn hp hd hD hlam hlam1 hexp hk hkN hdeg hm hmk
  have hnonneg : 0 ≤ c*(p : ℝ)*lam*(k : ℝ) := by positivity
  have hrate : 2*(k : ℝ)*log (Fintype.card V)/m -
      (p : ℝ)*lam*k/(128000*D) ≤ -(c/3)*(p : ℝ)*lam*k := by
    have he := mul_le_mul_of_nonneg_left hentropy hk.le
    have heq : (p : ℝ)*lam*k/(128000*D) = (c/2)*(p : ℝ)*lam*k := by
      dsimp [c]
      field_simp
      <;> ring
    rw [heq]
    have he' : 2*(k : ℝ)*log (Fintype.card V)/m ≤ c*(p : ℝ)*lam*k/50 := by
      calc
        _ = (k : ℝ)*(2*log (Fintype.card V)/m) := by ring
        _ ≤ (k : ℝ)*(c*(p : ℝ)*lam/50) := he
        _ = _ := by ring
    calc
      _ ≤ c*(p : ℝ)*lam*k/50 - (c/2)*(p : ℝ)*lam*k := sub_le_sub_right he' _
      _ = (-12/25 : ℝ)*(c*(p : ℝ)*lam*k) := by ring
      _ ≤ (-1/3 : ℝ)*(c*(p : ℝ)*lam*k) :=
        mul_le_mul_of_nonneg_right (by norm_num) hnonneg
      _ = _ := by ring
  have hupper' := hupper.trans (exp_le_exp.mpr hrate)
  have hstrict : exp (-(c/3)*(p : ℝ)*lam*k) < exp (-(c/4)*(p : ℝ)*lam*k) := by
    apply exp_lt_exp.mpr
    have hprod : 0 < c*((p : ℝ)*lam)*(k : ℝ) := mul_pos (mul_pos hc hpl0) hk
    nlinarith
  exact (not_lt_of_ge (hnormalized.trans hupper')) hstrict

end Erdos642.DenseMask20261019.Sampler
