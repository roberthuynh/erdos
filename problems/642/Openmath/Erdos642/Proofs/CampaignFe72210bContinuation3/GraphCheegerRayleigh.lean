import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.GraphDirichlet
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.WeightedMedian

/-! Actual conductance cut law implies actual normalized mean-zero Rayleigh gap. -/
namespace Erdos642.CampaignFe72210bContinuation3.GraphCheegerRayleigh
open Matrix Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.FiniteCoarea
open Erdos642.CampaignFe72210bContinuation3.GraphDirichlet
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem volume_add_compl (w : V → V → ℝ) (S : Finset V) :
    volume w S + volume w Sᶜ = ∑ x, FiniteCoarea.row w x := by
  classical
  unfold volume
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ S <;> simp [hx]

theorem conductance_half_volume_cut (w : V → V → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hW : 0 < ∑ x, FiniteCoarea.row w x)
    (hcut : ∀ S : Finset V, 0 < volume w S → 0 < volume w Sᶜ →
      η * volume w S * volume w Sᶜ ≤ (∑ x, FiniteCoarea.row w x) * cut w S)
    (S : Finset V) (hS : 0 < volume w S)
    (hhalf : volume w S ≤ (∑ x, FiniteCoarea.row w x) / 2) :
    (η / 2) * volume w S ≤ cut w S := by
  have hc := volume_add_compl w S
  have hSc : (∑ x, FiniteCoarea.row w x) / 2 ≤ volume w Sᶜ := by linarith
  have hScpos : 0 < volume w Sᶜ := lt_of_lt_of_le (half_pos hW) hSc
  have hh := hcut S hS hScpos
  have hb : (∑ x, FiniteCoarea.row w x) * ((η / 2) * volume w S) ≤
      (∑ x, FiniteCoarea.row w x) * cut w S := by
    calc
      _ = (η * volume w S) * ((∑ x, FiniteCoarea.row w x) / 2) := by ring
      _ ≤ (η * volume w S) * volume w Sᶜ :=
        mul_le_mul_of_nonneg_left hSc (mul_nonneg hη hS.le)
      _ ≤ _ := hh
  exact le_of_mul_le_mul_left hb hW

theorem cheeger_gap_pos {η : ℝ} (hη : 0 < η) : 0 < η ^ 2 / 8 := by positivity

theorem cheeger_gap_le_half {η : ℝ} (hη : 0 ≤ η) (hη2 : η ≤ 2) : η ^ 2 / 8 ≤ 1 / 2 := by
  nlinarith

variable (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]

theorem graph_conductance_half_volume_cut (hdeg : ∀ x : V, 0 < G.degree x)
    (η : ℝ) (hη : 0 ≤ η)
    (hcut : ∀ S : Finset V, 0 < volume (adjWeight G) S →
      0 < volume (adjWeight G) Sᶜ →
      η * volume (adjWeight G) S * volume (adjWeight G) Sᶜ ≤
        degreeVolume G * cut (adjWeight G) S)
    (S : Finset V) (hS : 0 < volume (adjWeight G) S)
    (hhalf : volume (adjWeight G) S ≤ degreeVolume G / 2) :
    (η / 2) * volume (adjWeight G) S ≤ cut (adjWeight G) S := by
  apply conductance_half_volume_cut (adjWeight G) η hη (adjWeight_total_pos G hdeg)
  · intro T hT hTc
    simpa only [adjWeight_total] using hcut T hT hTc
  · exact hS
  · simpa only [adjWeight_total] using hhalf

/-- No normalized quadratic or eigenspace conclusion is assumed. -/
theorem graph_cheeger_rayleigh (hdeg : ∀ x : V, 0 < G.degree x)
    (η : ℝ) (hη : 0 < η) (_hη2 : η ≤ 2)
    (hcut : ∀ S : Finset V, 0 < volume (adjWeight G) S →
      0 < volume (adjWeight G) Sᶜ →
      η * volume (adjWeight G) S * volume (adjWeight G) Sᶜ ≤
        degreeVolume G * cut (adjWeight G) S)
    (z : V → ℝ) (hz : dotProduct z (degreeRoot G) = 0) :
    dotProduct z (normalizedAdjacency G *ᵥ z) ≤
      (1 - η ^ 2 / 8) * dotProduct z z := by
  have hm : mass (adjWeight G) (normalizedFunction G z) = 0 := by
    rw [normalizedFunction_mean G hdeg, hz]
  have hr := WeightedMedian.mean_zero_rayleigh (adjWeight G)
    (adjWeight_nonneg G) (adjWeight_symmetric G) (η / 2) (by positivity)
    (normalizedFunction G z) hm (fun S hS hhalf =>
      graph_conductance_half_volume_cut G hdeg η hη.le hcut S hS
        (by simpa only [adjWeight_total] using hhalf))
  rw [normalizedFunction_norm G hdeg, normalized_dirichlet G hdeg] at hr
  nlinarith only [hr]

end Erdos642.CampaignFe72210bContinuation3.GraphCheegerRayleigh
