import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.GraphExpansionConductance
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.GraphCheegerGap

/-! Actual bipartite cardinal cut expansion yields the genuine spectral predicate. -/
namespace Erdos642.CampaignFe72210bContinuation3.GraphExpansionGap
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.GraphExpansionConductance
open Erdos642.CampaignFe72210bContinuation3.GraphCheegerGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Connectedness, conductance, eigenspace simplicity and absolute gap are derived,
not supplied as graph premises. -/
theorem graph_hasBipartiteSpectralGap_of_expansion
    (hdeg : ∀ x : V, 0 < G.degree x) (hbip : G.IsBipartite)
    (K lam : ℝ) (hK : 1 ≤ K) (hlam : 0 < lam) (hlam2 : lam ≤ 2)
    (hratio : (G.maxDegree : ℝ) ≤ K * (G.minDegree : ℝ))
    (hexpand : ∀ S : Finset V, (S.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 →
      lam * (degreeVolume G / (Fintype.card V : ℝ)) * (S.card : ℝ) ≤ crossing G S) :
    HasBipartiteSpectralGap G ((lam / K) ^ 2 / 8) := by
  have hKpos : 0 < K := by linarith
  have heta : 0 < lam / K := div_pos hlam hKpos
  have heta2 : lam / K ≤ 2 := by
    apply (div_le_iff₀ hKpos).mpr
    linarith
  have hconn := expansion_connected G hdeg lam hlam hexpand
  apply graph_hasBipartiteSpectralGap_of_conductance G hconn hbip hdeg
    (lam / K) heta heta2
  intro S _ _
  exact expansion_conductance G K lam hK hlam hratio hexpand S

end Erdos642.CampaignFe72210bContinuation3.GraphExpansionGap
