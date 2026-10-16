import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphForestOccupation
import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestOccupationParameters

/-! Actual two-window occupation with rounded forest parameters and absorbed constants. -/
namespace Erdos642.CampaignFe72210b.ForestBundle
open Erdos642.FiniteMarkov Erdos642.OccupationTail
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B : Finset V}
variable (d : ℕ)
variable (F : Erdos642.CampaignFe72210b.ForestBundle G A B
  (ForestParameters.q d) (ForestParameters.m (Fintype.card V) d) (ForestParameters.b d))

/-- Rounded bundle occupation under the written graph size and time conditions. -/
theorem graph_rounded_two_window_low_weightedCount_eventMass_le
    (hbi : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hdeg : ∀ x : V, 0 < G.degree x) (hd : 100000000 ≤ d)
    (hN : 2 * d ≤ Fintype.card V)
    (hmin : ∀ x : V, (d : ℝ) ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100 * (d : ℝ))
    (γ : ℝ) (hgap : HasBipartiteSpectralGap G γ)
    (t : ℕ) (ht : 2 ≤ t)
    (hlarge : 1000000000000000000 ≤ (d : ℝ) * γ * (t : ℝ) / (Fintype.card V : ℝ))
    (g : ℕ) (x : V) :
    (graphChain G hdeg).eventMass (((t - 1) + g) + (t - 1))
      (fun _ w => F.windowWeightedCount (graphChain G hdeg) (t - 1) g (t - 1) x w <
        (d : ℝ) * (t : ℝ)^2 / (1000000000000000000000000 * (Fintype.card V : ℝ))) x ≤
      400 * (Fintype.card V : ℝ)^2 *
        Real.exp (-γ * (t : ℝ) / 100000000000000000) := by
  have hdp : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hb : 1 ≤ ForestParameters.b d := by
    have hh := ForestParameters.ten_le_b d hd
    omega
  have hm := (ForestParameters.m_bounds (Fintype.card V) d hd hN).1
  have hh := F.graph_two_window_low_weightedCount_eventMass_le
    hbi hdeg (d : ℝ) hdp hmin hmax γ hgap hb hm t ht g x
  have hthreshold := ForestOccupationParameters.threshold_product (Fintype.card V) d t hd hN
  have hmono := (graphChain G hdeg).eventMass_mono
    (fun _ w => F.windowWeightedCount (graphChain G hdeg) (t - 1) g (t - 1) x w <
      (d : ℝ) * (t : ℝ)^2 / (1000000000000000000000000 * (Fintype.card V : ℝ)))
    (fun _ w => F.windowWeightedCount (graphChain G hdeg) (t - 1) g (t - 1) x w <
      ((t : ℝ) * (ForestParameters.b d : ℝ) / (600 * (Fintype.card V : ℝ))) *
        ((t : ℝ) * (ForestOccupationParameters.u (Fintype.card V) d : ℝ) /
          (300 * (Fintype.card V : ℝ))))
    (fun _ _ hw => lt_of_lt_of_le hw hthreshold) x
  refine hmono.trans (hh.trans ?_)
  have hr := ForestOccupationParameters.raw_failure_bound (Fintype.card V) d t γ hd hN hgap.1 ht hlarge
  simpa only [ForestOccupationParameters.u, ForestOccupationParameters.h, Nat.cast_mul, mul_assoc] using hr

end Erdos642.CampaignFe72210b.ForestBundle
