import Openmath.Erdos642.Proofs.CampaignFe72210b.OffsetEdgeGeometry
import Openmath.Erdos642.Proofs.CampaignFe72210b.FourIntervalCycle
import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralRichPath

/-! Deterministic actual-path assembly and the faithful spectral-host cycle theorem. -/
namespace Erdos642.CampaignFe72210b
open Erdos642.FiniteMarkov Erdos642.FiniteMarkov.PathCoordinates
open Erdos642.FiniteMarkov.PathAvoidance
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Actual positive-weight SA and literal outer/middle counts suffice for the cycle step. -/
theorem rich_cycle_of_actual_window_counts
    (hdeg : ∀ x : V, 0 < G.degree x) {A B : Finset V} {q m b : ℕ}
    (F : ForestBundle G A B q m b) (T t : ℕ) (ht : 2 ≤ t) (hT : 16 ≤ T)
    (hfit : 7 * t ≤ T + 1)
    (hO : ((T - (((t - 1) + (5 * t + 1)) + (t - 1))) +
      (((t - 1) + (5 * t + 1)) + (t - 1))) + 0 = T)
    (hI : ((T - ((((t - 1) + 1) + (t - 1)) + 2 * t)) +
      (((t - 1) + 1) + (t - 1))) + 2 * t = T)
    (x : V) (w : Path V T) (hw : 0 < (graphChain G hdeg).weight x w)
    (hSA : actualSA x w)
    (houter : 3 * (T : ℝ) ≤ F.windowWeightedCountAt (graphChain G hdeg)
      0 (t - 1) (5 * t + 1) (t - 1)
      (T - (((t - 1) + (5 * t + 1)) + (t - 1))) x (PathTransport.castPath hO.symm w))
    (hinner : 3 * (T : ℝ) ≤ F.windowWeightedCountAt (graphChain G hdeg)
      (2 * t) (t - 1) 1 (t - 1)
      (T - ((((t - 1) + 1) + (t - 1)) + 2 * t)) x (PathTransport.castPath hI.symm w)) :
    HasRichCycle G := by
  let C := graphChain G hdeg
  let p := positiveWalk G hdeg x w hw
  have hp : p.IsPath := positiveWalk_isPath G hdeg x w hw (by
    rw [nodeList_eq_observations]
    exact hSA)
  have hlen : p.length = T := positiveWalk_length G hdeg x w hw
  let O := F.pairEdgesAtOfEq C 0 (t - 1) (5 * t + 1) (t - 1)
    (T - (((t - 1) + (5 * t + 1)) + (t - 1))) T hO x w
  let I := F.pairEdgesAtOfEq C (2 * t) (t - 1) 1 (t - 1)
    (T - ((((t - 1) + 1) + (t - 1)) + 2 * t)) T hI x w
  have hOeq := F.windowWeightedCountAt_eq_pairEdgesAt_of_eq C 0 (t - 1)
    (5 * t + 1) (t - 1) (T - (((t - 1) + (5 * t + 1)) + (t - 1))) T hO x w hSA
  have hIeq := F.windowWeightedCountAt_eq_pairEdgesAt_of_eq C (2 * t) (t - 1)
    1 (t - 1) (T - ((((t - 1) + 1) + (t - 1)) + 2 * t)) T hI x w hSA
  have hOcardR : 3 * (T : ℝ) ≤ (O.card : ℝ) := houter.trans hOeq.le
  have hIcardR : 3 * (T : ℝ) ≤ (I.card : ℝ) := hinner.trans hIeq.le
  have hOcard : 3 * T ≤ O.card := by exact_mod_cast hOcardR
  have hIcard : 3 * T ≤ I.card := by exact_mod_cast hIcardR
  have hOne : O.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, j, _, hi, hj0, hj1, hadj⟩ := F.closing_indices_of_pairEdgesAtOfEq_nonempty
    C 0 (t - 1) (5 * t + 1) (t - 1)
    (T - (((t - 1) + (5 * t + 1)) + (t - 1))) T hO x w hOne
  have hclose : ∃ i j : ℕ, i < t ∧ 6 * t ≤ j ∧ j < 7 * t ∧
      G.Adj (p.getVert i) (p.getVert j) := by
    refine ⟨i, j, by omega, by omega, by omega, ?_⟩
    simpa only [p, positiveWalk_getVert] using hadj
  apply four_interval_rich_cycle p hp t ht (by omega) (by omega) hclose I
  · intro u v he
    obtain ⟨hadj, ⟨i, hi0, hi1, hei⟩, ⟨j, hj0, hj1, hej⟩⟩ :=
      F.pairEdgesAtOfEq_supported C (2 * t) (t - 1) 1 (t - 1)
        (T - ((((t - 1) + 1) + (t - 1)) + 2 * t)) T hI x w u v he
    refine ⟨hadj, ⟨i, hi0, by omega, ?_⟩, ⟨j, hj0, by omega, ?_⟩⟩
    · simpa only [p, positiveWalk_getVert] using hei
    · simpa only [p, positiveWalk_getVert] using hej
  · simpa only [hlen] using hIcard

/-- The reviewed spectral-host premises yield a literal rich simple cycle. -/
theorem spectral_host_has_rich_cycle (γ : ℝ) (hhost : SpectralHostPremises G γ) :
    HasRichCycle G := by
  classical
  let N := Fintype.card V
  let k := spectralBlockLength N γ
  let T := IntegrationParameters.T N k
  let t := IntegrationParameters.t N k
  have hk := spectral_host_two_le_blockLength G γ hhost
  have horder : SpectralParameters.A * (k : ℝ)^2 ≤ (N : ℝ) := hhost.2.2.2.2.2.2
  have hgeom := IntegrationParameters.time_geometry N k hk horder
  have ht : 2 ≤ t := hgeom.2.1
  have hT : 16 ≤ T := hgeom.1
  have h8 : 8 * t ≤ T + 1 := hgeom.2.2.1
  obtain ⟨A, B, F, ho, hi, x, w, hw, hSA, houter, hinner⟩ :=
    SpectralRichPath.exists_spectral_rich_path G γ hhost
  exact rich_cycle_of_actual_window_counts G (spectral_host_degree_pos G γ hhost)
    F T t ht hT (by omega) (SpectralRichPath.outer_time T t ho)
    (SpectralRichPath.inner_time T t hi) x w hw hSA houter hinner

/-- The faithful parent proposition, with no additional host hypotheses. -/
theorem spectral_cycle_claim : SpectralCycleClaim (V := V) := by
  intro G _ γ hhost
  exact spectral_host_has_rich_cycle G γ hhost

end Erdos642.CampaignFe72210b
