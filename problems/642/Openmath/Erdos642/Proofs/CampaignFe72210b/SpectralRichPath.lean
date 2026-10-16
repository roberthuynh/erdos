import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralHostSelfAvoidance
import Openmath.Erdos642.Proofs.CampaignFe72210b.IntegrationParameters
import Openmath.Erdos642.Proofs.CampaignFe72210b.RoundedForestExtraction
import Openmath.Erdos642.Proofs.CampaignFe72210b.TwoWindowTransfer
import Openmath.Erdos642.Proofs.CampaignFe72210b.EventWitness

/-! Actual positive-weight self-avoiding paths rich in two prescribed window pairs. -/
namespace Erdos642.CampaignFe72210b.SpectralRichPath

open Erdos642.FiniteMarkov Erdos642.FiniteMarkov.PathAvoidance

def outerCore (t : ℕ) : ℕ := ((t - 1) + (5 * t + 1)) + (t - 1)
def innerCore (t : ℕ) : ℕ := ((t - 1) + 1) + (t - 1)

theorem outer_time (T t : ℕ) (hfit : outerCore t ≤ T) :
    (((T - outerCore t) + (((t - 1) + (5 * t + 1)) + (t - 1))) + 0) = T := by
  change ((T - outerCore t) + outerCore t) + 0 = T
  omega

theorem inner_time (T t : ℕ) (hfit : innerCore t + 2 * t ≤ T) :
    (((T - (innerCore t + 2 * t)) + (((t - 1) + 1) + (t - 1))) + 2 * t) = T := by
  change ((T - (innerCore t + 2 * t)) + innerCore t) + 2 * t = T
  omega

theorem window_fits (T t : ℕ) (ht : 2 ≤ t) (h8 : 8 * t ≤ T + 1) :
    outerCore t ≤ T ∧ innerCore t + 2 * t ≤ T := by
  unfold outerCore innerCore
  omega

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {A B : Finset V} {q m b : ℕ}

/-- Actual outer windows 0..t-1 and 6t..7t-1 in a length-T path. -/
noncomputable def outerCount (F : ForestBundle G A B q m b) (C : Chain V)
    (T t : ℕ) (hfit : outerCore t ≤ T) (x : V) (w : Path V T) : ℝ :=
  F.windowWeightedCountAt C 0 (t - 1) (5 * t + 1) (t - 1) (T - outerCore t) x
    (PathTransport.castPath (outer_time T t hfit).symm w)

/-- Actual inner windows 2t..3t-1 and 3t..4t-1 in a length-T path. -/
noncomputable def innerCount (F : ForestBundle G A B q m b) (C : Chain V)
    (T t : ℕ) (hfit : innerCore t + 2 * t ≤ T) (x : V) (w : Path V T) : ℝ :=
  F.windowWeightedCountAt C (2 * t) (t - 1) 1 (t - 1) (T - (innerCore t + 2 * t)) x
    (PathTransport.castPath (inner_time T t hfit).symm w)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Uniform in the actual starting vertex, with every graph and probability input discharged. -/
theorem exists_spectral_rich_path_from (γ : ℝ) (hhost : SpectralHostPremises G γ) (x : V) :
    let N := Fintype.card V
    let k := spectralBlockLength N γ
    let T := IntegrationParameters.T N k
    let t := IntegrationParameters.t N k
    ∃ A B : Finset V,
      ∃ F : ForestBundle G A B (ForestParameters.q G.minDegree)
          (ForestParameters.m N G.minDegree) (ForestParameters.b G.minDegree),
      ∃ ho : outerCore t ≤ T, ∃ hi : innerCore t + 2 * t ≤ T,
      ∃ w : Path V T,
        0 < (graphChain G (spectral_host_degree_pos G γ hhost)).weight x w ∧
        actualSA x w ∧
        3 * (T : ℝ) ≤ outerCount F (graphChain G (spectral_host_degree_pos G γ hhost)) T t ho x w ∧
        3 * (T : ℝ) ≤ innerCount F (graphChain G (spectral_host_degree_pos G γ hhost)) T t hi x w := by
  classical
  let N := Fintype.card V
  let k := spectralBlockLength N γ
  let T := IntegrationParameters.T N k
  let t := IntegrationParameters.t N k
  let d := G.minDegree
  let hdeg := spectral_host_degree_pos G γ hhost
  let C := graphChain G hdeg
  have hcopy := hhost
  rcases hcopy with ⟨hN3, _hconnected, hbip, hratio, hgap, hd, horder⟩
  have : Nonempty V := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  have hk := spectral_host_two_le_blockLength G γ hhost
  have hkceil : (2 : ℝ) + Real.log (N : ℝ) / γ ≤ (k : ℝ) := Nat.le_ceil _
  have hgk : Real.log (N : ℝ) ≤ γ * (k : ℝ) := by
    have h' : Real.log (N : ℝ) / γ ≤ (k : ℝ) := by linarith
    simpa only [mul_comm] using (div_le_iff₀ hgap.1).mp h'
  have hdA : SpectralParameters.A * (k : ℝ) / γ ≤ (d : ℝ) := hd
  have horderA : SpectralParameters.A * (k : ℝ)^2 ≤ (N : ℝ) := horder
  have hreq := IntegrationParameters.occupation_requirements N d k γ hN3 hk
    hgap.1 hgap.2.1 hgk hdA horderA
  have hthreshold := IntegrationParameters.edge_threshold N d k γ hN3 hk
    hgap.1 hgap.2.1 hdA horderA
  have hgeom := IntegrationParameters.time_geometry N k hk horderA
  have ht : 2 ≤ t := hgeom.2.1
  have h8 : 8 * t ≤ T + 1 := hgeom.2.2.1
  obtain ⟨ho, hi⟩ := window_fits T t ht h8
  have hminNat : ∀ v : V, d ≤ G.degree v := fun v => G.minDegree_le_degree v
  have hmaxNat : ∀ v : V, G.degree v ≤ 100 * d :=
    fun v => (G.degree_le_maxDegree v).trans hratio
  have hmin : ∀ v : V, (d : ℝ) ≤ (G.degree v : ℝ) := by
    intro v
    exact_mod_cast hminNat v
  have hmax : ∀ v : V, (G.degree v : ℝ) ≤ 100 * (d : ℝ) := by
    intro v
    exact_mod_cast hmaxNat v
  obtain ⟨s, r, hsr⟩ := hbip.exists_isBipartiteWith
  let A := s.toFinset
  let B := r.toFinset
  have hbi : G.IsBipartiteWith (A : Set V) (B : Set V) := by simpa [A, B] using hsr
  have hNd := RoundedForestExtraction.two_degree_le_card G A B d (by omega) hminNat hbi
  obtain ⟨F⟩ := RoundedForestExtraction.exists_rounded_forestBundle
    G A B d hreq.1 hminNat hmaxNat hbi
  let delta := Real.exp (-γ * (t : ℝ) / 200000000000000000)
  have habsorb : 400 * (N : ℝ)^2 * Real.exp (-γ * (t : ℝ) / 100000000000000000) ≤ delta := by
    simpa only [delta, neg_mul] using
      IntegrationParameters.absorb_prefactor N (γ * (t : ℝ)) hN3 hreq.2.2
  have houtRaw := ForestBundle.graph_rounded_windowWeightedCountAt_eventMass_le_of_eq d F
    hbi hdeg hreq.1 hNd hmin hmax γ hgap t ht hreq.2.1
    0 (5 * t + 1) (T - outerCore t) T (outer_time T t ho) x
  have hinRaw := ForestBundle.graph_rounded_windowWeightedCountAt_eventMass_le_of_eq d F
    hbi hdeg hreq.1 hNd hmin hmax γ hgap t ht hreq.2.1
    (2 * t) 1 (T - (innerCore t + 2 * t)) T (inner_time T t hi) x
  have houtCore : C.eventMass T
      (fun y w => outerCount F C T t ho y w <
        (d : ℝ) * (t : ℝ)^2 / (1000000000000000000000000 * (N : ℝ))) x ≤
      400 * (N : ℝ)^2 * Real.exp (-γ * (t : ℝ) / 100000000000000000) := by
    simpa only [outerCount] using houtRaw
  have hinCore : C.eventMass T
      (fun y w => innerCount F C T t hi y w <
        (d : ℝ) * (t : ℝ)^2 / (1000000000000000000000000 * (N : ℝ))) x ≤
      400 * (N : ℝ)^2 * Real.exp (-γ * (t : ℝ) / 100000000000000000) := by
    simpa only [innerCount] using hinRaw
  let Eout : V → Path V T → Prop := fun y w => outerCount F C T t ho y w < 3 * (T : ℝ)
  let Ein : V → Path V T → Prop := fun y w => innerCount F C T t hi y w < 3 * (T : ℝ)
  have hout : C.eventMass T Eout x ≤ delta := by
    have hm := C.eventMass_mono Eout
      (fun y w => outerCount F C T t ho y w <
        (d : ℝ) * (t : ℝ)^2 / (1000000000000000000000000 * (N : ℝ)))
      (fun _ _ hw => lt_of_lt_of_le hw hthreshold) x
    exact hm.trans (houtCore.trans habsorb)
  have hin : C.eventMass T Ein x ≤ delta := by
    have hm := C.eventMass_mono Ein
      (fun y w => innerCount F C T t hi y w <
        (d : ℝ) * (t : ℝ)^2 / (1000000000000000000000000 * (N : ℝ)))
      (fun _ _ hw => lt_of_lt_of_le hw hthreshold) x
    exact hm.trans (hinCore.trans habsorb)
  have hunion : C.eventMass T (fun y w => Eout y w ∨ Ein y w) x ≤ 2 * delta := by
    have h := C.eventMass_union_le Eout Ein x
    linarith
  have hstrict := IntegrationParameters.strict_event_intersection N k γ hN3 hk hgap.1 hgk horderA
  have hSA : Real.exp (-6 * SpectralParameters.beta * (SpectralParameters.q N k : ℝ)) ≤
      C.eventMass T actualSA x := spectral_host_self_avoidance G γ hhost x
  have hsep : C.eventMass T (fun y w => Eout y w ∨ Ein y w) x < C.eventMass T actualSA x :=
    lt_of_le_of_lt hunion (lt_of_lt_of_le hstrict hSA)
  obtain ⟨w, hwSA, hwavoid, hwpos⟩ := C.exists_positive_weight_avoiding actualSA
    (fun y w => Eout y w ∨ Ein y w) x hsep
  dsimp only
  refine ⟨A, B, F, ho, hi, w, hwpos, hwSA, ?_, ?_⟩
  · exact le_of_not_gt (fun h => hwavoid (Or.inl h))
  · exact le_of_not_gt (fun h => hwavoid (Or.inr h))

/-- An actual path and bundle exist under exactly the original spectral-host premises. -/
theorem exists_spectral_rich_path (γ : ℝ) (hhost : SpectralHostPremises G γ) :
    let N := Fintype.card V
    let k := spectralBlockLength N γ
    let T := IntegrationParameters.T N k
    let t := IntegrationParameters.t N k
    ∃ A B : Finset V,
      ∃ F : ForestBundle G A B (ForestParameters.q G.minDegree)
          (ForestParameters.m N G.minDegree) (ForestParameters.b G.minDegree),
      ∃ ho : outerCore t ≤ T, ∃ hi : innerCore t + 2 * t ≤ T,
      ∃ x : V, ∃ w : Path V T,
        0 < (graphChain G (spectral_host_degree_pos G γ hhost)).weight x w ∧
        actualSA x w ∧
        3 * (T : ℝ) ≤ outerCount F (graphChain G (spectral_host_degree_pos G γ hhost)) T t ho x w ∧
        3 * (T : ℝ) ≤ innerCount F (graphChain G (spectral_host_degree_pos G γ hhost)) T t hi x w := by
  classical
  have hN3 : 3 ≤ Fintype.card V := hhost.1
  have : Nonempty V := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  let x : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨A, B, F, ho, hi, w, hwpos, hwSA, hout, hin⟩ :=
    exists_spectral_rich_path_from G γ hhost x
  exact ⟨A, B, F, ho, hi, x, w, hwpos, hwSA, hout, hin⟩

end Erdos642.CampaignFe72210b.SpectralRichPath
