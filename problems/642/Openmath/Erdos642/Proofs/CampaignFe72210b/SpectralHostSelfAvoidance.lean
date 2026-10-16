import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphSelfAvoidance
import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralParameters

namespace Erdos642.CampaignFe72210b
open Erdos642.FiniteMarkov.PathAvoidance
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem spectral_host_two_le_blockLength (γ : ℝ) (hhost : SpectralHostPremises G γ) :
    2 ≤ spectralBlockLength (Fintype.card V) γ := by
  rcases hhost with ⟨hN, _, _, _, hgap, _, _⟩
  have hN1 : (1:ℝ) ≤ (Fintype.card V:ℝ) := by exact_mod_cast (show 1≤Fintype.card V by omega)
  have hlog := Real.log_nonneg hN1
  have hdiv := div_nonneg hlog hgap.1.le
  have hceil : (2:ℝ)+Real.log (Fintype.card V:ℝ)/γ ≤
      (spectralBlockLength (Fintype.card V) γ:ℝ) := Nat.le_ceil _
  have hk : (2:ℝ) ≤ (spectralBlockLength (Fintype.card V) γ:ℝ) := by linarith
  exact_mod_cast hk

theorem spectral_host_degree_pos (γ : ℝ) (hhost : SpectralHostPremises G γ) :
    ∀ x : V, 0 < G.degree x := by
  have hk := spectral_host_two_le_blockLength G γ hhost
  rcases hhost with ⟨_, _, _, _, hgap, hd, _⟩
  have hd1 := SpectralParameters.degree_pos G.minDegree
    (spectralBlockLength (Fintype.card V) γ) γ hk hgap.1 hd
  intro x
  have hm := G.minDegree_le_degree x
  omega

/-- Actual exponential self-avoidance under exactly the reviewed spectral-host premises. -/
theorem spectral_host_self_avoidance (γ : ℝ) (hhost : SpectralHostPremises G γ) (x : V) :
    let N := Fintype.card V
    let k := spectralBlockLength N γ
    let q := SpectralParameters.q N k
    Real.exp (-6*SpectralParameters.beta*(q:ℝ)) ≤
      (graphChain G (spectral_host_degree_pos G γ hhost)).eventMass (q*k) actualSA x := by
  have hdeg := spectral_host_degree_pos G γ hhost
  have hk := spectral_host_two_le_blockLength G γ hhost
  rcases hhost with ⟨hN, _, hbip, hratio, hgap, hd, horderN⟩
  have : Nonempty V := Fintype.card_pos_iff.mp (show 0<Fintype.card V by omega)
  let N := Fintype.card V
  let k := spectralBlockLength N γ
  let q := SpectralParameters.q N k
  have hmin : ∀ v : V, (G.minDegree:ℝ) ≤ (G.degree v:ℝ) := by
    intro v
    exact_mod_cast G.minDegree_le_degree v
  have hmax : ∀ v : V, (G.degree v:ℝ) ≤ (100:ℝ)*(G.minDegree:ℝ) := by
    intro v
    exact_mod_cast (G.degree_le_maxDegree v).trans hratio
  have hd1nat := SpectralParameters.degree_pos G.minDegree k γ hk hgap.1 hd
  have hd1 : (1:ℝ)≤G.minDegree := by exact_mod_cast hd1nat
  have hq := (SpectralParameters.q_bounds N k hk horderN).1
  have hklog : (2:ℝ)+Real.log (Fintype.card V:ℝ)/γ ≤ (k:ℝ) := Nat.le_ceil _
  have hbeta : 0<SpectralParameters.beta := SpectralParameters.beta_pos
  have hbetaupper : SpectralParameters.beta≤1/6 := by norm_num [SpectralParameters.beta]
  have hsqrt : Real.sqrt (100:ℝ)=10 := by norm_num
  have hHJ :
      ((k:ℝ)/(G.minDegree:ℝ)+2*100*(k:ℝ)^2/(N:ℝ)+
        Real.sqrt 100*(k:ℝ)/((G.minDegree:ℝ)*γ))+
      (2*100*(k:ℝ)^2/(N:ℝ)+Real.sqrt 100*(k:ℝ)/((G.minDegree:ℝ)*γ)) ≤
        SpectralParameters.beta := by
    calc
      _ = (k:ℝ)/(G.minDegree:ℝ)+400*(k:ℝ)^2/(N:ℝ)+
          20*(k:ℝ)/((G.minDegree:ℝ)*γ) := by rw [hsqrt]; ring
      _ ≤ _ := SpectralParameters.local_failure_le_beta N G.minDegree k γ hk
        hgap.1 hgap.2.1 horderN hd
  have horder : (2*(100:ℝ)+Real.sqrt 100)*100*(k:ℝ)*((q*k+1:ℕ):ℝ) ≤
      SpectralParameters.beta^2*(Fintype.card V:ℝ) := by
    have h := SpectralParameters.block_order_bound N k hk horderN
    simpa only [hsqrt, show (2*(100:ℝ)+10)*100=21000 by norm_num] using h
  exact graph_self_avoidance_exp G hdeg γ (G.minDegree:ℝ) 100 hgap hbip
    hd1 (by norm_num) hmin hmax k q hq hklog SpectralParameters.beta hbeta hbetaupper
    hHJ horder x
end Erdos642.CampaignFe72210b
