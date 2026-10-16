import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentRichPath
import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralCycleProof

/-! The strong actual moment-host theorem, with literal simple cycle and actual chords. -/
namespace Erdos642.CampaignFe72210bContinuation3.MomentCycleProof
open Erdos642.CampaignFe72210b Erdos642.FiniteMarkov
open MomentRichPath Erdos642.CampaignFe72210b.SpectralRichPath
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem moment_host_has_rich_cycle (γ Λ : ℝ) (hhost : StrongMomentHostPremises G γ Λ) :
    HasRichCycle G := by
  classical
  let N := Fintype.card V
  let T := MomentHostParameters.T N γ
  let t := MomentHostParameters.t N γ
  have hred := MomentHostParameters.strong_reductions N G.minDegree hhost.order γ Λ
    hhost.gap.1 hhost.gap.2.1 hhost.momentParameter hhost.degreeScale hhost.orderScale hhost.momentScale
  have hb := MomentHostParameters.block_length_bounds N hhost.order γ hhost.gap.1 hhost.gap.2.1
  have hg := MomentHostParameters.time_bounds N γ (by omega) hred.2.2.1
  obtain ⟨A,B,F,ho,hi,x,w,hw,hSA,hout,hin⟩ := exists_moment_rich_path G γ Λ hhost
  exact rich_cycle_of_actual_window_counts G (degree_pos G γ Λ hhost) F T t hg.2.1 hg.1
    (by have := hg.2.2.1; omega) (outer_time T t ho) (inner_time T t hi) x w hw hSA hout hin
end Erdos642.CampaignFe72210bContinuation3.MomentCycleProof
