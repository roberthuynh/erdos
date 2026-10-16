import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentTwoWindow
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentRarityParameters
import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralRichPath

/-! One actual positive-weight SA path with both moment-host window counts. -/
namespace Erdos642.CampaignFe72210bContinuation3.MomentRichPath
open Erdos642.FiniteMarkov Erdos642.FiniteMarkov.PathAvoidance
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210b.SpectralRichPath
variable {V : Type*} [Fintype V] [DecidableEq V]

structure StrongMomentHostPremises (G : SimpleGraph V) [DecidableRel G.Adj] (γ Λ : ℝ) : Prop where
  order : 3 ≤ Fintype.card V
  connected : G.Connected
  bipartite : G.IsBipartite
  ratio : G.maxDegree ≤ 100*G.minDegree
  gap : HasBipartiteSpectralGap G γ
  momentParameter : 1 ≤ Λ
  moment : ∀ x, (graphTransition G^4) x x ≤ Λ/(G.minDegree:ℝ)^2
  degreeScale : MomentSAParameters.A*(spectralBlockLength (Fintype.card V) γ:ℝ)*
    Real.log (Fintype.card V:ℝ) ≤ (G.minDegree:ℝ)
  orderScale : MomentSAParameters.A*(spectralBlockLength (Fintype.card V) γ:ℝ)^2*
    Real.log (Fintype.card V:ℝ) ≤ (Fintype.card V:ℝ)
  momentScale : MomentSAParameters.A*Λ*(spectralBlockLength (Fintype.card V) γ:ℝ)*
    Real.log (Fintype.card V:ℝ) ≤ (G.minDegree:ℝ)^2*γ

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem degree_pos (γ Λ : ℝ) (hhost : StrongMomentHostPremises G γ Λ) :
    ∀ x : V, 0 < G.degree x := by
  have hh := MomentHostParameters.strong_reductions (Fintype.card V) G.minDegree hhost.order γ Λ
    hhost.gap.1 hhost.gap.2.1 hhost.momentParameter hhost.degreeScale hhost.orderScale hhost.momentScale
  intro x
  exact lt_of_lt_of_le (by omega : 0<G.minDegree) (G.minDegree_le_degree x)

/-- All graph and probability suppliers are discharged; the returned path is shared by both pairs. -/
theorem exists_moment_rich_path_from (γ Λ : ℝ) (hhost : StrongMomentHostPremises G γ Λ) (x : V) :
    let N := Fintype.card V
    let T := MomentHostParameters.T N γ
    let t := MomentHostParameters.t N γ
    ∃ A B : Finset V,
      ∃ F : ForestBundle G A B (ForestParameters.q G.minDegree)
        (ForestParameters.m N G.minDegree) (ForestParameters.b G.minDegree),
      ∃ ho : outerCore t ≤ T, ∃ hi : innerCore t+2*t ≤ T,
      ∃ w : Path V T,
      0 < (graphChain G (degree_pos G γ Λ hhost)).weight x w ∧ actualSA x w ∧
      3*(T:ℝ) ≤ outerCount F (graphChain G (degree_pos G γ Λ hhost)) T t ho x w ∧
      3*(T:ℝ) ≤ innerCount F (graphChain G (degree_pos G γ Λ hhost)) T t hi x w := by
  classical
  let N := Fintype.card V
  let d := G.minDegree
  let T := MomentHostParameters.T N γ
  let t := MomentHostParameters.t N γ
  let hdeg := degree_pos G γ Λ hhost
  let C := graphChain G hdeg
  have : Nonempty V := ⟨x⟩
  have hred := MomentHostParameters.strong_reductions N d hhost.order γ Λ hhost.gap.1 hhost.gap.2.1
    hhost.momentParameter hhost.degreeScale hhost.orderScale hhost.momentScale
  have hblocks := MomentHostParameters.block_length_bounds N hhost.order γ hhost.gap.1 hhost.gap.2.1
  have hgeom := MomentHostParameters.time_bounds N γ (by omega) hred.2.2.1
  have ht : 2 ≤ t := hgeom.2.1
  have h8 : 8*t ≤ T+1 := hgeom.2.2.1
  obtain ⟨ho,hi⟩ := window_fits T t ht h8
  have hmin : ∀ z, d ≤ G.degree z := fun z => G.minDegree_le_degree z
  have hmax : ∀ z, G.degree z ≤ 100*d :=
    fun z => (G.degree_le_maxDegree z).trans hhost.ratio
  obtain ⟨s,r,hbi0⟩ := hhost.bipartite.exists_isBipartiteWith
  let A := s.toFinset
  let B := r.toFinset
  have hbi : G.IsBipartiteWith (A:Set V) (B:Set V) := by simpa [A,B] using hbi0
  obtain ⟨F⟩ := RoundedForestExtraction.exists_rounded_forestBundle G A B d hred.1 hmin hmax hbi
  let threshold : ℝ := (d:ℝ)*(t:ℝ)^2/((10:ℝ)^24*(N:ℝ))
  let error : ℝ := (Real.exp (-(t:ℝ)/(2*(10:ℝ)^35*Real.log (N:ℝ)))+
    Real.exp (-γ*(t:ℝ)/(2*(10:ℝ)^21)))+Real.exp (-γ*(t:ℝ)/(8*(10:ℝ)^14))
  have hcore : ∀ g y, C.eventMass (((t-1)+g)+(t-1))
      (fun z w => F.windowWeightedCount C (t-1) g (t-1) z w < threshold) y ≤ error := by
    intro g y
    exact MomentTwoWindow.graph_two_window_absorbed G A B hbi d γ Λ hdeg hhost.order hhost.gap
      hhost.momentParameter hmin hmax hhost.moment hhost.degreeScale hhost.orderScale hhost.momentScale F g y
  have hoff : ∀ off g suffix y, C.eventMass ((suffix+(((t-1)+g)+(t-1)))+off)
      (fun z w => F.windowWeightedCountAt C off (t-1) g (t-1) suffix z w < threshold) y ≤ error := by
    intro off g suffix y
    exact F.windowWeightedCountAt_eventMass_le C off (t-1) g (t-1) suffix threshold error (hcore g) y
  have houtRaw := hoff 0 (5*t+1) (T-outerCore t) x
  have hinRaw := hoff (2*t) 1 (T-(innerCore t+2*t)) x
  have hout : C.eventMass T (fun y w => outerCount F C T t ho y w < threshold) x ≤ error := by
    dsimp only [outerCount]
    have hh := C.eventMass_castPath (outer_time T t ho)
      (fun y w => F.windowWeightedCountAt C 0 (t-1) (5*t+1) (t-1) (T-outerCore t) y w < threshold) x
    exact hh.le.trans houtRaw
  have hin : C.eventMass T (fun y w => innerCount F C T t hi y w < threshold) x ≤ error := by
    dsimp only [innerCount]
    have hh := C.eventMass_castPath (inner_time T t hi)
      (fun y w => F.windowWeightedCountAt C (2*t) (t-1) 1 (t-1) (T-(innerCore t+2*t)) y w < threshold) x
    exact hh.le.trans hinRaw
  have hthreshold : 3*(T:ℝ) ≤ threshold :=
    MomentPairParameters.weighted_threshold_ge_three_time N d hhost.order γ hhost.gap.1 hhost.gap.2.1
      hhost.degreeScale hhost.orderScale
  let Eout : V → Path V T → Prop := fun y w => outerCount F C T t ho y w < 3*(T:ℝ)
  let Ein : V → Path V T → Prop := fun y w => innerCount F C T t hi y w < 3*(T:ℝ)
  have hoBad : C.eventMass T Eout x ≤ error :=
    (C.eventMass_mono Eout _ (fun _ _ h => h.trans_le hthreshold) x).trans hout
  have hiBad : C.eventMass T Ein x ≤ error :=
    (C.eventMass_mono Ein _ (fun _ _ h => h.trans_le hthreshold) x).trans hin
  have hrates := MomentRarityParameters.three_rates N hhost.order γ hhost.gap.1 hhost.gap.2.1 hhost.orderScale
  have herror : error ≤ 3*Real.exp (-12*MomentSAParameters.beta*(MomentHostParameters.q N γ:ℝ)) := by
    dsimp [error]
    linarith [hrates.1,hrates.2.1,hrates.2.2]
  have hunion : C.eventMass T (fun y w => Eout y w ∨ Ein y w) x ≤
      6*Real.exp (-12*MomentSAParameters.beta*(MomentHostParameters.q N γ:ℝ)) := by
    have hh := C.eventMass_union_le Eout Ein x
    linarith
  have hminR : ∀ z, (d:ℝ) ≤ (G.degree z:ℝ) := by intro z; exact_mod_cast hmin z
  have hmaxR : ∀ z, (G.degree z:ℝ) ≤ 100*(d:ℝ) := by intro z; exact_mod_cast hmax z
  have hSA : Real.exp (-6*MomentSAParameters.beta*(MomentHostParameters.q N γ:ℝ)) ≤ C.eventMass T actualSA x := by
    exact graph_moment_self_avoidance_exp G γ (d:ℝ) Λ hhost.order hhost.gap hhost.bipartite
      (by exact_mod_cast (show 0<d by omega)) hhost.momentParameter hminR hmaxR hhost.moment
      hhost.degreeScale hhost.momentScale hhost.orderScale x
  have hstrict := MomentRarityParameters.strict_intersection N hhost.order γ hhost.gap.1 hhost.gap.2.1 hhost.orderScale
  have hsep := lt_of_le_of_lt hunion (lt_of_lt_of_le hstrict hSA)
  obtain ⟨w,hwSA,hwavoid,hwpos⟩ := C.exists_positive_weight_avoiding actualSA
    (fun y w => Eout y w ∨ Ein y w) x hsep
  refine ⟨A,B,F,ho,hi,w,hwpos,hwSA,?_,?_⟩
  · exact le_of_not_gt (fun h => hwavoid (Or.inl h))
  · exact le_of_not_gt (fun h => hwavoid (Or.inr h))

/-- An actual common full path exists under only the strong moment-host premises. -/
theorem exists_moment_rich_path (γ Λ : ℝ) (hhost : StrongMomentHostPremises G γ Λ) :
    let N := Fintype.card V
    let T := MomentHostParameters.T N γ
    let t := MomentHostParameters.t N γ
    ∃ A B : Finset V,
      ∃ F : ForestBundle G A B (ForestParameters.q G.minDegree)
        (ForestParameters.m N G.minDegree) (ForestParameters.b G.minDegree),
      ∃ ho : outerCore t ≤ T, ∃ hi : innerCore t+2*t ≤ T,
      ∃ x : V, ∃ w : Path V T,
      0 < (graphChain G (degree_pos G γ Λ hhost)).weight x w ∧ actualSA x w ∧
      3*(T:ℝ) ≤ outerCount F (graphChain G (degree_pos G γ Λ hhost)) T t ho x w ∧
      3*(T:ℝ) ≤ innerCount F (graphChain G (degree_pos G γ Λ hhost)) T t hi x w := by
  have : Nonempty V := Fintype.card_pos_iff.mp (show 0<Fintype.card V by have := hhost.order; omega)
  let x : V := Classical.choice inferInstance
  obtain ⟨A,B,F,ho,hi,w,hwpos,hwSA,hout,hin⟩ := exists_moment_rich_path_from G γ Λ hhost x
  exact ⟨A,B,F,ho,hi,x,w,hwpos,hwSA,hout,hin⟩
end Erdos642.CampaignFe72210bContinuation3.MomentRichPath
