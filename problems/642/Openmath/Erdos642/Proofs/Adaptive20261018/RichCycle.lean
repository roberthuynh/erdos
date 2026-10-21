import Openmath.Erdos642.Proofs.Adaptive20261018.Windows
import Openmath.Erdos642.Proofs.Adaptive20261018.Parameters
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentRarityParameters
import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralCycleProof

/-! Adaptive-window rarity and actual shared-law rich-cycle closure. -/
namespace Erdos642.Adaptive20261018.RichCycle
open Erdos642.FiniteMarkov Erdos642.FiniteMarkov.PathAvoidance
open Erdos642.CampaignFe72210b Erdos642.CampaignFe72210bContinuation3
open Erdos642.CampaignFe72210b.SpectralRichPath
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem graph_weak_self_avoidance_exp (γ d Λ : ℝ)
    (hN3 : 3 ≤ Fintype.card V) (hgap : HasBipartiteSpectralGap G γ)
    (hbip : G.IsBipartite) (hd : 0 < d) (hΛ : 1 ≤ Λ)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100*d)
    (hmoment : ∀ z : V, (graphTransition G ^ 4) z z ≤ Λ / d ^ 2)
    (hdegree : MomentSAParameters.A * (spectralBlockLength (Fintype.card V) γ : ℝ) ≤ d)
    (hmomentScale : MomentSAParameters.A * Λ * (spectralBlockLength (Fintype.card V) γ : ℝ) ≤ d^2*γ)
    (horder : MomentSAParameters.A * (spectralBlockLength (Fintype.card V) γ : ℝ)^2 ≤ (Fintype.card V : ℝ)) (x : V) :
    let k := spectralBlockLength (Fintype.card V) γ
    let q := MomentSAParameters.q (Fintype.card V) k
    let hdeg : ∀ z : V, 0 < G.degree z := fun z => by
      exact_mod_cast lt_of_lt_of_le hd (hmin z)
    Real.exp (-6*MomentSAParameters.beta*(q:ℝ)) ≤
      (graphChain G hdeg).eventMass (q*k) actualSA x := by
  dsimp only
  let N := Fintype.card V
  let k := spectralBlockLength N γ
  have hell : 1 < Real.log (N:ℝ) := IntegrationParameters.log_order_gt_one N hN3
  have hklog : (2:ℝ)+Real.log (N:ℝ)/γ ≤ (k:ℝ) := Nat.le_ceil _
  have hγ : 0 < γ := hgap.1
  have hγ1 : γ ≤ 1 := hgap.2.1
  have hdiv : 1 < Real.log (N:ℝ)/γ := by
    apply (lt_div_iff₀ hγ).mpr
    nlinarith
  have hkreal : (3:ℝ) < k := by linarith
  have hk : 4 ≤ k := by exact_mod_cast (show 3 < k by exact_mod_cast hkreal)
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hA := MomentSAParameters.A_pos
  have hdBase : MomentSAParameters.A*(k:ℝ) ≤ d := hdegree
  have hNBase : MomentSAParameters.A*(k:ℝ)^2 ≤ (N:ℝ) := horder
  have hMBase : MomentSAParameters.A*Λ*(k:ℝ) ≤ d^2*γ := hmomentScale
  have hd1 : 1 ≤ d := by
    have hA1 : (1:ℝ) ≤ MomentSAParameters.A := by
      exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 10)
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (show 1≤k by omega)
    nlinarith
  have hq := MomentSAParameters.q_bounds N k (by omega) hNBase
  have hHJ := MomentSAParameters.local_failure_le_beta N k d γ Λ (by omega) hd hγ
    (by linarith) hNBase hdBase hMBase
  have hOrd := MomentSAParameters.block_order_bound N k (by omega) hNBase
  let hdeg : ∀ z : V, 0 < G.degree z := fun z => by
    exact_mod_cast lt_of_lt_of_le hd (hmin z)
  apply graph_fourth_self_avoidance_exp G hdeg γ d 100 Λ hgap hbip hd1
    (by norm_num) hmin hmax hmoment k (MomentSAParameters.q N k) hk hq.1 hklog
    MomentSAParameters.beta MomentSAParameters.beta_pos
  · norm_num [MomentSAParameters.beta]
  · norm_num only [show Real.sqrt (100:ℝ) = 10 by norm_num]
    convert hHJ using 1; ring
  · norm_num only [show Real.sqrt (100:ℝ) = 10 by norm_num]
    convert hOrd using 1


open MomentSAParameters MomentHostParameters

theorem weighted_threshold_ge_three_time (N d : ℕ) (hN : 3 ≤ N) (γ : ℝ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hdegree : A*(k N γ:ℝ) ≤ (d:ℝ))
    (horder : A*(k N γ:ℝ)^2*Real.log (N:ℝ) ≤ (N:ℝ)) :
    3*(T N γ:ℝ) ≤ (d:ℝ)*(t N γ:ℝ)^2/((10:ℝ)^24*(N:ℝ)) := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hell := IntegrationParameters.log_order_gt_one N hN
  have hell0 : 0 < Real.log (N:ℝ) := by linarith
  have hA := A_pos
  have ha := a_pos
  have hb := block_length_bounds N hN γ hγ hγ1
  have hk : 0 < (k N γ:ℝ) := by exact_mod_cast (show 0<k N γ by omega)
  have hweak : A*(k N γ:ℝ)^2 ≤ (N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hell.le (show 0≤A*(k N γ:ℝ)^2 by positivity)
    nlinarith only [hh,horder]
  have hg := time_bounds N γ (by omega) hweak
  have hlow1 : (T N γ:ℝ)/16 ≤ (t N γ:ℝ) := hg.2.2.2.1
  have hlow2 : a*(N:ℝ)/(32*(k N γ:ℝ)) ≤ (t N γ:ℝ) := hg.2.2.2.2.1
  have hprod := mul_le_mul hlow1 hlow2
    (show 0≤a*(N:ℝ)/(32*(k N γ:ℝ)) by positivity) (Nat.cast_nonneg _)
  have hts : a*(N:ℝ)*(T N γ:ℝ) ≤ 512*(k N γ:ℝ)*(t N γ:ℝ)^2 := by
    have he : (T N γ:ℝ)/16*(a*(N:ℝ)/(32*(k N γ:ℝ))) =
      a*(N:ℝ)*(T N γ:ℝ)/(512*(k N γ:ℝ)) := by ring
    rw [he] at hprod
    have hh := (div_le_iff₀ (show 0<512*(k N γ:ℝ) by positivity)).mp hprod
    nlinarith
  have hdegreeBase : A*(k N γ:ℝ) ≤ (d:ℝ) := hdegree
  have hc : (1536:ℝ)*(10:ℝ)^24 ≤ a*A :=
    (by norm_num : (1536:ℝ)*(10:ℝ)^24 ≤ (10:ℝ)^40).trans MomentOccupationAbsorption.aA_large
  have hcNT := mul_le_mul_of_nonneg_right hc (show 0≤(N:ℝ)*(T N γ:ℝ) by positivity)
  have hdegreeScaled := mul_le_mul_of_nonneg_right hdegreeBase
    (show 0≤512*(t N γ:ℝ)^2 by positivity)
  have htimeScaled := mul_le_mul_of_nonneg_left hts A_pos.le
  have hfinal : 3*(T N γ:ℝ)*((10:ℝ)^24*(N:ℝ)) ≤ (d:ℝ)*(t N γ:ℝ)^2 := by
    nlinarith only [hcNT,hdegreeScaled,htimeScaled]
  exact (le_div_iff₀ (by positivity : (0:ℝ)<(10:ℝ)^24*(N:ℝ))).mpr hfinal


private theorem rate_bound (q : ℕ) (t ell C : ℝ) (hell : 0<ell) (hC : 0<C)
    (h16 : (q:ℝ)*ell ≤ 16*t) (hc : 384*beta*C ≤ 1) :
    12*beta*(q:ℝ) ≤ t/(2*C*ell) := by
  have hm := mul_le_mul_of_nonneg_right hc (show 0≤(q:ℝ)*ell by positivity)
  apply (le_div_iff₀ (by positivity : 0<2*C*ell)).mpr
  nlinarith only [h16,hm]

theorem three_rates (N : ℕ) (hN : 3≤N) (γ : ℝ) (hγ : 0<γ) (hγ1 : γ≤1)
    (r : ℕ) (hr : 1 ≤ r) (hrk : (r:ℝ) ≤ 27*(k N γ:ℝ))
    (horder : A*(k N γ:ℝ)^2*Real.log (N:ℝ) ≤ (N:ℝ)) :
    Real.exp (-(t N γ:ℝ)/(2*(10:ℝ)^35*(r:ℝ))) ≤ Real.exp (-12*beta*(q N γ:ℝ)) ∧
    Real.exp (-γ*(t N γ:ℝ)/(2*(10:ℝ)^21)) ≤ Real.exp (-12*beta*(q N γ:ℝ)) ∧
    Real.exp (-γ*(t N γ:ℝ)/(8*(10:ℝ)^14)) ≤ Real.exp (-12*beta*(q N γ:ℝ)) := by
  have hell := IntegrationParameters.log_order_gt_one N hN
  have hA := A_pos
  have hb := block_length_bounds N hN γ hγ hγ1
  have hweak : A*(k N γ:ℝ)^2 ≤ (N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hell.le (mul_nonneg hA.le (sq_nonneg (k N γ:ℝ)))
    nlinarith only [hh,horder]
  have ht := (time_bounds N γ (by omega) hweak).2.2.2.1
  have h16 : (q N γ:ℝ)*(k N γ:ℝ) ≤ 16*(t N γ:ℝ) := by
    change ((q N γ*k N γ:ℕ):ℝ)/16 ≤ _ at ht
    push_cast at ht
    linarith only [ht]
  have hq : (0:ℝ) ≤ (q N γ:ℝ) := Nat.cast_nonneg _
  have hf : (q N γ:ℝ)*(r:ℝ) ≤ 432*(t N γ:ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hrk hq
    nlinarith only [hm,h16]
  have hg16 := mul_le_mul_of_nonneg_left h16 hγ.le
  have hgk : (q N γ:ℝ) ≤ (q N γ:ℝ)*(γ*(k N γ:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hb.2.2.1 hq
    nlinarith [hell]
  have hg : (q N γ:ℝ)*1 ≤ 16*(γ*(t N γ:ℝ)) := by nlinarith only [hg16,hgk]
  have hβ := beta_pos
  have hrpos : 0 < (r:ℝ) := by exact_mod_cast (show 0<r by omega)
  have hfast : 12*beta*(q N γ:ℝ) ≤ (t N γ:ℝ)/(2*(10:ℝ)^35*(r:ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0<2*(10:ℝ)^35*(r:ℝ))).mpr
    have hc : 10368*beta*(10:ℝ)^35 ≤ 1 := by norm_num [beta]
    have hm := mul_le_mul_of_nonneg_right hc (show 0≤(t N γ:ℝ) by positivity)
    have hfscaled := mul_le_mul_of_nonneg_left hf (show 0≤24*beta*(10:ℝ)^35 by positivity)
    nlinarith only [hm,hfscaled]
  have hslow := rate_bound (q N γ) (γ*(t N γ:ℝ)) 1 ((10:ℝ)^21)
    (by norm_num) (by positivity) hg (by norm_num [beta])
  have hroot := rate_bound (q N γ) (γ*(t N γ:ℝ)) 1 (4*(10:ℝ)^14)
    (by norm_num) (by positivity) hg (by norm_num [beta])
  refine ⟨Real.exp_le_exp.mpr ?_,Real.exp_le_exp.mpr ?_,Real.exp_le_exp.mpr ?_⟩
  · simpa only [neg_div,neg_mul] using neg_le_neg hfast
  · simpa only [mul_one,neg_div,neg_mul] using neg_le_neg hslow
  · have he : γ*(t N γ:ℝ)/(2*(4*(10:ℝ)^14)*1) = γ*(t N γ:ℝ)/(8*(10:ℝ)^14) := by ring
    rw [he] at hroot
    simpa only [neg_div,neg_mul] using neg_le_neg hroot


structure AdaptiveHostPremises (G : SimpleGraph V) [DecidableRel G.Adj] (γ Λ : ℝ) : Prop where
  order : 3 ≤ Fintype.card V
  connected : G.Connected
  bipartite : G.IsBipartite
  ratio : G.maxDegree ≤ 100*G.minDegree
  gap : HasBipartiteSpectralGap G γ
  momentParameter : 1 ≤ Λ
  moment : ∀ x, (graphTransition G^4) x x ≤ Λ/(G.minDegree:ℝ)^2
  scalar : Parameters.Hstar (Fintype.card V) G.minDegree γ Λ

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem degree_pos (γ Λ : ℝ) (hhost : AdaptiveHostPremises G γ Λ) :
    ∀ x : V, 0 < G.degree x := by
  have hh := Parameters.reductions hhost.scalar
  intro x
  exact lt_of_lt_of_le (by omega : 0<G.minDegree) (G.minDegree_le_degree x)

/-- All graph and probability suppliers are discharged; the returned path is shared by both pairs. -/
theorem exists_adaptive_rich_path_from (γ Λ : ℝ) (hhost : AdaptiveHostPremises G γ Λ)
    (x : V) :
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
  have hred := Parameters.reductions hhost.scalar
  have horderOld : MomentSAParameters.A*(MomentHostParameters.k N γ:ℝ)^2*Real.log (N:ℝ) ≤ (N:ℝ) :=
    Parameters.order_log hhost.scalar
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
  let error : ℝ := (Real.exp (-(t:ℝ)/(2*(10:ℝ)^35*(Parameters.r N:ℝ)))+
    Real.exp (-γ*(t:ℝ)/(2*(10:ℝ)^21)))+Real.exp (-γ*(t:ℝ)/(8*(10:ℝ)^14))
  have hcore : ∀ g y, C.eventMass (((t-1)+g)+(t-1))
      (fun z w => F.windowWeightedCount C (t-1) g (t-1) z w < threshold) y ≤ error := by
    intro g y
    exact Windows.graph_two_window_absorbed G A B hbi d γ Λ hdeg hhost.order hhost.gap
      hhost.momentParameter hmin hmax hhost.moment hred.1 horderOld (Parameters.r N) F g y
      (fun z => Forest.graph_bad_half_absorbed G A B hbi d γ Λ hhost.order hhost.gap
        hhost.momentParameter hmin hmax hhost.moment hhost.scalar F z)
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
    weighted_threshold_ge_three_time N d hhost.order γ hhost.gap.1 hhost.gap.2.1
      hred.2.1 horderOld
  let Eout : V → Path V T → Prop := fun y w => outerCount F C T t ho y w < 3*(T:ℝ)
  let Ein : V → Path V T → Prop := fun y w => innerCount F C T t hi y w < 3*(T:ℝ)
  have hoBad : C.eventMass T Eout x ≤ error :=
    (C.eventMass_mono Eout _ (fun _ _ h => h.trans_le hthreshold) x).trans hout
  have hiBad : C.eventMass T Ein x ≤ error :=
    (C.eventMass_mono Ein _ (fun _ _ h => h.trans_le hthreshold) x).trans hin
  have hrates := three_rates N hhost.order γ hhost.gap.1 hhost.gap.2.1 (Parameters.r N) (Parameters.r_ge_one N)
    (Parameters.r_le_block N γ hhost.order hhost.scalar.log_large hhost.gap.1 hhost.gap.2.1) horderOld
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
    exact graph_weak_self_avoidance_exp G γ (d:ℝ) Λ hhost.order hhost.gap hhost.bipartite
      (by exact_mod_cast (show 0<d by omega)) hhost.momentParameter hminR hmaxR hhost.moment
      hred.2.1 hred.2.2.2.1 hred.2.2.1 x
  have hstrict := MomentRarityParameters.strict_intersection N hhost.order γ hhost.gap.1 hhost.gap.2.1 horderOld
  have hsep := lt_of_le_of_lt hunion (lt_of_lt_of_le hstrict hSA)
  obtain ⟨w,hwSA,hwavoid,hwpos⟩ := C.exists_positive_weight_avoiding actualSA
    (fun y w => Eout y w ∨ Ein y w) x hsep
  refine ⟨A,B,F,ho,hi,w,hwpos,hwSA,?_,?_⟩
  · exact le_of_not_gt (fun h => hwavoid (Or.inl h))
  · exact le_of_not_gt (fun h => hwavoid (Or.inr h))


/-- Hstar on an actual graph supplies a connected simple cycle with at least its order many distinct chords. -/
theorem adaptive_host_has_rich_cycle (γ Λ : ℝ) (hhost : AdaptiveHostPremises G γ Λ) :
    HasRichCycle G := by
  classical
  let N := Fintype.card V
  let T := MomentHostParameters.T N γ
  let t := MomentHostParameters.t N γ
  have hred := Parameters.reductions hhost.scalar
  have hb := MomentHostParameters.block_length_bounds N hhost.order γ hhost.gap.1 hhost.gap.2.1
  have hg := MomentHostParameters.time_bounds N γ (by omega) hred.2.2.1
  let x : V := Classical.choice inferInstance
  obtain ⟨A,B,F,ho,hi,w,hw,hSA,hout,hin⟩ := exists_adaptive_rich_path_from G γ Λ hhost x
  exact rich_cycle_of_actual_window_counts G (degree_pos G γ Λ hhost) F T t hg.2.1 hg.1
    (by have := hg.2.2.1; omega) (outer_time T t ho) (inner_time T t hi) x w hw hSA hout hin

end Erdos642.Adaptive20261018.RichCycle
