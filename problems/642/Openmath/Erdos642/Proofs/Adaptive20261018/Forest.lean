import Openmath.Erdos642.Proofs.Adaptive20261018.ShoreFamily
import Openmath.Erdos642.Proofs.Adaptive20261018.Absorption
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentForestOccupation

/-! Actual fixed-family forest event with a variable spectral cutoff. -/
namespace Erdos642.Adaptive20261018.Forest
open SimpleGraph Matrix Erdos642.FiniteMarkov Erdos642.OccupationTail
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3
open MomentForestOccupation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {A B : Finset V} {q m b : ℕ}
variable (F : ForestBundle G A B q m b)
variable [Nonempty (B:Set V)]

attribute [-instance] FinsetCoe.fintype in
/-- Raw actual ordinary first-stage bound. The only smoothing input is a scalar condition on r;
all graph rank/tail/family/mean/parity and bad-half containment are derived. -/
theorem graph_bad_half_raw (hbi : G.IsBipartiteWith (B:Set V) (A:Set V))
    (hdeg : ∀ x : V, 0 < G.degree x) (γ d Λ : ℝ)
    (hgap : HasBipartiteSpectralGap G γ) (hd : 0 < d) (hΛ : 1 ≤ Λ)
    (hmin : ∀ x : V, d ≤ (G.degree x:ℝ)) (hmax : ∀ x : V, (G.degree x:ℝ) ≤ 100*d)
    (hmoment : ∀ x : V, (graphTransition G^4) x x ≤ Λ/d^2)
    (hq : 1 ≤ q) (hm : 1 ≤ m) (hb : 1 ≤ b)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (r : ℕ) (hr : 1 ≤ r)
    (hrsmall : Real.sqrt (50*Λ*(Fintype.card V:ℝ))/d*θ^(r-1) ≤
      ((((m+1)/2*b:ℕ):ℝ)/(50*(Fintype.card V:ℝ)))/1024)
    (L : ℕ) (hL : 2 ≤ L) :
    ∃ D : ℕ, 1 ≤ D ∧ D ≤ Fintype.card V ∧ (D:ℝ) ≤ Λ*(Fintype.card V:ℝ)/(d^2*θ^2) ∧
      ∀ x : V, (graphChain G hdeg).eventMass (L-1)
        (fun y p => ∃ f : Fin q, (m+1)/2 ≤
          (F.badInForest f ((L:ℝ)*(b:ℝ)/(600*(Fintype.card V:ℝ))) y p).card) x ≤
      ((q:ℝ)*2^m)*(1+((((m+1)/2*b:ℕ):ℝ)/(50*(Fintype.card V:ℝ)))/16)*
        Real.exp (-((((m+1)/2*b:ℕ):ℝ)/(50*(Fintype.card V:ℝ)))^2*(L/2:ℕ)/(256*(r:ℝ))) +
      (CoordinateGrid.alphabet (Fintype.card V) ((((m+1)/2*b:ℕ):ℝ)/(50*(Fintype.card V:ℝ)))^D:ℕ)*
        (⌈2/(((((m+1)/2*b:ℕ):ℝ)/(50*(Fintype.card V:ℝ)))/1024)⌉₊:ℝ)*
        (100*(Fintype.card V:ℝ))*Real.exp
          (-γ*((((m+1)/2*b:ℕ):ℝ)/(50*(Fintype.card V:ℝ)))*(L/2:ℕ)/65536) := by
  classical
  let h := (m+1)/2
  let n := L/2
  let μ : ℝ := ((h*b:ℕ):ℝ)/(50*(Fintype.card V:ℝ))
  have hhh : 1 ≤ h := by dsimp [h]; omega
  have hhm : h ≤ m := by dsimp [h]; omega
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hfit : 2*(n-1)+1 ≤ L-1 := by dsimp [n]; omega
  have hcount : (L:ℝ) ≤ 3*(n:ℝ) := by exact_mod_cast (show L ≤ 3*n by dsimp [n]; omega)
  have hNV : 0 < Fintype.card V := by
    let z : (B:Set V) := Classical.choice inferInstance
    have : Nonempty V := ⟨z.val⟩
    exact Fintype.card_pos
  have hN : 0 < (Fintype.card V:ℝ) := by exact_mod_cast hNV
  have hμ : 0 < μ := by dsimp [μ]; positivity
  obtain ⟨J,_,hJ⟩ := Finset.exists_subset_card_eq
    (show h ≤ (Finset.univ : Finset (Fin m)).card by simpa using hhm)
  let f0 : Fin q := ⟨0,by omega⟩
  have hsize : h*b ≤ Fintype.card V := by
    have hh := (F.leafUnion f0 J).card_le_univ
    simpa only [F.leafUnion_card, hJ] using hh
  have hμ1 : μ ≤ 1 := by
    dsimp [μ]
    apply (div_le_iff₀ (by positivity : 0 < 50*(Fintype.card V:ℝ))).mpr
    have hh : ((h*b:ℕ):ℝ) ≤ (Fintype.card V:ℝ) := by exact_mod_cast hsize
    nlinarith
  have hfunctions : ∀ f ∈ indicatorFamily F h, ∀ y, 0 ≤ f y ∧ f y ≤ 1 := by
    intro f hff y
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hff
    dsimp only
    split_ifs <;> norm_num
  have hmean : ∀ f ∈ indicatorFamily F h, μ ≤ ∑ y, shoreRoot G (B:Set V) y^2*f y := by
    intro f hff
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hff
    have hh := shore_mass_lower G (B:Set V) (A:Set V) hbi hdeg d hd hmin hmax T
    rw [leafFamily_member_card F h T hT] at hh
    simpa only [Erdos642.TiltedOperator.mass, mul_ite, mul_one, mul_zero] using hh
  obtain ⟨D,hD,hDN,hRank,hprob⟩ := ShoreFamily.graph_shore_family_tail G
    (B:Set V) (A:Set V) hbi hdeg γ d Λ hgap hd hΛ hmin hmax hmoment
    θ hθ hθ1 (indicatorFamily F h) hfunctions μ hμ hμ1 hmean r hr hrsmall
  let C0 : ℝ := ((q:ℝ)*2^m)*(1+μ/16)*Real.exp (-μ^2*(n:ℝ)/(256*(r:ℝ))) +
    (CoordinateGrid.alphabet (Fintype.card V) μ^D:ℕ)*(⌈2/(μ/1024)⌉₊:ℝ)*
      (100*(Fintype.card V:ℝ))*Real.exp (-γ*μ*(n:ℝ)/65536)
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hshore : ∀ y : (B:Set V), (shoreChain G (B:Set V) (A:Set V) hbi hdeg).eventMass (n-1)
      (fun z p => ∃ T ∈ leafFamily F h, occupation T z p ≤ μ*(n:ℝ)/4) y ≤ C0 := by
    intro y
    have he : (fun (z : (B:Set V)) (p : Path (B:Set V) (n-1)) => ∃ T ∈ leafFamily F h, occupation T z p ≤ μ*(n:ℝ)/4) =
      (fun (z : (B:Set V)) (p : Path (B:Set V) (n-1)) => ∃ f ∈ indicatorFamily F h, Chain.vertexSum f z p ≤ μ*(n:ℝ)/4) := by
      funext z p
      apply propext
      constructor
      · rintro ⟨T,hT,hp⟩
        exact ⟨(fun v => if v ∈ T then (1:ℝ) else 0), Finset.mem_image.mpr ⟨T,hT,rfl⟩,hp⟩
      · rintro ⟨f,hff,hp⟩
        obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hff
        exact ⟨T,hT,hp⟩
    rw [he]
    apply (hprob n hn y).trans
    dsimp only [C0]
    apply add_le_add ?_ le_rfl
    have hc : ((indicatorFamily F h).card:ℝ) ≤ (q:ℝ)*2^m := by
      exact_mod_cast indicatorFamily_card_le F h
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (Real.exp_nonneg _)
  have ha : (L:ℝ)*((h*b:ℕ):ℝ)/(600*(Fintype.card V:ℝ)) ≤ μ*(n:ℝ)/4 := by
    have hh := mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg (h*b):0≤((h*b:ℕ):ℝ))
    calc
      _ ≤ (3*(n:ℝ))*((h*b:ℕ):ℝ)/(600*(Fintype.card V:ℝ)) :=
        div_le_div_of_nonneg_right hh (by positivity)
      _ = _ := by dsimp [μ]; ring
  refine ⟨D,hD,hDN,hRank,?_⟩
  intro x
  have hc := (graphChain G hdeg).eventMass_mono
    (fun y p => ∃ f : Fin q, h ≤ (F.badInForest f ((L:ℝ)*(b:ℝ)/(600*(Fintype.card V:ℝ))) y p).card)
    (fun y p => ∃ T ∈ leafFamily F h, occupation (ambientShoreSet (B:Set V) T) y p <
      (L:ℝ)*((h*b:ℕ):ℝ)/(600*(Fintype.card V:ℝ)))
    (fun y p hp => bad_half_subset_family F L (by omega) hN hm y p hp) x
  have ht := graph_family_sample_bound G (B:Set V) (A:Set V) hbi hdeg (leafFamily F h)
    (n-1) (L-1) hfit ((L:ℝ)*((h*b:ℕ):ℝ)/(600*(Fintype.card V:ℝ)))
    (μ*(n:ℝ)/4) C0 ha hC0 (by simpa only [Nat.sub_add_cancel hn] using hshore) x
  exact hc.trans ht


section Absorbed
variable [Nonempty V]

set_option maxHeartbeats 800000 in
/-- The actual rounded forest bad-half mass, with no supplied smoothing/rank/net/probability input. -/
theorem graph_bad_half_absorbed (A B : Finset V)
    (hbi : G.IsBipartiteWith (A:Set V) (B:Set V)) (d : ℕ) (γ Λ : ℝ)
    (hN3 : 3 ≤ Fintype.card V) (hgap : HasBipartiteSpectralGap G γ) (hΛ : 1 ≤ Λ)
    (hmin : ∀ x, d ≤ G.degree x)
    (hmax : ∀ x, G.degree x ≤ 100*d)
    (hmoment : ∀ x, (graphTransition G^4) x x ≤ Λ/(d:ℝ)^2)
    (hscalar : Parameters.Hstar (Fintype.card V) d γ Λ)
    (F : ForestBundle G A B (ForestParameters.q d)
      (ForestParameters.m (Fintype.card V) d) (ForestParameters.b d)) (x : V) :
    let t := MomentHostParameters.t (Fintype.card V) γ
    (graphChain G (fun z => by
      have hh := Parameters.reductions hscalar
      exact lt_of_lt_of_le (by omega : 0<d) (hmin z))).eventMass (t-1)
      (fun y p => (∃ f : Fin (ForestParameters.q d),
        (ForestParameters.m (Fintype.card V) d+1)/2 ≤
        (F.badInForest f ((t:ℝ)*(ForestParameters.b d:ℝ)/(600*(Fintype.card V:ℝ))) y p).card)) x ≤
    Real.exp (-(t:ℝ)/(2*(10:ℝ)^35*(Parameters.r (Fintype.card V):ℝ))) +
      Real.exp (-γ*(t:ℝ)/(2*(10:ℝ)^21)) := by
  classical
  let N := Fintype.card V
  let k := MomentHostParameters.k N γ
  let t := MomentHostParameters.t N γ
  let μ := MomentHostParameters.mu N d
  let r := Parameters.r N
  have hred := Parameters.reductions hscalar
  have hdlarge : 100000000 ≤ d := hred.1
  have hdp : 0 < d := by omega
  have hd : 0 < (d:ℝ) := by exact_mod_cast hdp
  let hdeg : ∀ z : V, 0 < G.degree z := fun z => hdp.trans_le (hmin z)
  have hminR : ∀ z, (d:ℝ) ≤ (G.degree z:ℝ) := by intro z; exact_mod_cast hmin z
  have hmaxR : ∀ z, (G.degree z:ℝ) ≤ 100*(d:ℝ) := by intro z; exact_mod_cast hmax z
  have hNd : 2*d ≤ N := MomentHostParameters.bipartite_order_lower G d hdp hbi.isBipartite hmin
  have hμbounds := MomentHostParameters.forest_mean_bounds N d hdlarge hNd
  have hblocks := MomentHostParameters.block_length_bounds N hN3 γ hgap.1 hgap.2.1
  have hgeom := MomentHostParameters.time_bounds N γ (by omega) hred.2.2.1
  have ht : 2 ≤ t := hgeom.2.1
  have htime : MomentSAParameters.a*(N:ℝ)/(32*(k:ℝ)) ≤ (t:ℝ) := hgeom.2.2.2.2.1
  have hell := IntegrationParameters.log_order_gt_one N hN3
  have hr : 1 ≤ r := Parameters.r_ge_one N
  have hθ := Parameters.theta_bounds N hscalar.log_large
  have hrsmall : Real.sqrt (50*Λ*(N:ℝ))/(d:ℝ)*(Parameters.theta N)^(r-1) ≤ μ/1024 := by
    have hh := div_le_div_of_nonneg_right hμbounds.2.2.1 (by norm_num : (0:ℝ)≤1024)
    exact (Parameters.smoothing_tail N hN3 (d:ℝ) Λ hscalar.log_large hd hΛ hred.2.2.2.2).trans hh
  have hqF : 1 ≤ ForestParameters.q d := by have hh := ForestParameters.q_pos d hdlarge; omega
  have hm : 1 ≤ ForestParameters.m N d := (ForestParameters.m_bounds N d hdlarge hNd).1
  have hb : 1 ≤ ForestParameters.b d := by have hh := ForestParameters.ten_le_b d hdlarge; omega
  have hB : Nonempty (B:Set V) := by
    let f : Fin (ForestParameters.q d) := ⟨0,by omega⟩
    let j : Fin (ForestParameters.m N d) := ⟨0,by omega⟩
    have hh : (F.leaves (f,j)).Nonempty := Finset.card_pos.mp (by rw [F.leaves_card]; omega)
    obtain ⟨z,hz⟩ := hh
    exact ⟨⟨z,F.leaves_subset (f,j) hz⟩⟩
  have := hB
  obtain ⟨D,hD,hDN,hRank,hraw⟩ := graph_bad_half_raw G F hbi.symm hdeg γ (d:ℝ) Λ
    hgap hd hΛ hminR hmaxR hmoment hqF hm hb (Parameters.theta N) hθ.1 hθ.2.1 r hr hrsmall t ht
  have hn : (t:ℝ)/3 ≤ (t/2:ℕ) := by
    have hh : t ≤ 3*(t/2) := by omega
    have hc : (t:ℝ) ≤ 3*((t/2:ℕ):ℝ) := by exact_mod_cast hh
    linarith
  have hmu0 : MomentOccupationAbsorption.mu0 ≤ μ := by
    simpa only [MomentOccupationAbsorption.mu0, MomentSmoothingParameters.mu0] using hμbounds.2.2.1
  have hqFN : ForestParameters.q d ≤ N := by
    exact_mod_cast ForestOccupationParameters.q_le_order N d hdlarge hNd
  have hfast := Absorption.fast_family_absorbed N k t (t/2) r
    (ForestParameters.q d) (ForestParameters.m N d) (d:ℝ) μ hN3 hell hblocks.2.1
    hscalar.degree hscalar.order htime hn hr
    (Parameters.r_le_block N γ hN3 hscalar.log_large hgap.1 hgap.2.1) hmu0 hμbounds.2.1 hqFN hμbounds.2.2.2
  have hRank' : (D:ℝ) ≤ Λ*(N:ℝ)*Real.log (N:ℝ)/(d:ℝ)^2 := by
    rw [hθ.2.2] at hRank
    convert hRank using 1 <;> field_simp [ne_of_gt hd, ne_of_gt (lt_trans zero_lt_one hell)] <;> ring
  have hslow := Absorption.slow_family_absorbed N k t (t/2) D
    (d:ℝ) γ Λ μ hN3 hell hblocks.2.1 hd hgap.1 hscalar.moment htime hn
    hmu0 hμbounds.2.1 hD hRank'
  have hlevel : 2/(μ/1024) = 2048/μ := by ring
  have hs : (CoordinateGrid.alphabet N μ^D:ℕ)*(⌈2/(μ/1024)⌉₊:ℝ)*(100*(N:ℝ))*
      Real.exp (-γ*μ*(t/2:ℕ)/65536) ≤ Real.exp (-γ*(t:ℝ)/(2*(10:ℝ)^21)) := by
    rw [hlevel]
    simpa only [Nat.cast_pow,mul_assoc] using hslow
  have hrx := hraw x
  change (graphChain G hdeg).eventMass (t-1)
      (fun y p => ∃ f : Fin (ForestParameters.q d), (ForestParameters.m N d+1)/2 ≤
        (F.badInForest f ((t:ℝ)*(ForestParameters.b d:ℝ)/(600*(N:ℝ))) y p).card) x ≤ _ at hrx
  exact hrx.trans (add_le_add hfast hs)

end Absorbed

end Erdos642.Adaptive20261018.Forest
