import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralParameters

namespace Erdos642.CampaignFe72210b.IntegrationParameters
open SpectralParameters
noncomputable def T (N k : ℕ) : ℕ := q N k*k
noncomputable def t (N k : ℕ) : ℕ := (T N k+1)/8

theorem integration_constants : (10:ℝ)^46  ≤  a*A/2 ∧
    100000000000000000000  ≤  a*A/32 ∧
    3  ≤  a*A/(512*1000000000000000000000000) := by norm_num [a,A,beta]

theorem q_large (N k : ℕ) (hk : 2 ≤ k) (hN : A*(k:ℝ)^2 ≤ N) :
    (10:ℝ)^46  ≤  (q N k:ℝ) := by
  have hq := (q_bounds N k hk hN).2.1
  have hkpos : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hm := mul_le_mul_of_nonneg_left hN a_pos.le
  have hr : a*A/2  ≤  a*(N:ℝ)/(2*(k:ℝ)^2) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2*(k:ℝ)^2)).mpr
    nlinarith
  exact integration_constants.1.trans (hr.trans hq)

theorem time_geometry (N k : ℕ) (hk : 2 ≤ k) (hN : A*(k:ℝ)^2 ≤ N) :
    16 ≤ T N k ∧ 2 ≤ t N k ∧ 8*t N k ≤ T N k+1 ∧
    (T N k:ℝ)/16 ≤ (t N k:ℝ) ∧ a*(N:ℝ)/(32*(k:ℝ)) ≤ (T N k:ℝ)/16 ∧
    3*T N k ≥ 2*(T N k+1) := by
  have hqbig := q_large N k hk hN
  have hq8 : 8 ≤ q N k := by
    have hh : (8:ℝ) ≤ (q N k:ℝ) := by norm_num at hqbig ⊢; linarith
    exact_mod_cast hh
  have hT : 16 ≤ T N k := by
    have hh := Nat.mul_le_mul hq8 hk
    simpa [T] using hh
  have ht2 : 2 ≤ t N k := by unfold t; omega
  have ht8 : 8*t N k ≤ T N k+1 := by unfold t; omega
  have ht16 : T N k ≤ 16*t N k := by unfold t; omega
  have ht16r : (T N k:ℝ) ≤ 16*(t N k:ℝ) := by exact_mod_cast ht16
  have hq := (q_bounds N k hk hN).2.1
  have hkpos : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hqs : a*(N:ℝ) ≤ (q N k:ℝ)*(2*(k:ℝ)^2) :=
    (div_le_iff₀ (by positivity : (0:ℝ)<2*(k:ℝ)^2)).mp hq
  have hTlow : a*(N:ℝ)/(32*(k:ℝ)) ≤ (T N k:ℝ)/16 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<32*(k:ℝ))).mpr
    simp only [T, Nat.cast_mul]
    nlinarith
  exact ⟨hT,ht2,ht8,by linarith,hTlow,by omega⟩

theorem log_order_gt_one (N : ℕ) (hN : 3 ≤ N) : 1<Real.log (N:ℝ) := by
  have h3 : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<3) h3
  have h := Real.log_three_gt_d9
  linarith

theorem occupation_requirements (N d k : ℕ) (γ : ℝ) (hN3 : 3 ≤ N) (hk : 2 ≤ k)
    (hγ : 0<γ) (hγ1 : γ ≤ 1) (hgk : Real.log (N:ℝ) ≤ γ*(k:ℝ))
    (hd : A*(k:ℝ)/γ ≤ d) (hN : A*(k:ℝ)^2 ≤ N) :
    100000000 ≤ d ∧ 1000000000000000000 ≤ (d:ℝ)*γ*(t N k:ℝ)/(N:ℝ) ∧
      100000000000000000000*Real.log (N:ℝ) ≤ γ*(t N k:ℝ) := by
  have hkpos : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hdg : A*(k:ℝ) ≤ (d:ℝ)*γ := (div_le_iff₀ hγ).mp hd
  have hdc : (d:ℝ)*γ ≤ d := mul_le_of_le_one_right (Nat.cast_nonneg d) hγ1
  have hAk := mul_le_mul_of_nonneg_left hk2 A_pos.le
  have hAbig : (100000000:ℝ) ≤ 2*A := by norm_num [A]
  have hdlarge : (100000000:ℝ) ≤ d := by nlinarith
  have hgeom := time_geometry N k hk hN
  have htlow : a*(N:ℝ)/(32*(k:ℝ)) ≤ (t N k:ℝ) := hgeom.2.2.2.2.1.trans hgeom.2.2.2.1
  have hts : a*(N:ℝ) ≤ (t N k:ℝ)*(32*(k:ℝ)) :=
    (div_le_iff₀ (by positivity : (0:ℝ)<32*(k:ℝ))).mp htlow
  have hta := mul_le_mul_of_nonneg_left hts A_pos.le
  have hdt := mul_le_mul_of_nonneg_right hdg (Nat.cast_nonneg (t N k) : (0:ℝ) ≤ t N k)
  have hconst := integration_constants.2.1
  have hcN := mul_le_mul_of_nonneg_right hconst (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  have hdegreeTime : (1000000000000000000:ℝ) ≤ (d:ℝ)*γ*(t N k:ℝ)/(N:ℝ) := by
    apply (le_div_iff₀ hNp).mpr
    nlinarith
  have haN := mul_le_mul_of_nonneg_left hN a_pos.le
  have htAk : a*A*(k:ℝ)/32 ≤ (t N k:ℝ) := by
    apply (mul_le_mul_iff_right₀ hkpos).mp
    nlinarith
  have hgam := mul_le_mul_of_nonneg_left htAk hγ.le
  have hlognonneg := (log_order_gt_one N hN3).le
  have hcLog := mul_le_mul_of_nonneg_right hconst (show 0 ≤ Real.log (N:ℝ) by linarith)
  have hgk' := mul_le_mul_of_nonneg_left hgk (show 0 ≤ a*A/32 by linarith [integration_constants.2.1])
  refine ⟨by exact_mod_cast hdlarge,hdegreeTime,?_⟩
  nlinarith

theorem edge_threshold (N d k : ℕ) (γ : ℝ) (hN3 : 3 ≤ N) (hk : 2 ≤ k)
    (hγ : 0<γ) (hγ1 : γ ≤ 1) (hd : A*(k:ℝ)/γ ≤ d) (hN : A*(k:ℝ)^2 ≤ N) :
    3*(T N k:ℝ) ≤ (d:ℝ)*(t N k:ℝ)^2/(1000000000000000000000000*(N:ℝ)) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hkpos : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hdg : A*(k:ℝ) ≤ (d:ℝ)*γ := (div_le_iff₀ hγ).mp hd
  have hdc : (d:ℝ)*γ ≤ d := mul_le_of_le_one_right (Nat.cast_nonneg d) hγ1
  have hAd : A*(k:ℝ) ≤ d := hdg.trans hdc
  have hg := time_geometry N k hk hN
  have htT := hg.2.2.2.1
  have htN : a*(N:ℝ)/(32*(k:ℝ)) ≤ (t N k:ℝ) := hg.2.2.2.2.1.trans htT
  have hts : a*(N:ℝ) ≤ (t N k:ℝ)*(32*(k:ℝ)) :=
    (div_le_iff₀ (by positivity : (0:ℝ)<32*(k:ℝ))).mp htN
  have hTscaled : (T N k:ℝ) ≤ 16*(t N k:ℝ) := by linarith
  have hprod := mul_le_mul hTscaled hts (mul_nonneg a_pos.le (Nat.cast_nonneg N))
    (show (0:ℝ) ≤ 16*(t N k:ℝ) by positivity)
  have hprodA := mul_le_mul_of_nonneg_left hprod A_pos.le
  have hdegree := mul_le_mul_of_nonneg_right hAd (sq_nonneg (t N k:ℝ))
  have hc := integration_constants.2.2
  have hcNT := mul_le_mul_of_nonneg_right hc
    (show (0:ℝ) ≤ (N:ℝ)*(T N k:ℝ) by positivity)
  apply (le_div_iff₀ (by positivity : (0:ℝ)<1000000000000000000000000*(N:ℝ))).mpr
  nlinarith

theorem absorb_prefactor (N : ℕ) (s : ℝ) (hN : 3 ≤ N)
    (hs : 100000000000000000000*Real.log (N:ℝ) ≤ s) :
    400*(N:ℝ)^2*Real.exp (-s/100000000000000000)  ≤ 
      Real.exp (-s/200000000000000000) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlog := log_order_gt_one N hN
  have h400 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<400)
  have he : Real.log 400+2*Real.log (N:ℝ)-s/100000000000000000  ≤ 
      -s/200000000000000000 := by linarith
  calc
    _ = Real.exp (Real.log 400)*Real.exp ((2:ℝ)*Real.log (N:ℝ))*
        Real.exp (-s/100000000000000000) := by
      rw [Real.exp_log (by norm_num : (0:ℝ)<400),
        show Real.exp ((2:ℝ)*Real.log (N:ℝ))=(N:ℝ)^2 by
          rw [show (2:ℝ)=(2:ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hNp]]
    _ = Real.exp (Real.log 400+2*Real.log (N:ℝ)-s/100000000000000000) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _  ≤  _ := Real.exp_le_exp.mpr he

theorem strict_event_intersection (N k : ℕ) (γ : ℝ) (hN3 : 3 ≤ N) (hk : 2 ≤ k)
    (hγ : 0<γ) (hgk : Real.log (N:ℝ) ≤ γ*(k:ℝ)) (hN : A*(k:ℝ)^2 ≤ N) :
    2*Real.exp (-γ*(t N k:ℝ)/200000000000000000) <
      Real.exp (-6*beta*(q N k:ℝ)) := by
  have hlog := log_order_gt_one N hN3
  have hgamk : (1:ℝ) ≤ γ*(k:ℝ) := by linarith
  have htT := (time_geometry N k hk hN).2.2.2.1
  have hmul := mul_le_mul_of_nonneg_left htT hγ.le
  have hqgam := mul_le_mul_of_nonneg_left hgamk
    (Nat.cast_nonneg (q N k) : (0:ℝ) ≤ q N k)
  have htime : (q N k:ℝ)/16 ≤ γ*(t N k:ℝ) := by
    simp only [T, Nat.cast_mul] at hmul
    nlinarith
  have hqbig := q_large N k hk hN
  have hgap : 1<(q N k:ℝ)/3200000000000000000-6*beta*(q N k:ℝ) := by
    have hqreal : (100000000000000000000:ℝ) ≤ (q N k:ℝ) :=
      (by norm_num : (100000000000000000000:ℝ) ≤ (10:ℝ)^46).trans hqbig
    norm_num [beta]
    nlinarith
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hexp : Real.log 2-γ*(t N k:ℝ)/200000000000000000 <
      -6*beta*(q N k:ℝ) := by linarith
  calc
    _ = Real.exp (Real.log 2-γ*(t N k:ℝ)/200000000000000000) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<2)]
      congr 2
      ring
    _ < _ := Real.exp_lt_exp.mpr hexp
end Erdos642.CampaignFe72210b.IntegrationParameters
