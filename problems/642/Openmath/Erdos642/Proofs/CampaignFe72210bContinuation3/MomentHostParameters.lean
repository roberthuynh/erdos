import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentSmoothingParameters
import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestOccupationParameters

/-! Strong moment-host core rounding and actual forest mean parameters. -/
namespace Erdos642.CampaignFe72210bContinuation3.MomentHostParameters
open Erdos642.CampaignFe72210b
open MomentSAParameters

noncomputable def k (N : ℕ) (γ : ℝ) : ℕ := spectralBlockLength N γ
noncomputable def q (N : ℕ) (γ : ℝ) : ℕ := MomentSAParameters.q N (k N γ)
noncomputable def T (N : ℕ) (γ : ℝ) : ℕ := q N γ * k N γ
noncomputable def t (N : ℕ) (γ : ℝ) : ℕ := (T N γ + 1) / 8
noncomputable def mu (N d : ℕ) : ℝ :=
  ((ForestOccupationParameters.h N d * ForestParameters.b d : ℕ) : ℝ) / (50 * (N : ℝ))

theorem large_constants : (10 : ℝ)^8 ≤ A ∧ 64 ≤ a*A ∧ 2 ≤ beta*a*A := by
  have hl : (10 : ℝ)^310 ≤ A :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) (by norm_num : (310 : ℕ) ≤ 1000)
  refine ⟨?_, ?_, ?_⟩
  · exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) (by norm_num : (8 : ℕ) ≤ 310)).trans hl
  · exact (show (64 : ℝ) ≤ a*(10 : ℝ)^310 by
        rw [show (310 : ℕ) = 210+100 by norm_num, pow_add]
        norm_num [a,beta]).trans
      (mul_le_mul_of_nonneg_left hl a_pos.le)
  · exact (show (2 : ℝ) ≤ beta*a*(10 : ℝ)^310 by
        rw [show (310 : ℕ) = 210+100 by norm_num, pow_add]
        norm_num [a,beta]).trans
      (mul_le_mul_of_nonneg_left hl (mul_nonneg beta_pos.le a_pos.le))

theorem block_length_bounds (N : ℕ) (hN : 3 ≤ N) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    4 ≤ k N γ ∧ Real.log (N : ℝ) ≤ (k N γ : ℝ) ∧
    Real.log (N : ℝ) ≤ γ*(k N γ : ℝ) ∧
    2 + Real.log (N : ℝ)/γ ≤ (k N γ : ℝ) := by
  have hell := IntegrationParameters.log_order_gt_one N hN
  have hc : 2 + Real.log (N : ℝ)/γ ≤ (k N γ : ℝ) := Nat.le_ceil _
  have hdiv : Real.log (N : ℝ) ≤ Real.log (N : ℝ)/γ := by
    apply (le_div_iff₀ hγ).mpr
    nlinarith
  have hkreal : (3 : ℝ) < (k N γ : ℝ) := by linarith
  have hk : 4 ≤ k N γ := by
    have hh : 3 < k N γ := by exact_mod_cast hkreal
    omega
  have hmul := mul_le_mul_of_nonneg_left hc hγ.le
  have he : γ*(2+Real.log (N : ℝ)/γ) = 2*γ+Real.log (N : ℝ) := by field_simp
  rw [he] at hmul
  exact ⟨hk, by linarith, by linarith, hc⟩

theorem strong_reductions (N d : ℕ) (hN : 3 ≤ N) (γ Λ : ℝ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hΛ : 1 ≤ Λ)
    (hdegree : A*(k N γ : ℝ)*Real.log (N : ℝ) ≤ d)
    (horder : A*(k N γ : ℝ)^2*Real.log (N : ℝ) ≤ N)
    (hmoment : A*Λ*(k N γ : ℝ)*Real.log (N : ℝ) ≤ (d : ℝ)^2*γ) :
    100000000 ≤ d ∧ A*(k N γ : ℝ) ≤ d ∧ A*(k N γ : ℝ)^2 ≤ N ∧
    A*Λ*(k N γ : ℝ) ≤ (d : ℝ)^2*γ ∧ Λ ≤ (d : ℝ)^2 := by
  have hell := IntegrationParameters.log_order_gt_one N hN
  have hk := (block_length_bounds N hN γ hγ hγ1).1
  have hk' : (4 : ℝ) ≤ (k N γ : ℝ) := by exact_mod_cast hk
  have hA := A_pos
  have hΛ0 : 0 ≤ Λ := by linarith
  have hdweak : A*(k N γ : ℝ) ≤ d := by
    have hh := mul_le_mul_of_nonneg_left hell.le (show 0 ≤ A*(k N γ : ℝ) by positivity)
    nlinarith only [hh,hdegree]
  have hNweak : A*(k N γ : ℝ)^2 ≤ N := by
    have hh := mul_le_mul_of_nonneg_left hell.le (show 0 ≤ A*(k N γ : ℝ)^2 by positivity)
    nlinarith only [hh,horder]
  have hMweak : A*Λ*(k N γ : ℝ) ≤ (d : ℝ)^2*γ := by
    have hh := mul_le_mul_of_nonneg_left hell.le (show 0 ≤ A*Λ*(k N γ : ℝ) by positivity)
    nlinarith only [hh,hmoment]
  have hd : (100000000 : ℝ) ≤ d := by
    have hh := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (k N γ : ℝ) by linarith) hA.le
    nlinarith [large_constants.1]
  have hcoeff : (1 : ℝ) ≤ A*(k N γ : ℝ) := by
    have hA1 : (1 : ℝ) ≤ A := by nlinarith [large_constants.1]
    have hh := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (k N γ : ℝ) by linarith) hA.le
    linarith
  have hΛlower := mul_le_mul_of_nonneg_right hcoeff hΛ0
  have hγupper := mul_le_mul_of_nonneg_left hγ1 (sq_nonneg (d : ℝ))
  refine ⟨by exact_mod_cast hd, hdweak, hNweak, hMweak, ?_⟩
  nlinarith only [hΛlower,hMweak,hγupper]

theorem q_large (N : ℕ) (γ : ℝ) (hk : 2 ≤ k N γ)
    (horder : A*(k N γ : ℝ)^2 ≤ N) :
    32 ≤ q N γ ∧ 1 ≤ beta*(q N γ : ℝ) ∧
    a*(N : ℝ)/(2*(k N γ : ℝ)^2) ≤ (q N γ : ℝ) ∧
    (q N γ : ℝ) ≤ a*(N : ℝ)/(k N γ : ℝ)^2 := by
  have hq := MomentSAParameters.q_bounds N (k N γ) hk horder
  have hkpos : 0 < (k N γ : ℝ) := by exact_mod_cast (show 0 < k N γ by omega)
  have hh : a*A/2 ≤ a*(N : ℝ)/(2*(k N γ : ℝ)^2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*(k N γ : ℝ)^2)).mpr
    have hm := mul_le_mul_of_nonneg_left horder a_pos.le
    nlinarith only [hm]
  have hbase : a*A/2 ≤ (q N γ : ℝ) := hh.trans hq.2.1
  have h32 : (32 : ℝ) ≤ (q N γ : ℝ) := by linarith [large_constants.2.1]
  have hβ := mul_le_mul_of_nonneg_left hbase beta_pos.le
  refine ⟨by exact_mod_cast h32, ?_, hq.2.1, hq.2.2⟩
  nlinarith only [hβ,large_constants.2.2]

theorem time_bounds (N : ℕ) (γ : ℝ) (hk : 2 ≤ k N γ)
    (horder : A*(k N γ : ℝ)^2 ≤ N) :
    16 ≤ T N γ ∧ 2 ≤ t N γ ∧ 8*t N γ ≤ T N γ+1 ∧
    (T N γ : ℝ)/16 ≤ (t N γ : ℝ) ∧
    a*(N : ℝ)/(32*(k N γ : ℝ)) ≤ (t N γ : ℝ) ∧
    2*(T N γ+1) ≤ 3*T N γ := by
  have hq := q_large N γ hk horder
  have hT : 16 ≤ T N γ := by dsimp [T]; nlinarith [hq.1]
  have ht : 2 ≤ t N γ := by dsimp [t]; omega
  have hfit : 8*t N γ ≤ T N γ+1 := by dsimp [t]; omega
  have hhalf : T N γ ≤ 16*t N γ := by dsimp [t]; omega
  have hhalf' : (T N γ : ℝ) ≤ 16*(t N γ : ℝ) := by exact_mod_cast hhalf
  have hkpos : 0 < (k N γ : ℝ) := by exact_mod_cast (show 0 < k N γ by omega)
  have hmul := mul_le_mul_of_nonneg_right hq.2.2.1 hkpos.le
  have hTl : a*(N : ℝ)/(2*(k N γ : ℝ)) ≤ (T N γ : ℝ) := by
    dsimp [T]
    push_cast
    have heq : (a*(N : ℝ)/(2*(k N γ : ℝ)^2))*(k N γ : ℝ) =
        a*(N : ℝ)/(2*(k N γ : ℝ)) := by field_simp [ne_of_gt hkpos]
    rw [heq] at hmul
    exact hmul
  refine ⟨hT,ht,hfit,by linarith,?_,by omega⟩
  have he : a*(N : ℝ)/(32*(k N γ : ℝ)) = (a*(N : ℝ)/(2*(k N γ : ℝ)))/16 := by ring
  rw [he]
  linarith only [hTl,hhalf']

theorem forest_mean_bounds (N d : ℕ) (hd : 100000000 ≤ d) (hNd : 2*d ≤ N) :
    5/(10 : ℝ)^15 ≤ mu N d ∧ mu N d ≤ 1/50 ∧
    MomentSmoothingParameters.mu0 ≤ mu N d ∧
    (ForestParameters.m N d : ℝ) ≤ (N : ℝ)/(d : ℝ) := by
  have hdp : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hs := ForestOccupationParameters.support_bounds N d hd hNd
  have hm := ForestParameters.m_le_order_div_degree N d hd hNd
  have hm1 := (ForestParameters.m_bounds N d hd hNd).1
  have hb := (ForestParameters.b_bounds d hd).2
  have hh : ForestOccupationParameters.h N d ≤ ForestParameters.m N d := by
    dsimp [ForestOccupationParameters.h]; omega
  have hh' : (ForestOccupationParameters.h N d : ℝ) ≤ (ForestParameters.m N d : ℝ) := by exact_mod_cast hh
  have hb' : (ForestParameters.b d : ℝ) ≤ (d : ℝ) := by linarith
  have hupper : (ForestOccupationParameters.h N d : ℝ)*(ForestParameters.b d : ℝ) ≤ N := by
    have h1 := mul_le_mul hh' hb' (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h2 := (le_div_iff₀ hdp).mp hm
    exact h1.trans h2
  have hlo : 5/(10 : ℝ)^15 ≤ mu N d := by
    unfold mu
    push_cast
    apply (le_div_iff₀ (by positivity : 0 < 50*(N : ℝ))).mpr
    nlinarith only [hs.2]
  have hup : mu N d ≤ 1/50 := by
    unfold mu
    push_cast
    apply (div_le_iff₀ (by positivity : 0 < 50*(N : ℝ))).mpr
    nlinarith only [hupper]
  refine ⟨hlo,hup,?_,hm⟩
  exact (show MomentSmoothingParameters.mu0 ≤ 5/(10 : ℝ)^15 by norm_num [MomentSmoothingParameters.mu0]).trans hlo

section Graph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Nonempty V] in
private theorem shore_order_lower (d : ℕ) (hmin : ∀ x, d ≤ G.degree x)
    (s t : Set V) (hbi : G.IsBipartiteWith s t) (x y : V) (hx : x ∈ s) (hy : y ∈ t) :
    2*d ≤ Fintype.card V := by
  classical
  have hleft : d ≤ s.toFinset.card := by
    apply (hmin y).trans
    rw [← G.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro z hz
    exact Set.mem_toFinset.mpr (hbi.mem_of_mem_adj' hy ((G.mem_neighborFinset y z).mp hz).symm)
  have hright : d ≤ t.toFinset.card := by
    apply (hmin x).trans
    rw [← G.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro z hz
    exact Set.mem_toFinset.mpr (hbi.mem_of_mem_adj hx ((G.mem_neighborFinset x z).mp hz))
  have hd : Disjoint s.toFinset t.toFinset := by
    rw [← Finset.disjoint_coe]
    simpa using hbi.disjoint
  have hcard : s.toFinset.card+t.toFinset.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hd]
    exact Finset.card_le_univ _
  omega

/-- Actual bipartiteness and minimum degree pay the forest order premise. -/
theorem bipartite_order_lower (d : ℕ) (hd : 0 < d) (hbip : G.IsBipartite)
    (hmin : ∀ x, d ≤ G.degree x) : 2*d ≤ Fintype.card V := by
  classical
  let x : V := Classical.choice inferInstance
  have hxdeg : 0 < G.degree x := hd.trans_le (hmin x)
  have hn : (G.neighborFinset x).Nonempty := by
    rw [← Finset.card_pos, G.card_neighborFinset_eq_degree]
    exact hxdeg
  obtain ⟨y,hy⟩ := hn
  have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy
  obtain ⟨s,t,hbi⟩ := SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mp hbip
  rcases hbi.mem_of_adj hxy with h|h
  · exact shore_order_lower G d hmin s t hbi x y h.1 h.2
  · exact shore_order_lower G d hmin t s hbi.symm x y h.1 h.2
end Graph
end Erdos642.CampaignFe72210bContinuation3.MomentHostParameters
