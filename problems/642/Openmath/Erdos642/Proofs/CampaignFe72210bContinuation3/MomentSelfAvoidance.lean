import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.FourthBlock
import Openmath.Erdos642.Proofs.CampaignFe72210b.SelfAvoidanceExponential
import Openmath.Erdos642.Proofs.CampaignFe72210b.IntegrationParameters

namespace Erdos642.CampaignFe72210bContinuation3
open Erdos642.CampaignFe72210b
namespace MomentSAParameters
noncomputable def beta : ℝ := 1/(10:ℝ)^100
def A : ℝ := (10:ℝ)^1000
noncomputable def a : ℝ := beta^2/84000
noncomputable def q (N k : ℕ) : ℕ := ⌊a*(N:ℝ)/(k:ℝ)^2⌋₊
theorem beta_pos : 0 < beta := by norm_num [beta]
theorem A_pos : 0 < A := by norm_num [A]
theorem a_pos : 0 < a := by norm_num [a, beta]
theorem constant_bounds : 417/A ≤ beta ∧ 2 ≤ a*A ∧ 42000*a ≤ beta^2 := by
  have hlarge : (10:ℝ)^210 ≤ A :=
    pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 10) (by norm_num : (210:ℕ) ≤ 1000)
  have hb : (417:ℝ) ≤ beta*(10:ℝ)^210 := by norm_num [beta]
  have ha : (2:ℝ) ≤ a*(10:ℝ)^210 := by norm_num [a, beta]
  refine ⟨(div_le_iff₀ A_pos).mpr ?_, ?_, ?_⟩
  · exact hb.trans (mul_le_mul_of_nonneg_left hlarge beta_pos.le)
  · exact ha.trans (mul_le_mul_of_nonneg_left hlarge a_pos.le)
  · norm_num [a, beta]
theorem ratio_ge_two (N k : ℕ) (hk : 2 ≤ k) (hN : A*(k:ℝ)^2 ≤ N) :
    2 ≤ a*(N:ℝ)/(k:ℝ)^2 := by
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hmul := mul_le_mul_of_nonneg_left hN a_pos.le
  have hratio : a*A ≤ a*(N:ℝ)/(k:ℝ)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hk')).mpr
    nlinarith
  exact constant_bounds.2.1.trans hratio

theorem q_bounds (N k : ℕ) (hk : 2 ≤ k) (hN : A*(k:ℝ)^2 ≤ N) :
    1 ≤ q N k ∧ a*(N:ℝ)/(2*(k:ℝ)^2) ≤ (q N k:ℝ) ∧
      (q N k:ℝ) ≤ a*(N:ℝ)/(k:ℝ)^2 := by
  have hr := ratio_ge_two N k hk hN
  have hl := Nat.lt_floor_add_one (a*(N:ℝ)/(k:ℝ)^2)
  have hu := Nat.floor_le (by linarith : (0:ℝ)≤a*(N:ℝ)/(k:ℝ)^2)
  refine ⟨(Nat.one_le_floor_iff _).mpr (by linarith), ?_, hu⟩
  change a*(N:ℝ)/(2*(k:ℝ)^2) ≤ (⌊a*(N:ℝ)/(k:ℝ)^2⌋₊:ℝ)
  have he : a*(N:ℝ)/(2*(k:ℝ)^2) = (a*(N:ℝ)/(k:ℝ)^2)/2 := by ring
  rw [he]
  linarith

theorem local_failure_le_beta (N k : ℕ) (d γ Λ : ℝ) (hk : 2 ≤ k)
    (hd : 0 < d) (hγ : 0 < γ) (_hΛ : 0 ≤ Λ)
    (hN : A*(k:ℝ)^2 ≤ N) (hdegree : A*(k:ℝ) ≤ d)
    (hmoment : A*Λ*(k:ℝ) ≤ d^2*γ) :
    6*(k:ℝ)/d+400*(k:ℝ)^2/(N:ℝ)+11*Λ*(k:ℝ)/(d^2*γ) ≤ beta := by
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hN' : (0:ℝ)<N := lt_of_lt_of_le (mul_pos A_pos (sq_pos_of_pos hk')) hN
  have h1 : 6*(k:ℝ)/d ≤ 6/A := by
    apply (div_le_div_iff₀ hd A_pos).mpr
    nlinarith
  have h2 : 400*(k:ℝ)^2/(N:ℝ) ≤ 400/A := by
    apply (div_le_div_iff₀ hN' A_pos).mpr
    nlinarith
  have h3 : 11*Λ*(k:ℝ)/(d^2*γ) ≤ 11/A := by
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hd) hγ) A_pos).mpr
    nlinarith
  calc
    _ ≤ 6/A+400/A+11/A := add_le_add (add_le_add h1 h2) h3
    _ = 417/A := by ring
    _ ≤ beta := constant_bounds.1

theorem block_order_bound (N k : ℕ) (hk : 2 ≤ k) (hN : A*(k:ℝ)^2 ≤ N) :
    21000*(k:ℝ)*((q N k*k+1:ℕ):ℝ) ≤ beta^2*(N:ℝ) := by
  have hq := q_bounds N k hk hN
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hqscaled : (q N k:ℝ)*(k:ℝ)^2 ≤ a*(N:ℝ) :=
    (le_div_iff₀ (sq_pos_of_pos hk')).mp hq.2.2
  have ht : (1:ℝ) ≤ (q N k:ℝ)*(k:ℝ) := by
    have hnat : 1 ≤ q N k*k := by
      simpa using Nat.mul_le_mul hq.1 (show 1≤k by omega)
    exact_mod_cast hnat
  have hdouble : (q N k:ℝ)*(k:ℝ)+1 ≤ 2*(q N k:ℝ)*(k:ℝ) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hdouble
    (show (0:ℝ)≤21000*(k:ℝ) by positivity)
  have hc := mul_le_mul_of_nonneg_right constant_bounds.2.2 (Nat.cast_nonneg N : (0:ℝ)≤N)
  push_cast
  nlinarith
end MomentSAParameters

open Erdos642.FiniteMarkov.PathCoordinates Erdos642.FiniteMarkov.PathAvoidance
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The reviewed spectral block theorem for the actual graph path event.
All probability, column, and mixing inputs are derived from actual graph proofs. -/
theorem graph_fourth_self_avoidance_exp (hdeg : ∀ x : V, 0 < G.degree x)
    (γ d R Λ : ℝ) (hgap : HasBipartiteSpectralGap G γ) (hbip : G.IsBipartite)
    (hd1 : 1 ≤ d) (hR : 1 ≤ R)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ R * d)
    (hmoment : ∀ z : V, (graphTransition G ^ 4) z z ≤ Λ / d ^ 2)
    (k q : ℕ) (hkfour : 4 ≤ k) (hq : 1 ≤ q)
    (hklog : (2 : ℝ) + Real.log (Fintype.card V : ℝ) / γ ≤ (k : ℝ))
    (β : ℝ) (hβ : 0 < β) (hβupper : β ≤ 1 / 6)
    (hHJ :
      (3 * (k : ℝ) / d + 2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
        Real.sqrt R * Λ * (k : ℝ) / (d ^ 2 * γ)) +
      (3 * (k : ℝ) / d + 2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
        Λ * (k : ℝ) / (d ^ 2 * γ)) ≤ β)
    (horder : (2 * R + Real.sqrt R) * R * (k : ℝ) * ((q * k + 1 : ℕ) : ℝ) ≤
      β ^ 2 * (Fintype.card V : ℝ)) (x : V) :
    Real.exp (-6 * β * (q : ℝ)) ≤ (graphChain G hdeg).eventMass (q * k) actualSA x := by
  have hγ : 0 < γ := hgap.1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have hN : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hN1 : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast (show 1 ≤ Fintype.card V by have := Fintype.card_pos (α := V); omega)
  have hlognonneg : 0 ≤ Real.log (Fintype.card V : ℝ) := Real.log_nonneg hN1
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by
    have := div_nonneg hlognonneg hγ.le
    linarith
  have hk : 2 ≤ k := by exact_mod_cast hkreal
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  let H : ℝ := 3 * (k : ℝ) / d + 2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
    Real.sqrt R * Λ * (k : ℝ) / (d ^ 2 * γ)
  let J : ℝ := 3 * (k : ℝ) / d + 2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
    Λ * (k : ℝ) / (d ^ 2 * γ)
  let M : ℝ := 2 * R + Real.sqrt R
  have hM : 0 ≤ M := add_nonneg (mul_nonneg (by norm_num) hR0) (Real.sqrt_nonneg _)
  have hlocal : ∀ v (S : Finset V), S.card ≤ k →
      (graphChain G hdeg).eventMass k (actualHit S) v ≤ H := by
    intro v S hS
    exact graph_actualHit_fourthBlock_le G hdeg γ d R Λ hgap hbip hd hR hmin hmax hmoment k hkfour S hS v
  have hcollision : ∀ v,
      (graphChain G hdeg).eventMass k (fun z s => ¬ actualSA z s) v ≤ J := by
    intro v
    exact graph_not_actualSA_fourthBlock_le G hdeg γ d R Λ hgap hbip hd hR hmin hmax hmoment k hkfour v
  have hcol : ∀ t ∈ Finset.Icc 1 k, ∀ a,
      ∑ v, ((graphChain G hdeg).transition ^ t) v a ≤ R := by
    intro t _ a
    exact graphTransition_pow_column_sum_le G hdeg d R hd hR hmin hmax t a
  have hmix : ∀ a b, ((graphChain G hdeg).transition ^ k) a b ≤
      M / (Fintype.card V : ℝ) := by
    intro a b
    exact graphTransition_block_mixing G γ d R hgap hbip hd1 hR hmin hmax k hklog a b
  exact (graphChain G hdeg).block_self_avoidance_exp k q β H J M (Fintype.card V : ℝ) R
    (by omega) hq hβ hβupper hN hM hR0 hlocal hcollision hHJ hcol hmix horder x


/-- Full actual graph endpoint: all local probability and exposed-history scalar inputs are derived. -/
theorem graph_moment_self_avoidance_exp (γ d Λ : ℝ)
    (hN3 : 3 ≤ Fintype.card V) (hgap : HasBipartiteSpectralGap G γ)
    (hbip : G.IsBipartite) (hd : 0 < d) (hΛ : 1 ≤ Λ)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100*d)
    (hmoment : ∀ z : V, (graphTransition G ^ 4) z z ≤ Λ / d ^ 2)
    (hdegree : MomentSAParameters.A * (spectralBlockLength (Fintype.card V) γ : ℝ) *
      Real.log (Fintype.card V : ℝ) ≤ d)
    (hmomentScale : MomentSAParameters.A * Λ * (spectralBlockLength (Fintype.card V) γ : ℝ) *
      Real.log (Fintype.card V : ℝ) ≤ d^2*γ)
    (horder : MomentSAParameters.A * (spectralBlockLength (Fintype.card V) γ : ℝ)^2 *
      Real.log (Fintype.card V : ℝ) ≤ (Fintype.card V : ℝ)) (x : V) :
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
  have hdBase : MomentSAParameters.A*(k:ℝ) ≤ d := by
    have hh := mul_le_mul_of_nonneg_left hell.le (mul_nonneg hA.le hk0.le)
    exact (by simpa using hh : MomentSAParameters.A*(k:ℝ) ≤ _).trans hdegree
  have hNBase : MomentSAParameters.A*(k:ℝ)^2 ≤ (N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hell.le (mul_nonneg hA.le (sq_nonneg (k:ℝ)))
    exact (by simpa using hh : MomentSAParameters.A*(k:ℝ)^2 ≤ _).trans horder
  have hMBase : MomentSAParameters.A*Λ*(k:ℝ) ≤ d^2*γ := by
    have hh := mul_le_mul_of_nonneg_left hell.le
      (mul_nonneg (mul_nonneg hA.le (by linarith : 0 ≤ Λ)) hk0.le)
    exact (by simpa using hh : MomentSAParameters.A*Λ*(k:ℝ) ≤ _).trans hmomentScale
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

end Erdos642.CampaignFe72210bContinuation3
