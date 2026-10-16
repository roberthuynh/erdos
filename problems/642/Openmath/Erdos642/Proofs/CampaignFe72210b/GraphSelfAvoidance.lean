import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphBlockMixing
import Openmath.Erdos642.Proofs.CampaignFe72210b.ShortBlockCollisions
import Openmath.Erdos642.Proofs.CampaignFe72210b.SelfAvoidanceExponential

/-! Actual ordinary graph self-avoidance from the original spectral hypotheses. -/

namespace Erdos642.CampaignFe72210b

open Erdos642.FiniteMarkov.PathCoordinates Erdos642.FiniteMarkov.PathAvoidance

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The reviewed spectral block theorem for the actual graph path event.
All probability, column, and mixing inputs are derived from actual graph proofs. -/
theorem graph_self_avoidance_exp (hdeg : ∀ x : V, 0 < G.degree x)
    (γ d R : ℝ) (hgap : HasBipartiteSpectralGap G γ) (hbip : G.IsBipartite)
    (hd1 : 1 ≤ d) (hR : 1 ≤ R)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ R * d)
    (k q : ℕ) (hq : 1 ≤ q)
    (hklog : (2 : ℝ) + Real.log (Fintype.card V : ℝ) / γ ≤ (k : ℝ))
    (β : ℝ) (hβ : 0 < β) (hβupper : β ≤ 1 / 6)
    (hHJ :
      ((k : ℝ) / d + 2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
        Real.sqrt R * (k : ℝ) / (d * γ)) +
      (2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
        Real.sqrt R * (k : ℝ) / (d * γ)) ≤ β)
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
  let H : ℝ := (k : ℝ) / d + 2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
    Real.sqrt R * (k : ℝ) / (d * γ)
  let J : ℝ := 2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
    Real.sqrt R * (k : ℝ) / (d * γ)
  let M : ℝ := 2 * R + Real.sqrt R
  have hM : 0 ≤ M := add_nonneg (mul_nonneg (by norm_num) hR0) (Real.sqrt_nonneg _)
  have hlocal : ∀ v (S : Finset V), S.card ≤ k →
      (graphChain G hdeg).eventMass k (actualHit S) v ≤ H := by
    intro v S hS
    exact graph_actualHit_shortBlock_le G hdeg γ d R hgap hbip hd hR hmin hmax k hk S hS v
  have hcollision : ∀ v,
      (graphChain G hdeg).eventMass k (fun z s => ¬ actualSA z s) v ≤ J := by
    intro v
    exact graph_not_actualSA_shortBlock_le G hdeg γ d R hgap hbip hd hR hmin hmax k hk v
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

end Erdos642.CampaignFe72210b
