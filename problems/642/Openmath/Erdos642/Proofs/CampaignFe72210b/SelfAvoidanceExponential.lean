import Openmath.Erdos642.Proofs.CampaignFe72210b.BlockSelfAvoidance

namespace Erdos642.FiniteMarkov
open PathCoordinates PathAvoidance

/-- The scalar logarithmic estimate used by block self-avoidance. -/
theorem log_one_sub_three_beta (β : ℝ) (hβ : 0 < β) (hupper : β ≤ 1/6) :
    -6*β ≤ Real.log (1-3*β) := by
  have hp : 0 < 1-3*β := by linarith
  have hinv : (1-3*β)⁻¹ ≤ 1+6*β := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).mpr
    have hprod := mul_nonneg hβ.le (show 0 ≤ 1-6*β by linarith)
    nlinarith
  have hl := Real.one_sub_inv_le_log_of_pos hp
  linarith

/-- Scalar product-to-exponential comparison, including q=0. -/
theorem exp_neg_six_beta_mul_le_pow (β : ℝ) (hβ : 0 < β)
    (hupper : β ≤ 1/6) (q : ℕ) :
    Real.exp (-6*β*(q:ℝ)) ≤ (1-3*β)^q := by
  have hp : 0 < 1-3*β := by linarith
  have hl := log_one_sub_three_beta β hβ hupper
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg q : 0 ≤ (q:ℝ))
  calc
    Real.exp (-6*β*(q:ℝ)) ≤ Real.exp ((q:ℝ)*Real.log (1-3*β)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = (1-3*β)^q := by rw [Real.exp_nat_mul, Real.exp_log hp]

namespace Chain
variable {V : Type*} [Fintype V] [DecidableEq V] (C : Chain V)

/-- Actual ordinary-chain exponential self-avoidance from the same local inputs. -/
theorem block_self_avoidance_exp (k q : ℕ) (β H J M N R : ℝ)
    (hk : 1 ≤ k) (hq : 1 ≤ q) (hβ : 0 < β) (hβupper : β ≤ 1/6)
    (hN : 0 < N) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hlocal : ∀ v (S : Finset V), S.card ≤ k → C.eventMass k (actualHit S) v ≤ H)
    (hcollision : ∀ v, C.eventMass k (fun z s => ¬ actualSA z s) v ≤ J)
    (hHJ : H+J ≤ β)
    (hcol : ∀ t ∈ Finset.Icc 1 k, ∀ a, ∑ v, (C.transition^t) v a ≤ R)
    (hmix : ∀ x y, (C.transition^k) x y ≤ M/N)
    (horder : M*R*(k:ℝ)*((q*k+1:ℕ):ℝ) ≤ β^2*N) (x : V) :
    Real.exp (-6*β*(q:ℝ)) ≤ C.eventMass (q*k) actualSA x := by
  exact (exp_neg_six_beta_mul_le_pow β hβ hβupper q).trans
    (C.block_self_avoidance k q β H J M N R hk hq hβ hβupper hN hM hR
      hlocal hcollision hHJ hcol hmix horder x)
end Chain
end Erdos642.FiniteMarkov
