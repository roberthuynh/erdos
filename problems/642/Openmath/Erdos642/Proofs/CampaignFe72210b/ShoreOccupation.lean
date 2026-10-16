import Openmath.Erdos642.Proofs.CampaignFe72210b.ShoreGap
import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralOccupation

/-! Actual shore path occupation tails from the original graph spectral hypotheses. -/
namespace Erdos642.CampaignFe72210b
open SimpleGraph Matrix Erdos642.OccupationTail
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (s : Set V) [DecidablePred (· ∈ s)] [Nonempty s]

 theorem shore_similarity_hermitian (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) :
    ((shoreChain G s t hbi hdeg).similarTransition (shoreRoot G s)).IsHermitian := by
  rw [shore_similarTransition G s t hbi hdeg]
  exact (shore_normalized_posSemidef G s).1

 theorem shore_similarity_positive (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) (f : s → ℝ) :
    0 ≤ dotProduct f (((shoreChain G s t hbi hdeg).similarTransition (shoreRoot G s)) *ᵥ f) := by
  rw [shore_similarTransition G s t hbi hdeg]
  simpa only [star_trivial] using (shore_normalized_posSemidef G s).dotProduct_mulVec_nonneg f

 theorem shore_similarity_fixes_root (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) :
    (shoreChain G s t hbi hdeg).similarTransition (shoreRoot G s) *ᵥ shoreRoot G s =
      shoreRoot G s := by
  funext x
  have he (y : s) :
      ((shoreChain G s t hbi hdeg).similarTransition (shoreRoot G s)) x y * shoreRoot G s y =
        shoreRoot G s x * (shoreChain G s t hbi hdeg).transition x y := by
    unfold Erdos642.FiniteMarkov.Chain.similarTransition
    exact div_mul_cancel₀ _ (ne_of_gt (shoreRoot_pos G s t hbi hdeg y))
  change (∑ y : s, ((shoreChain G s t hbi hdeg).similarTransition (shoreRoot G s)) x y *
    shoreRoot G s y) = shoreRoot G s x
  simp_rw [he]
  rw [← Finset.mul_sum, (shoreChain G s t hbi hdeg).row_sum, mul_one]

/-- Actual occupation bound for a fixed shore-chain start, with n observed vertices. -/
theorem shore_occupation_tail (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) (γ : ℝ)
    (hgap : HasBipartiteSpectralGap G γ) (S : Finset s)
    (n : ℕ) (hn : 1 ≤ n) (x : s) :
    (shoreChain G s t hbi hdeg).eventMass (n - 1)
      (fun x p => occupation S x p ≤ (n : ℝ) * Erdos642.TiltedOperator.mass S (shoreRoot G s) / 2) x ≤
      (2 / shoreRoot G s x ^ 2) *
        Real.exp (-γ * Erdos642.TiltedOperator.mass S (shoreRoot G s) * (n : ℝ) / 64) := by
  exact (shoreChain G s t hbi hdeg).point_mass_occupation_tail
    (shoreRoot G s) (shoreRoot_pos G s t hbi hdeg)
    (shoreRoot_normalized G s t hbi hdeg) γ hgap.1 hgap.2.1
    (shore_similarity_hermitian G s t hbi hdeg)
    (shore_similarity_fixes_root G s t hbi hdeg)
    (shore_similarity_positive G s t hbi hdeg)
    (shore_chain_gap s G t hbi hdeg γ hgap) S n hn x

omit [Nonempty s] in
 theorem shore_mass_degree (S : Finset s) :
    Erdos642.TiltedOperator.mass S (shoreRoot G s) =
      ∑ x : s, if x ∈ S then (G.degree x.val : ℝ) / (G.edgeFinset.card : ℝ) else 0 := by
  simp only [Erdos642.TiltedOperator.mass, shoreRoot_sq]

/-- The same bound with the actual stationary starting mass deg(x)/e(G). -/
theorem shore_occupation_tail_degree (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) (γ : ℝ)
    (hgap : HasBipartiteSpectralGap G γ) (S : Finset s)
    (n : ℕ) (hn : 1 ≤ n) (x : s) :
    (shoreChain G s t hbi hdeg).eventMass (n - 1)
      (fun x p => occupation S x p ≤ (n : ℝ) * Erdos642.TiltedOperator.mass S (shoreRoot G s) / 2) x ≤
      (2 / ((G.degree x.val : ℝ) / (G.edgeFinset.card : ℝ))) *
        Real.exp (-γ * Erdos642.TiltedOperator.mass S (shoreRoot G s) * (n : ℝ) / 64) := by
  simpa only [shoreRoot_sq] using shore_occupation_tail G s t hbi hdeg γ hgap S n hn x

end Erdos642.CampaignFe72210b
