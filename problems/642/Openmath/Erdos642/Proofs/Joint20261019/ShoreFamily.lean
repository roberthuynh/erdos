import Openmath.Erdos642.Proofs.Joint20261019.JointFamily
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.GraphSmoothingOccupation

namespace Erdos642.Joint20261019.ShoreFamily
open Matrix Erdos642.FiniteMarkov Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3 MomentSmoothing
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (s : Set V) [DecidablePred (· ∈ s)] [Nonempty s]

/-- The actual shore law, with fixed cutoff rank and dimension-only entropy. -/
theorem graph_shore_family_tail (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x)
    (γ d Λ : ℝ) (hgap : HasBipartiteSpectralGap G γ) (hd : 0 < d) (hΛ : 1 ≤ Λ)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100*d)
    (hmoment : ∀ x : V, (graphTransition G ^ 4) x x ≤ Λ / d^2)
    (F : Finset (s → ℝ)) (hf : ∀ f ∈ F, ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hmean : ∀ f ∈ F, μ ≤ ∑ x : s, shoreRoot G s x^2*f x) :
    ∃ D : ℕ, 1 ≤ D ∧ D ≤ Fintype.card V ∧
      (D:ℝ) ≤ 16*Λ*(Fintype.card V:ℝ)/d^2 ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ x : s,
      (shoreChain G s t hbi hdeg).eventMass (n-1)
        (fun y p => ∃ f ∈ F, Chain.vertexSum f y p ≤ μ*(n:ℝ)/4) x ≤
      (F.card:ℝ)*(50*(Fintype.card V:ℝ))*Real.exp (-μ^2*(n:ℝ)/4096) +
      (65/μ)^D*(50*(Fintype.card V:ℝ))*Real.exp (-γ*μ^2*(n:ℝ)/32) := by
  classical
  let C := shoreChain G s t hbi hdeg
  let u := shoreRoot G s
  let A := C.similarTransition u
  have hA : A.IsHermitian := shore_similarity_hermitian G s t hbi hdeg
  have huPos : ∀ x : s, 0 < u x := shoreRoot_pos G s t hbi hdeg
  have hu : (∑ x : s, u x^2) = 1 := shoreRoot_normalized G s t hbi hdeg
  have hdiag : ∀ x : s, (A^2) x x ≤ Λ/d^2 := by
    intro x
    rw [show (A^2) x x = (graphTransition G^4) x.val x.val from
      MomentSmoothing.shore_similarity_square_diagonal G s t hbi hdeg x]
    exact hmoment x.val
  let E := slowSpace A hA
  let D := Module.finrank ℝ E
  have hroot : WithLp.toLp 2 u ∈ E :=
    MomentSmoothingMean.stationary_root_mem_slowSpace C u huPos hA
  have hDpos : 1 ≤ D := by
    have hfin : 0 < Module.finrank ℝ E := Module.finrank_pos_iff_exists_ne_zero.mpr (by
      refine ⟨⟨WithLp.toLp 2 u,hroot⟩, ?_⟩
      intro hz
      have he := congrArg (fun z : E => (z : EuclideanSpace ℝ s)) hz
      let x : s := Classical.choice inferInstance
      have hx := congrArg (fun z : EuclideanSpace ℝ s => z x) he
      have hn : u x = 0 := hx
      exact (ne_of_gt (huPos x)) hn)
    exact hfin
  have hs : Fintype.card s ≤ Fintype.card V := Fintype.card_subtype_le _
  have hDN : D ≤ Fintype.card V := (slowSpace_finrank_le A hA).trans hs
  have hRank : (D:ℝ) ≤ 16*Λ*(Fintype.card V:ℝ)/d^2 := by
    apply (slow_rank_diagonal_bound A hA d Λ hdiag).trans
    have hm := mul_le_mul_of_nonneg_left
      (show (Fintype.card s:ℝ) ≤ (Fintype.card V:ℝ) by exact_mod_cast hs)
      (show 0 ≤ 16*Λ/d^2 by positivity)
    convert hm using 1 <;> ring
  refine ⟨D,hDpos,hDN,hRank,?_⟩
  intro n hn x
  have ht := JointFamily.fixed_family_tail C u huPos hu hA
    (shore_similarity_positive G s t hbi hdeg) γ hgap.1.le
    (shore_chain_gap s G t hbi hdeg γ hgap) F hf μ hμ hμ1 hmean n hn x
  have hat : 1/(u x)^2 ≤ 50*(Fintype.card V:ℝ) := by
    have hh := shoreRoot_prefactor_upper G s t hbi hdeg d hd hmin hmax x
    dsimp [u]
    simp only [div_eq_mul_inv,one_mul] at hh ⊢
    linarith
  apply ht.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hat (Nat.cast_nonneg _)) (Real.exp_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hat (by positivity)) (Real.exp_nonneg _)

end Erdos642.Joint20261019.ShoreFamily
