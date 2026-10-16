import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.UniformSmoothingOccupation
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MomentSmoothingMean

/-! Actual graph moment and gap supply the canonical shore smoothing occupation law. -/
namespace Erdos642.CampaignFe72210bContinuation3.GraphSmoothingOccupation
open Matrix Erdos642.FiniteMarkov Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3
open MomentSmoothing
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (s : Set V) [DecidablePred (· ∈ s)] [Nonempty s]

/-- Actual canonical rank, root, spectral tail and finite-family probability all derive from
original graph premises. Only the scalar smoothing-time choice remains explicit. -/
theorem graph_shore_family_tail (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x)
    (γ d Λ : ℝ) (hgap : HasBipartiteSpectralGap G γ) (hd : 0 < d) (hΛ : 1 ≤ Λ)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100*d)
    (hmoment : ∀ x : V, (graphTransition G ^ 4) x x ≤ Λ / d^2)
    (F : Finset (s → ℝ)) (hf : ∀ f ∈ F, ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hmean : ∀ f ∈ F, μ ≤ ∑ x : s, shoreRoot G s x^2*f x)
    (r : ℕ) (hr : 1 ≤ r)
    (hrsmall : Real.sqrt (50*Λ*(Fintype.card V:ℝ))/d*(1/4:ℝ)^(r-1) ≤ μ/1024) :
    ∃ D : ℕ, 1 ≤ D ∧ D ≤ Fintype.card V ∧
      (D:ℝ) ≤ 16*Λ*(Fintype.card V:ℝ)/d^2 ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ x : s,
      (shoreChain G s t hbi hdeg).eventMass (n-1)
        (fun y p => ∃ f ∈ F, Chain.vertexSum f y p ≤ μ*(n:ℝ)/4) x ≤
      (F.card:ℝ)*(1+μ/16)*Real.exp (-μ^2*(n:ℝ)/(256*(r:ℝ))) +
      (CoordinateGrid.alphabet (Fintype.card V) μ ^ D : ℕ)*(⌈2/(μ/1024)⌉₊:ℝ)*
        (100*(Fintype.card V:ℝ))*Real.exp (-γ*μ*(n:ℝ)/65536) := by
  classical
  let C := shoreChain G s t hbi hdeg
  let u := shoreRoot G s
  let A := C.similarTransition u
  have hA : A.IsHermitian := shore_similarity_hermitian G s t hbi hdeg
  have huPos : ∀ x : s, 0 < u x := shoreRoot_pos G s t hbi hdeg
  have hu : (∑ x : s, u x^2) = 1 := shoreRoot_normalized G s t hbi hdeg
  have hstat : ∀ y : s, ∑ x : s, u x^2*C.transition x y = u y^2 :=
    C.similarTransition_stationary u huPos hA
  have hp : A.PosSemidef := by
    dsimp [A,C,u]
    rw [shore_similarTransition G s t hbi hdeg]
    exact shore_normalized_posSemidef G s
  have hdiag : ∀ x : s, (A^2) x x ≤ Λ/d^2 := by
    intro x
    rw [show (A^2) x x = (graphTransition G^4) x.val x.val from
      shore_similarity_square_diagonal G s t hbi hdeg x]
    exact hmoment x.val
  let E := slowSpace A hA
  let D := (slowIndices A hA).card
  let e := slowFinBasis A hA
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
    rw [slowSpace_finrank] at hfin
    exact hfin
  have hs : Fintype.card s ≤ Fintype.card V := Fintype.card_subtype_le _
  have hDN : D ≤ Fintype.card V := (Finset.card_le_univ _).trans hs
  have hN : 0 < Fintype.card V := by
    have hh : 0 < Fintype.card s := Fintype.card_pos
    omega
  have hRank : (D:ℝ) ≤ 16*Λ*(Fintype.card V:ℝ)/d^2 := by
    have hh := slow_rank_diagonal_bound A hA d Λ hdiag
    rw [slowSpace_finrank] at hh
    apply hh.trans
    have hm := mul_le_mul_of_nonneg_left
      (show (Fintype.card s:ℝ) ≤ (Fintype.card V:ℝ) by exact_mod_cast hs)
      (show 0 ≤ 16*Λ/d^2 by positivity)
    convert hm using 1 <;> ring
  refine ⟨D,hDpos,hDN,hRank,?_⟩
  intro n hn x
  have ht := UniformSmoothingOccupation.fixed_family_tail C u huPos hu hstat γ hgap.1 hgap.2.1
    hA (shore_similarity_fixes_root G s t hbi hdeg)
    (shore_similarity_positive G s t hbi hdeg)
    (shore_chain_gap s G t hbi hdeg γ hgap)
    (Fintype.card V) D (by omega) hDN
    (shoreRoot_sq_lower G s t hbi hdeg d hd hmin hmax) E e hroot F hf μ hμ hμ1
    hmean r hr (by
      intro f hff y
      exact (chain_projectedFunction_tail C u huPos hu hA hp (Fintype.card V) hN d Λ hd
        (by linarith) (shoreRoot_sq_lower G s t hbi hdeg d hd hmin hmax) hdiag f (hf f hff) r hr y).trans hrsmall)
    n hn x
  apply ht.trans
  apply add_le_add le_rfl
  have hat := shoreRoot_prefactor_upper G s t hbi hdeg d hd hmin hmax x
  have hcoef : 0 ≤ (CoordinateGrid.alphabet (Fintype.card V) μ ^ D : ℕ)*(⌈2/(μ/1024)⌉₊:ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_left hat hcoef
  exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg _)

end Erdos642.CampaignFe72210bContinuation3.GraphSmoothingOccupation
