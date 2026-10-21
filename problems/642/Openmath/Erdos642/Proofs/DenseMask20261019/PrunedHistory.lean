import Openmath.Erdos642.Proofs.DenseMask20261019.Sampling

/-! Quantitative pruning of an actual bad sampled history. -/
namespace Erdos642.DenseMask20261019.PrunedHistory
open SimpleGraph Finset
open Erdos642.CampaignFe72210bContinuation3.CutExtraction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- All retained vertices and edges are original; the closed bad core is
literally U intersect W, with the complete boundary deletion charged. -/
theorem exists_pruned_history (A B U : Finset V) (rho D k b : ℝ)
    (hBA : B ⊆ A) (hUA : U ⊆ A) (hUB : Disjoint U B)
    (hboundary : ∀ x ∈ U, ∀ y ∈ A, G.Adj x y → y ∈ U ∨ y ∈ B)
    (hrho : 0 < rho) (hD : 1 ≤ D) (hk : rho/4 ≤ k) (hb : 0 ≤ b)
    (hU : (U.card : ℝ) = k) (hB : (B.card : ℝ) ≤ b)
    (hsmall : 16*D*b ≤ k/10)
    (hlo : ∀ x ∈ A, rho/2 ≤ (restrictedDegree G A x : ℝ))
    (hhi : ∀ x, (restrictedDegree G A x : ℝ) ≤ 2*D*rho) :
    ∃ W : Finset V, W ⊆ A \ B ∧
      (∀ x ∈ W, rho/8 ≤ (restrictedDegree G W x : ℝ)) ∧
      (∀ x ∈ U ∩ W, ∀ y ∈ W, G.Adj x y → y ∈ U ∩ W) ∧
      9*k/10 ≤ ((U ∩ W).card : ℝ) ∧
      ((U ∩ W).card : ℝ) ≤ k ∧
      1 ≤ W.card ∧ ((A \ W).card : ℝ) ≤ (1+16*D)*b := by
  classical
  obtain ⟨W,hW,hdegree,hcharge⟩ := Sampling.exists_pruned_sample G A B hBA
    (rho/8) (rho/2) (2*D*rho) (by positivity) hlo (fun x _ => hhi x)
  let R := (A \ B) \ W
  have hD0 : 0 ≤ D := by linarith
  have hR : (R.card : ℝ) ≤ 8*D*(B.card : ℝ) := by
    apply (mul_le_mul_iff_right₀ hrho).mp
    change (rho/2-2*(rho/8))*(R.card : ℝ) ≤ 2*D*rho*(B.card : ℝ) at hcharge
    nlinarith only [hcharge]
  have hRb : (R.card : ℝ) ≤ 16*D*b := by
    have hm := mul_le_mul_of_nonneg_left hB (show 0 ≤ 8*D by positivity)
    have hDb : 0 ≤ D*b := mul_nonneg hD0 hb
    nlinarith
  have hUAB : U ⊆ A \ B := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hUA hx, fun hxB => Finset.disjoint_left.mp hUB hx hxB⟩
  have hdiscard : U \ W ⊆ R := by
    intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨hUAB (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
  have hdiscardR : ((U \ W).card : ℝ) ≤ (R.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hdiscard
  have hpart : ((U ∩ W).card : ℝ) + ((U \ W).card : ℝ) = (U.card : ℝ) := by
    exact_mod_cast Finset.card_inter_add_card_sdiff U W
  have hcorelo : 9*k/10 ≤ ((U ∩ W).card : ℝ) := by linarith
  have hcorehi : ((U ∩ W).card : ℝ) ≤ k := by
    rw [← hU]
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_left : U ∩ W ⊆ U)
  have hclosed : ∀ x ∈ U ∩ W, ∀ y ∈ W, G.Adj x y → y ∈ U ∩ W := by
    intro x hx y hy hxy
    have hyAB := Finset.mem_sdiff.mp (hW hy)
    rcases hboundary x (Finset.mem_inter.mp hx).1 y hyAB.1 hxy with hyU | hyB
    · exact Finset.mem_inter.mpr ⟨hyU,hy⟩
    · exact (hyAB.2 hyB).elim
  have hWcard : 1 ≤ W.card := by
    have hc : 0 < ((U ∩ W).card : ℝ) := by linarith
    have hn : 0 < (U ∩ W).card := by exact_mod_cast hc
    have hh := Finset.card_le_card (Finset.inter_subset_right : U ∩ W ⊆ W)
    omega
  have hWA : W ⊆ A := hW.trans Finset.sdiff_subset
  have hcardAW := Finset.card_sdiff_add_card_eq_card hWA
  have hcardAB := Finset.card_sdiff_add_card_eq_card hBA
  have hcardR := Finset.card_sdiff_add_card_eq_card hW
  have htotal : (A \ W).card = B.card + R.card := by
    change R.card + W.card = (A \ B).card at hcardR
    omega
  have htotalR : ((A \ W).card : ℝ) = (B.card : ℝ) + (R.card : ℝ) := by
    exact_mod_cast htotal
  refine ⟨W,hW,hdegree,hclosed,hcorelo,hcorehi,hWcard,?_⟩
  nlinarith [htotalR]

end Erdos642.DenseMask20261019.PrunedHistory
