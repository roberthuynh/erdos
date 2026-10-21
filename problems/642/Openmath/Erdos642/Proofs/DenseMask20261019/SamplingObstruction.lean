import Openmath.Erdos642.Proofs.DenseMask20261019.Sampling

/-! A bad sampled set leaves an actual nonempty separated minimum-degree core. -/
namespace Erdos642.DenseMask20261019.SamplingObstruction

open SimpleGraph Finset
open Erdos642.CampaignFe72210bContinuation3.CutExtraction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The boundary premise is the actual no-edge-outside-bad-set condition.
The resulting core retains both a degree bound and separation inside W. -/
theorem exists_separated_bad_core (A B U : Finset V) (hBA : B ⊆ A) (hUA : U ⊆ A)
    (hUB : Disjoint U B)
    (hboundary : ∀ x ∈ U, ∀ y ∈ A, G.Adj x y → y ∈ U ∨ y ∈ B)
    (q alpha beta : ℝ) (hq : 0 ≤ q) (hgap : 0 < alpha - 2*q)
    (hlo : ∀ x ∈ A, alpha ≤ (restrictedDegree G A x : ℝ))
    (hhi : ∀ x ∈ A, (restrictedDegree G A x : ℝ) ≤ beta)
    (hbudget : beta * (B.card : ℝ) < (alpha - 2*q) * (U.card : ℝ)) :
    ∃ W : Finset V, W ⊆ A \ B ∧
      (∀ x ∈ W, q ≤ (restrictedDegree G W x : ℝ)) ∧
      (U ∩ W).Nonempty ∧
      (∀ x ∈ U ∩ W, q ≤ (restrictedDegree G (U ∩ W) x : ℝ)) ∧
      (∀ x ∈ U ∩ W, ∀ y ∈ W, G.Adj x y → y ∈ U ∩ W) ∧
      (alpha - 2*q) * ((U \ W).card : ℝ) ≤ beta * (B.card : ℝ) := by
  classical
  obtain ⟨W, hW, hdegree, hcharge⟩ :=
    Sampling.exists_pruned_sample G A B hBA q alpha beta hq hlo hhi
  have hUAB : U ⊆ A \ B := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hUA hx, fun hb => Finset.disjoint_left.mp hUB hx hb⟩
  have hdiscard : U \ W ⊆ (A \ B) \ W := by
    intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨hUAB (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
  have hsmall : ((U \ W).card : ℝ) ≤ (((A \ B) \ W).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hdiscard
  have hchargeU : (alpha - 2*q) * ((U \ W).card : ℝ) ≤ beta * (B.card : ℝ) :=
    (mul_le_mul_of_nonneg_left hsmall hgap.le).trans hcharge
  have hclosed : ∀ x ∈ U ∩ W, ∀ y ∈ W, G.Adj x y → y ∈ U ∩ W := by
    intro x hx y hy hxy
    have hyAB := Finset.mem_sdiff.mp (hW hy)
    rcases hboundary x (Finset.mem_inter.mp hx).1 y hyAB.1 hxy with hyU | hyB
    · exact Finset.mem_inter.mpr ⟨hyU, hy⟩
    · exact (hyAB.2 hyB).elim
  have hretained : ∀ x ∈ U ∩ W,
      restrictedDegree G (U ∩ W) x = restrictedDegree G W x := by
    intro x hx
    unfold restrictedDegree
    apply congrArg Finset.card
    ext y
    simp only [Finset.mem_filter]
    exact ⟨fun hy => ⟨(Finset.mem_inter.mp hy.1).2, hy.2⟩,
      fun hy => ⟨hclosed x hx y hy.1 hy.2, hy.2⟩⟩
  have hnonempty : (U ∩ W).Nonempty := by
    apply Finset.card_pos.mp
    by_contra hnot
    have hz : (U ∩ W).card = 0 := by omega
    have hpart := Finset.card_inter_add_card_sdiff U W
    have heq : (U \ W).card = U.card := by omega
    rw [heq] at hchargeU
    exact (not_lt_of_ge hchargeU) hbudget
  refine ⟨W, hW, hdegree, hnonempty, ?_, hclosed, hchargeU⟩
  intro x hx
  rw [hretained x hx]
  exact hdegree x (Finset.mem_inter.mp hx).2

end Erdos642.DenseMask20261019.SamplingObstruction
