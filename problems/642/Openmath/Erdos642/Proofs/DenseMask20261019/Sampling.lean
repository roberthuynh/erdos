import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.CutOperations

/-! Actual induced-core pruning for the dense-mask sampling argument. -/
namespace Erdos642.DenseMask20261019.Sampling
open SimpleGraph Finset
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.CutExtraction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Deleting an actual boundary and maximizing edge potential produces an
actual induced minimum-degree core, with a charge for every further vertex. -/
theorem exists_pruned_sample (A B : Finset V) (hBA : B ⊆ A)
    (q alpha beta : ℝ) (hq : 0 ≤ q)
    (hlo : ∀ x ∈ A, alpha ≤ (restrictedDegree G A x : ℝ))
    (hhi : ∀ x ∈ A, (restrictedDegree G A x : ℝ) ≤ beta) :
    ∃ W : Finset V, W ⊆ A \ B ∧
      (∀ x ∈ W, q ≤ (restrictedDegree G W x : ℝ)) ∧
      (alpha - 2*q) * (((A \ B) \ W).card : ℝ) ≤ beta * (B.card : ℝ) := by
  classical
  let L := A \ B
  obtain ⟨W, hW, hmax⟩ := Finset.exists_max_image L.powerset
    (pruningPotential G q) (Finset.powerset_nonempty L)
  have hWL : W ⊆ L := Finset.mem_powerset.mp hW
  have hdeg : ∀ x ∈ W, q ≤ (restrictedDegree G W x : ℝ) := by
    intro x hx
    have he := hmax (W.erase x)
      (Finset.mem_powerset.mpr ((Finset.erase_subset x W).trans hWL))
    rw [pruningPotential_erase G q W x hx] at he
    rw [mask_degree_eq_restricted G W x hx] at he
    linarith
  let R := L \ W
  have hRA : R ⊆ A := (Finset.sdiff_subset.trans Finset.sdiff_subset)
  have hpot := hmax L (Finset.mem_powerset_self L)
  have hedge := edges_partition G L W hWL
  have hcard := Finset.card_sdiff_add_card_eq_card hWL
  have hcardR : (R.card : ℝ) + (W.card : ℝ) = (L.card : ℝ) := by
    exact_mod_cast hcard
  have hedgeR : (edges G L : ℝ) = (edges G W : ℝ) +
      (edges G R : ℝ) + (IncidenceCounts.count G W R : ℝ) := by
    exact_mod_cast hedge
  have hpotR : (edges G L : ℝ) - q*(L.card : ℝ) ≤
      (edges G W : ℝ) - q*(W.card : ℝ) := hpot
  have hbudget : (edges G R : ℝ) + (IncidenceCounts.count G W R : ℝ) ≤
      q*(R.card : ℝ) := by nlinarith [hcardR]
  have hlower : alpha*(R.card : ℝ) ≤ (IncidenceCounts.count G R A : ℝ) := by
    calc
      _ = ∑ x ∈ R, alpha := by simp [mul_comm]
      _ ≤ ∑ x ∈ R, (restrictedDegree G A x : ℝ) :=
        Finset.sum_le_sum (fun x hx => hlo x (hRA hx))
      _ = _ := by simp [IncidenceCounts.count, restrictedDegree]
  have hupper : (IncidenceCounts.count G B R : ℝ) ≤ beta*(B.card : ℝ) := by
    have hb : ∀ x ∈ B, (restrictedDegree G R x : ℝ) ≤ beta := by
      intro x hx
      have hs : R.filter (G.Adj x) ⊆ A.filter (G.Adj x) :=
        Finset.filter_subset_filter _ hRA
      have hle : (restrictedDegree G R x : ℝ) ≤ (restrictedDegree G A x : ℝ) := by
        exact_mod_cast Finset.card_le_card hs
      exact hle.trans (hhi x (hBA hx))
    calc
      _ = ∑ x ∈ B, (restrictedDegree G R x : ℝ) := by
        simp [IncidenceCounts.count, restrictedDegree]
      _ ≤ ∑ x ∈ B, beta := Finset.sum_le_sum hb
      _ = _ := by simp [mul_comm]
  have hp := count_partition_right G A B R hBA
  have hp' := count_partition_right G L W R hWL
  have hs := count_self_eq_twice_edges G R
  have hswap := IncidenceCounts.count_swap G R W
  have hswapB := IncidenceCounts.count_swap G R B
  have heq : IncidenceCounts.count G R A = IncidenceCounts.count G B R +
      IncidenceCounts.count G W R + 2*edges G R := by
    change IncidenceCounts.count G R A = IncidenceCounts.count G R B +
      IncidenceCounts.count G R L at hp
    change IncidenceCounts.count G R L = IncidenceCounts.count G R W +
      IncidenceCounts.count G R R at hp'
    omega
  have heqR : (IncidenceCounts.count G R A : ℝ) =
      (IncidenceCounts.count G B R : ℝ) +
      (IncidenceCounts.count G W R : ℝ) + 2*(edges G R : ℝ) := by
    exact_mod_cast heq
  have hc0 : (0 : ℝ) ≤ IncidenceCounts.count G W R := Nat.cast_nonneg _
  refine ⟨W, hWL, hdeg, ?_⟩
  change (alpha-2*q)*(R.card : ℝ) ≤ beta*(B.card : ℝ)
  nlinarith

end Erdos642.DenseMask20261019.Sampling
