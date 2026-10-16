import Openmath.Erdos642.Proofs.CampaignFe72210b.HeatKernel
import Openmath.Erdos642.Proofs.CampaignFe72210b.PathCoordinates
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum

/-! Actual short-block hitting from genuine path marginals and the graph heat kernel. -/

namespace Erdos642.CampaignFe72210b

/-- The finite geometric estimate includes the endpoint gap `γ = 1`. -/
theorem finite_geom_gap_sum_le (γ : ℝ) (hγ : 0 < γ) (hγone : γ ≤ 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 - γ) ^ i) ≤ 1 / γ := by
  have hp : 0 ≤ (1 - γ) ^ n := pow_nonneg (sub_nonneg.mpr hγone) n
  have he : (∑ i ∈ Finset.range n, (1 - γ) ^ i) * γ = 1 - (1 - γ) ^ n := by
    simpa only [sub_sub_cancel] using geom_sum_mul_neg (1 - γ) n
  apply (le_div_iff₀ hγ).2
  nlinarith

/-- Separate the first transition from the smoothed finite geometric remainder. -/
theorem shortBlock_kernel_sum_le (k : ℕ) (hk : 2 ≤ k) (d γ A B : ℝ)
    (_hd : 0 < d) (hγ : 0 < γ) (hγone : γ ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : ℕ → ℝ) (hfirst : f 1 ≤ 1 / d)
    (hlater : ∀ t, 2 ≤ t → t ≤ k → f t ≤ A + B * (1 - γ) ^ (t - 2)) :
    (∑ t ∈ Finset.Icc 1 k, f t) ≤ 1 / d + (k : ℝ) * A + B / γ := by
  have hsplit : (∑ t ∈ Finset.Icc 1 k, f t) =
      f 1 + ∑ i ∈ Finset.range (k - 1), f (i + 2) := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    rw [← Finset.sum_Ico_consecutive f (by omega : 1 ≤ 2) (by omega : 2 ≤ k + 1)]
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, Finset.sum_Ico_eq_sum_range]
    have he : k + 1 - 2 = k - 1 := by omega
    simp only [he, Nat.add_comm]
  have hsum : (∑ i ∈ Finset.range (k - 1), f (i + 2)) ≤ (k : ℝ) * A + B / γ := by
    calc
      _ ≤ ∑ i ∈ Finset.range (k - 1), (A + B * (1 - γ) ^ i) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        simpa using hlater (i + 2) (by omega) (by omega)
      _ = ((k - 1 : ℕ) : ℝ) * A +
          B * (∑ i ∈ Finset.range (k - 1), (1 - γ) ^ i) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
      _ ≤ (k : ℝ) * A + B * (1 / γ) :=
        add_le_add
          (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le k 1) hA)
          (mul_le_mul_of_nonneg_left (finite_geom_gap_sum_le γ hγ hγone (k - 1)) hB)
      _ = (k : ℝ) * A + B / γ := by ring
  rw [hsplit]
  have := add_le_add hfirst hsum
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual graph path hits a fixed set of at most k vertices with the
reviewed spectral short-block upper bound. Counts refer to steps1,...,k. -/
theorem graph_actualHit_shortBlock_le (hdeg : ∀ x : V, 0 < G.degree x)
    (γ d R : ℝ) (hgap : HasBipartiteSpectralGap G γ) (hbip : G.IsBipartite)
    (hd : 0 < d) (hR : 1 ≤ R)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ R * d)
    (k : ℕ) (hk : 2 ≤ k) (S : Finset V) (hS : S.card ≤ k) (x : V) :
    (graphChain G hdeg).eventMass k (Erdos642.FiniteMarkov.PathCoordinates.actualHit S) x ≤
      (k : ℝ) / d + 2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
        Real.sqrt R * (k : ℝ) / (d * γ) := by
  classical
  have hγ : 0 < γ := hgap.1
  have hγone : γ ≤ 1 := hgap.2.1
  let A : ℝ := 2 * R / (Fintype.card V : ℝ)
  let B : ℝ := Real.sqrt R / d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := div_nonneg (Real.sqrt_nonneg _) hd.le
  have hpoint (a : V) : (∑ t ∈ Finset.Icc 1 k, (graphTransition G ^ t) x a) ≤
      1 / d + (k : ℝ) * A + B / γ := by
    apply shortBlock_kernel_sum_le k hk d γ A B hd hγ hγone hA hB
    · simpa only [pow_one] using transition_entry_le G d hd hmin x a
    · intro t ht htk
      calc
        _ ≤ 2 * R / (Fintype.card V : ℝ) + Real.sqrt R * (1 - γ) ^ (t - 2) / d :=
          graphTransition_pow_heatKernel G γ d R hgap hbip hd hR hmin hmax t ht x a
        _ = A + B * (1 - γ) ^ (t - 2) := by dsimp [A, B]; ring
  have hbound : 0 ≤ 1 / d + (k : ℝ) * A + B / γ := by positivity
  have hScast : (S.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hS
  have hunion := (graphChain G hdeg).actualHit_mass_le k S x
  change (graphChain G hdeg).eventMass k
      (Erdos642.FiniteMarkov.PathCoordinates.actualHit S) x ≤
    ∑ t ∈ Finset.Icc 1 k, ∑ a ∈ S, (graphTransition G ^ t) x a at hunion
  apply hunion.trans
  calc
    (∑ t ∈ Finset.Icc 1 k, ∑ a ∈ S, (graphTransition G ^ t) x a) =
        ∑ a ∈ S, ∑ t ∈ Finset.Icc 1 k, (graphTransition G ^ t) x a := Finset.sum_comm
    _ ≤ ∑ _a ∈ S, (1 / d + (k : ℝ) * A + B / γ) :=
      Finset.sum_le_sum fun a _ => hpoint a
    _ = (S.card : ℝ) * (1 / d + (k : ℝ) * A + B / γ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ) * (1 / d + (k : ℝ) * A + B / γ) :=
      mul_le_mul_of_nonneg_right hScast hbound
    _ = (k : ℝ) / d + 2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
        Real.sqrt R * (k : ℝ) / (d * γ) := by
      dsimp [A, B]
      field_simp

end Erdos642.CampaignFe72210b
