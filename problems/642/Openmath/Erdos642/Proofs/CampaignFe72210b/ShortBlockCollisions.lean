import Openmath.Erdos642.Proofs.CampaignFe72210b.PathCollisions
import Openmath.Erdos642.Proofs.CampaignFe72210b.ShortBlockHitting

/-! Actual short-block collision bounds, including the starting coordinate. -/

namespace Erdos642.CampaignFe72210b

/-- With one-step return zero, no time-one degree loss enters the return sum. -/
theorem shortBlock_return_sum_le (k : ℕ) (hk : 2 ≤ k) (γ A B : ℝ)
    (hγ : 0 < γ) (hγone : γ ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : ℕ → ℝ) (hfirst : f 1 ≤ 0)
    (hlater : ∀ t, 2 ≤ t → t ≤ k → f t ≤ A + B * (1 - γ) ^ (t - 2)) :
    (∑ t ∈ Finset.Icc 1 k, f t) ≤ (k : ℝ) * A + B / γ := by
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
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual path's failure of self-avoidance has the reviewed spectral J
bound. Repeated coordinates include returns to time zero. -/
theorem graph_not_actualSA_shortBlock_le (hdeg : ∀ x : V, 0 < G.degree x)
    (γ d R : ℝ) (hgap : HasBipartiteSpectralGap G γ) (hbip : G.IsBipartite)
    (hd : 0 < d) (hR : 1 ≤ R)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ R * d)
    (k : ℕ) (hk : 2 ≤ k) (x : V) :
    (graphChain G hdeg).eventMass k
      (fun z p => ¬ Erdos642.FiniteMarkov.PathAvoidance.actualSA z p) x ≤
      2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
        Real.sqrt R * (k : ℝ) / (d * γ) := by
  classical
  have hγ : 0 < γ := hgap.1
  have hγone : γ ≤ 1 := hgap.2.1
  have hρ : 0 ≤ 1 - γ := sub_nonneg.mpr hγone
  let A : ℝ := 2 * R / (Fintype.card V : ℝ)
  let B : ℝ := Real.sqrt R / d
  let b : ℕ → ℝ := fun ell => if ell = 1 then 0 else A + B * (1 - γ) ^ (ell - 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := div_nonneg (Real.sqrt_nonneg _) hd.le
  have hb : ∀ ell ∈ Finset.Icc 1 k, 0 ≤ b ell := by
    intro ell _
    dsimp [b]
    split_ifs
    · exact le_rfl
    · exact add_nonneg hA (mul_nonneg hB (pow_nonneg hρ _))
  have hreturn : ∀ ell ∈ Finset.Icc 1 k, ∀ v : V,
      ((graphChain G hdeg).transition ^ ell) v v ≤ b ell := by
    intro ell hell v
    have hell' := Finset.mem_Icc.mp hell
    change (graphTransition G ^ ell) v v ≤ b ell
    by_cases he : ell = 1
    · simp [b, he, graphTransition, SimpleGraph.adjMatrix_apply]
    · have htwo : 2 ≤ ell := by omega
      calc
        _ ≤ 2 * R / (Fintype.card V : ℝ) + Real.sqrt R * (1 - γ) ^ (ell - 2) / d :=
          graphTransition_pow_heatKernel G γ d R hgap hbip hd hR hmin hmax ell htwo v v
        _ = b ell := by simp only [b, he, if_false]; dsimp [A, B]; ring
  have hsum : (∑ ell ∈ Finset.Icc 1 k, b ell) ≤ (k : ℝ) * A + B / γ := by
    apply shortBlock_return_sum_le k hk γ A B hγ hγone hA hB
    · simp [b]
    · intro ell htwo _hell
      have he : ell ≠ 1 := by omega
      simp [b, he]
  apply ((graphChain G hdeg).not_actualSA_mass_le_return_sum k b hb hreturn x).trans
  calc
    (k : ℝ) * (∑ ell ∈ Finset.Icc 1 k, b ell) ≤
        (k : ℝ) * ((k : ℝ) * A + B / γ) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = 2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
        Real.sqrt R * (k : ℝ) / (d * γ) := by
      dsimp [A, B]
      field_simp

end Erdos642.CampaignFe72210b
