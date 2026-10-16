import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.FourthDiagonal
import Openmath.Erdos642.Proofs.CampaignFe72210b.ShortBlockCollisions
import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphBlockMixing

namespace Erdos642.CampaignFe72210bContinuation3
open Erdos642.CampaignFe72210b
open Matrix

theorem fourthBlock_kernel_sum_le (k : ℕ) (hk : 4 ≤ k) (d γ A B : ℝ)
    (hγ : 0 < γ) (hγone : γ ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : ℕ → ℝ) (hearly : ∀ t, 1 ≤ t → t < 4 → f t ≤ 1 / d)
    (hlater : ∀ t, 4 ≤ t → t ≤ k → f t ≤ A + B * (1 - γ) ^ (t - 4)) :
    (∑ t ∈ Finset.Icc 1 k, f t) ≤ 3 / d + (k : ℝ) * A + B / γ := by
  have hsplit : (∑ t ∈ Finset.Icc 1 k, f t) =
      (∑ i ∈ Finset.range 3, f (i + 1)) + ∑ i ∈ Finset.range (k - 3), f (i + 4) := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    rw [← Finset.sum_Ico_consecutive f (by omega : 1 ≤ 4) (by omega : 4 ≤ k + 1)]
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have he : k + 1 - 4 = k - 3 := by omega
    simp only [he, Nat.add_comm]
  have hfirst : (∑ i ∈ Finset.range 3, f (i + 1)) ≤ 3 / d := by
    calc
      _ ≤ ∑ _i ∈ Finset.range 3, (1 / d) := by
        apply Finset.sum_le_sum
        intro i hi
        have := Finset.mem_range.mp hi
        exact hearly (i + 1) (by omega) (by omega)
      _ = _ := by simp; ring
  have hrest : (∑ i ∈ Finset.range (k - 3), f (i + 4)) ≤ (k : ℝ) * A + B / γ := by
    calc
      _ ≤ ∑ i ∈ Finset.range (k - 3), (A + B * (1 - γ) ^ i) := by
        apply Finset.sum_le_sum
        intro i hi
        have := Finset.mem_range.mp hi
        simpa using hlater (i + 4) (by omega) (by omega)
      _ = ((k - 3 : ℕ) : ℝ) * A + B * (∑ i ∈ Finset.range (k - 3), (1 - γ) ^ i) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
      _ ≤ (k : ℝ) * A + B * (1 / γ) :=
        add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le k 3) hA)
          (mul_le_mul_of_nonneg_left (finite_geom_gap_sum_le γ hγ hγone (k - 3)) hB)
      _ = _ := by ring
  rw [hsplit]
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Nonempty V] in
theorem graphTransition_positive_power_le_inv_degree
    (hdeg : ∀ x : V, 0 < G.degree x) (d : ℝ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (r : ℕ) (hr : 1 ≤ r) (x y : V) : (graphTransition G ^ r) x y ≤ 1 / d := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  rw [pow_succ, Matrix.mul_apply]
  calc
    _ ≤ ∑ z, (graphTransition G ^ n) x z * (1 / d) := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left (transition_entry_le G d hd hmin z y)
        (graphTransition_pow_nonneg G hdeg n x z)
    _ = 1 / d := by rw [← Finset.sum_mul, graphTransition_pow_row_sum G hdeg, one_mul]

theorem fourthMoment_parameter_nonneg (hdeg : ∀ x : V, 0 < G.degree x)
    (d Λ : ℝ) (hd : 0 < d)
    (hmoment : ∀ z : V, (graphTransition G ^ 4) z z ≤ Λ / d ^ 2) : 0 ≤ Λ := by
  let x : V := Classical.choice inferInstance
  have hh : 0 ≤ Λ / d ^ 2 := (graphTransition_pow_nonneg G hdeg 4 x x).trans (hmoment x)
  have hm := mul_nonneg hh (sq_nonneg d)
  rwa [div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hd))] at hm

/-- The actual graph path hits a fixed set of at most k vertices with the
reviewed spectral short-block upper bound. Counts refer to steps1,...,k. -/
theorem graph_actualHit_fourthBlock_le (hdeg : ∀ x : V, 0 < G.degree x)
    (γ d R Λ : ℝ) (hgap : HasBipartiteSpectralGap G γ) (hbip : G.IsBipartite)
    (hd : 0 < d) (hR : 1 ≤ R)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ R * d)
    (hmoment : ∀ z : V, (graphTransition G ^ 4) z z ≤ Λ / d ^ 2)
    (k : ℕ) (hk : 4 ≤ k) (S : Finset V) (hS : S.card ≤ k) (x : V) :
    (graphChain G hdeg).eventMass k (Erdos642.FiniteMarkov.PathCoordinates.actualHit S) x ≤
      3 * (k : ℝ) / d + 2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
        Real.sqrt R * Λ * (k : ℝ) / (d ^ 2 * γ) := by
  classical
  have hγ : 0 < γ := hgap.1
  have hγone : γ ≤ 1 := hgap.2.1
  let A : ℝ := 2 * R / (Fintype.card V : ℝ)
  have hΛ := fourthMoment_parameter_nonneg G hdeg d Λ hd hmoment
  let B : ℝ := Real.sqrt R * Λ / d ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint (a : V) : (∑ t ∈ Finset.Icc 1 k, (graphTransition G ^ t) x a) ≤
      3 / d + (k : ℝ) * A + B / γ := by
    apply fourthBlock_kernel_sum_le k hk d γ A B hγ hγone hA hB
    · intro r hr _
      exact graphTransition_positive_power_le_inv_degree G hdeg d hd hmin r hr x a
    · intro t ht htk
      calc
        _ ≤ 2 * R / (Fintype.card V : ℝ) + Real.sqrt R * Λ * (1 - γ) ^ (t - 4) / d ^ 2 :=
          graphTransition_pow_fourth_heatKernel G γ d R Λ hgap hbip hd hR hmin hmax hmoment t ht x a
        _ = A + B * (1 - γ) ^ (t - 4) := by dsimp [A, B]; ring
  have hbound : 0 ≤ 3 / d + (k : ℝ) * A + B / γ := by positivity
  have hScast : (S.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hS
  have hunion := (graphChain G hdeg).actualHit_mass_le k S x
  change (graphChain G hdeg).eventMass k
      (Erdos642.FiniteMarkov.PathCoordinates.actualHit S) x ≤
    ∑ t ∈ Finset.Icc 1 k, ∑ a ∈ S, (graphTransition G ^ t) x a at hunion
  apply hunion.trans
  calc
    (∑ t ∈ Finset.Icc 1 k, ∑ a ∈ S, (graphTransition G ^ t) x a) =
        ∑ a ∈ S, ∑ t ∈ Finset.Icc 1 k, (graphTransition G ^ t) x a := Finset.sum_comm
    _ ≤ ∑ _a ∈ S, (3 / d + (k : ℝ) * A + B / γ) :=
      Finset.sum_le_sum fun a _ => hpoint a
    _ = (S.card : ℝ) * (3 / d + (k : ℝ) * A + B / γ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ) * (3 / d + (k : ℝ) * A + B / γ) :=
      mul_le_mul_of_nonneg_right hScast hbound
    _ = 3 * (k : ℝ) / d + 2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
        Real.sqrt R * Λ * (k : ℝ) / (d ^ 2 * γ) := by
      dsimp [A, B]
      field_simp


/-- The actual path's failure of self-avoidance has the reviewed spectral J
bound. Repeated coordinates include returns to time zero. -/
theorem graph_not_actualSA_fourthBlock_le (hdeg : ∀ x : V, 0 < G.degree x)
    (γ d R Λ : ℝ) (hgap : HasBipartiteSpectralGap G γ) (hbip : G.IsBipartite)
    (hd : 0 < d) (hR : 1 ≤ R)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ R * d)
    (hmoment : ∀ z : V, (graphTransition G ^ 4) z z ≤ Λ / d ^ 2)
    (k : ℕ) (hk : 4 ≤ k) (x : V) :
    (graphChain G hdeg).eventMass k
      (fun z p => ¬ Erdos642.FiniteMarkov.PathAvoidance.actualSA z p) x ≤
      3 * (k : ℝ) / d + 2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
        Λ * (k : ℝ) / (d ^ 2 * γ) := by
  classical
  have hγ : 0 < γ := hgap.1
  have hγone : γ ≤ 1 := hgap.2.1
  have hρ : 0 ≤ 1 - γ := sub_nonneg.mpr hγone
  let A : ℝ := 2 * R / (Fintype.card V : ℝ)
  have hΛ := fourthMoment_parameter_nonneg G hdeg d Λ hd hmoment
  let B : ℝ := Λ / d ^ 2
  let b : ℕ → ℝ := fun ell => if ell < 4 then 1 / d else A + B * (1 - γ) ^ (ell - 4)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb : ∀ ell ∈ Finset.Icc 1 k, 0 ≤ b ell := by
    intro ell _
    dsimp [b]
    split_ifs
    · exact (one_div_pos.mpr hd).le
    · exact add_nonneg hA (mul_nonneg hB (pow_nonneg hρ _))
  have hreturn : ∀ ell ∈ Finset.Icc 1 k, ∀ v : V,
      ((graphChain G hdeg).transition ^ ell) v v ≤ b ell := by
    intro ell hell v
    have hell' := Finset.mem_Icc.mp hell
    change (graphTransition G ^ ell) v v ≤ b ell
    by_cases he : ell < 4
    · simp only [b, he, if_true]
      exact graphTransition_positive_power_le_inv_degree G hdeg d hd hmin ell hell'.1 v v
    · have hfour : 4 ≤ ell := by omega
      calc
        _ ≤ 2 * R / (Fintype.card V : ℝ) + Λ * (1 - γ) ^ (ell - 4) / d ^ 2 :=
          graphTransition_pow_fourth_diagonal_heatKernel G γ d R Λ hgap hbip hd hR hmin hmax hmoment ell hfour v
        _ = b ell := by simp only [b, he, if_false]; dsimp [A, B]; ring
  have hsum : (∑ ell ∈ Finset.Icc 1 k, b ell) ≤ 3 / d + (k : ℝ) * A + B / γ := by
    apply fourthBlock_kernel_sum_le k hk d γ A B hγ hγone hA hB
    · intro ell _ he
      simp [b, he]
    · intro ell hfour _
      have he : ¬ ell < 4 := by omega
      simp [b, he]
  apply ((graphChain G hdeg).not_actualSA_mass_le_return_sum k b hb hreturn x).trans
  calc
    (k : ℝ) * (∑ ell ∈ Finset.Icc 1 k, b ell) ≤
        (k : ℝ) * (3 / d + (k : ℝ) * A + B / γ) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = 3 * (k : ℝ) / d + 2 * R * (k : ℝ) ^ 2 / (Fintype.card V : ℝ) +
        Λ * (k : ℝ) / (d ^ 2 * γ) := by
      dsimp [A, B]
      field_simp


end Erdos642.CampaignFe72210bContinuation3
