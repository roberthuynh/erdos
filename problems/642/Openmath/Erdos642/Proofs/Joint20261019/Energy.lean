import Openmath.Erdos642.Proofs.CampaignFe72210b.ReversibleMoment
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real

open scoped BigOperators Matrix Topology
open Matrix Set

namespace Erdos642.Joint20261019.Energy

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def energy (A : Matrix V V ℝ) (p : V → ℝ) : ℝ :=
  (∑ x, p x) - ∑ x, ∑ y, A x y * Real.sqrt (p x) * Real.sqrt (p y)

theorem energy_eq_dotProduct (A : Matrix V V ℝ) (p : V → ℝ) :
    energy A p = (∑ x, p x) - dotProduct (fun x => Real.sqrt (p x))
      (A *ᵥ fun x => Real.sqrt (p x)) := by
  simp only [energy, Matrix.mulVec, dotProduct]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem continuous_energy (A : Matrix V V ℝ) : Continuous (energy A) := by
  unfold energy
  fun_prop

theorem exists_regularized_minimizer (A : Matrix V V ℝ) (π : V → ℝ)
    (K : Set (V → ℝ)) (hK : IsCompact K) (hne : K.Nonempty) (ε : ℝ) :
    ∃ p ∈ K, ∀ q ∈ K,
      energy A (fun x => p x + ε * π x) ≤ energy A (fun x => q x + ε * π x) := by
  exact hK.exists_isMinOn hne ((continuous_energy A).comp (by fun_prop)).continuousOn

/-- The derivative along an arbitrary affine direction, before using symmetry. -/
theorem hasDerivAt_energy_line (A : Matrix V V ℝ) (p z : V → ℝ)
    (hp : ∀ x, 0 < p x) :
    HasDerivAt (fun t : ℝ => energy A (fun x => p x + t * z x))
      ((∑ x, z x) - ∑ x, ∑ y,
        (A x y * (z x / (2 * Real.sqrt (p x))) * Real.sqrt (p y) +
          A x y * Real.sqrt (p x) * (z y / (2 * Real.sqrt (p y))))) 0 := by
  have hd (x : V) : HasDerivAt (fun t : ℝ => p x + t * z x) (z x) 0 := by
    exact (hasDerivAt_mul_const (x := (0 : ℝ)) (z x)).const_add (p x)
  have hs (x : V) : HasDerivAt (fun t : ℝ => Real.sqrt (p x + t * z x))
      (z x / (2 * Real.sqrt (p x))) 0 := by
    simpa using (hd x).sqrt (by simpa using ne_of_gt (hp x))
  unfold energy
  simpa only [zero_mul, add_zero, Pi.sub_apply, Pi.mul_apply] using
    (HasDerivAt.fun_sum (u := Finset.univ) fun x _ => hd x).fun_sub
      (HasDerivAt.fun_sum (u := Finset.univ) fun x _ =>
        HasDerivAt.fun_sum (u := Finset.univ) fun y _ =>
          ((hs x).const_mul (A x y)).mul (hs y))

/-- A differentiable function minimized on a closed unit segment has nonnegative right slope. -/
theorem derivative_nonneg_of_segment_min {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hmin : ∀ t ∈ Icc (0 : ℝ) 1, f 0 ≤ f t) :
    0 ≤ d := by
  have hm : IsLocalMinOn f (Icc (0 : ℝ) 1) 0 := (show IsMinOn f (Icc (0 : ℝ) 1) 0 from hmin).localize
  have ht : (1 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) 1) 0 := by
    have h := sub_mem_posTangentConeAt_of_openSegment_subset
      (show openSegment ℝ (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 from
        (openSegment_subset_segment ℝ 0 1).trans (by rw [segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]))
    simpa using h
  simpa using hm.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt ht

end Erdos642.Joint20261019.Energy
