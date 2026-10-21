import Openmath.Erdos642.Proofs.Joint20261019.Energy
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators Matrix Topology
open Matrix Set
namespace Erdos642.Joint20261019.Energy
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def gradient (A : Matrix V V ℝ) (p : V → ℝ) (x : V) : ℝ :=
  1 - (∑ y, A x y * Real.sqrt (p y)) / Real.sqrt (p x)

theorem derivative_eq_gradient (A : Matrix V V ℝ) (hA : ∀ x y, A x y = A y x)
    (p z : V → ℝ) (hp : ∀ x, 0 < p x) :
    ((∑ x, z x) - ∑ x, ∑ y,
      (A x y * (z x / (2 * Real.sqrt (p x))) * Real.sqrt (p y) +
        A x y * Real.sqrt (p x) * (z y / (2 * Real.sqrt (p y))))) =
      ∑ x, z x * gradient A p x := by
  have heq : (∑ x, ∑ y, A x y * Real.sqrt (p x) * (z y / (2 * Real.sqrt (p y)))) =
      ∑ x, ∑ y, A x y * (z x / (2 * Real.sqrt (p x))) * Real.sqrt (p y) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hA y x]
    ring
  simp_rw [Finset.sum_add_distrib]
  rw [heq]
  simp only [gradient, mul_sub, mul_one, Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  field_simp [ne_of_gt (Real.sqrt_pos.2 (hp x))]
  <;> ring

theorem gradient_euler (A : Matrix V V ℝ) (p : V → ℝ) (hp : ∀ x, 0 < p x) :
    (∑ x, p x * gradient A p x) = energy A p := by
  simp only [gradient, energy, mul_sub, mul_one, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have hs := Real.sq_sqrt (le_of_lt (hp x))
  have hn := ne_of_gt (Real.sqrt_pos.2 (hp x))
  field_simp [hn]
  linear_combination -(A x y * Real.sqrt (p y)) * hs

theorem minimizer_gradient_support (A : Matrix V V ℝ)
    (hA : ∀ x y, A x y = A y x) (π : V → ℝ) (ε : ℝ)
    (K : Set (V → ℝ)) (hc : Convex ℝ K) (p : V → ℝ) (hpK : p ∈ K)
    (hp : ∀ x, 0 < p x + ε * π x)
    (hmin : ∀ q ∈ K, energy A (fun x => p x + ε * π x) ≤
      energy A (fun x => q x + ε * π x)) (q : V → ℝ) (hq : q ∈ K) :
    (∑ x, p x * gradient A (fun x => p x + ε * π x) x) ≤
      ∑ x, q x * gradient A (fun x => p x + ε * π x) x := by
  have hd := hasDerivAt_energy_line A (fun x => p x + ε * π x) (fun x => q x - p x) hp
  rw [derivative_eq_gradient A hA _ _ hp] at hd
  have hn := derivative_nonneg_of_segment_min hd (by
    intro t ht
    have hm := hmin ((1-t) • p + t • q)
      (hc hpK hq (by linarith [ht.2]) ht.1 (by ring))
    convert hm using 1 <;> congr 1 <;> funext x <;> simp <;> ring)
  simp_rw [sub_mul, Finset.sum_sub_distrib] at hn
  linarith

theorem transition_mulVec_pos (C : Erdos642.FiniteMarkov.Chain V)
    (v : V → ℝ) (hv : ∀ x, 0 < v x) (x : V) :
    0 < (C.transition *ᵥ v) x := by
  have hr : 0 < ∑ y, C.transition x y := by rw [C.row_sum]; norm_num
  obtain ⟨y, _, hy⟩ := (Finset.sum_pos_iff_of_nonneg (fun y _ => C.nonneg x y)).1 hr
  exact (Finset.sum_pos_iff_of_nonneg (fun y _ => mul_nonneg (C.nonneg x y) (hv y).le)).2
    ⟨y, Finset.mem_univ _, mul_pos hy (hv y)⟩

theorem gradient_chain (C : Erdos642.FiniteMarkov.Chain V) (u p : V → ℝ)
    (hu : ∀ x, 0 < u x) (hp : ∀ x, 0 < p x) (x : V) :
    gradient (C.similarTransition u) p x =
      1 - (C.transition *ᵥ (fun y => Real.sqrt (p y) / u y)) x /
        (Real.sqrt (p x) / u x) := by
  simp only [gradient, Erdos642.FiniteMarkov.Chain.similarTransition, Matrix.mulVec, dotProduct]
  congr 1
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  field_simp [ne_of_gt (hu x), ne_of_gt (hu y), ne_of_gt (Real.sqrt_pos.2 (hp x))]

theorem exists_supporting_potential (C : Erdos642.FiniteMarkov.Chain V)
    (u : V → ℝ) (hu : ∀ x, 0 < u x) (hnorm : ∑ x, u x ^ 2 = 1)
    (hA : ∀ x y, C.similarTransition u x y = C.similarTransition u y x)
    (K : Set (V → ℝ)) (hK : IsCompact K) (hne : K.Nonempty) (hc : Convex ℝ K)
    (hsimplex : K ⊆ stdSimplex ℝ V) (ε : ℝ) (hε : 0 < ε) :
    ∃ p ∈ K, ∃ v : V → ℝ, (∀ x, 0 < v x) ∧
      (∀ q ∈ K, energy (C.similarTransition u) (fun x => p x + ε * u x ^ 2) ≤
        energy (C.similarTransition u) (fun x => q x + ε * u x ^ 2)) ∧
      ∀ q ∈ K,
        energy (C.similarTransition u) (fun x => p x + ε * u x ^ 2) - ε ≤
          ∑ x, q x * Real.log (v x / (C.transition *ᵥ v) x) := by
  obtain ⟨p, hpK, hmin⟩ := exists_regularized_minimizer (C.similarTransition u)
    (fun x => u x ^ 2) K hK hne ε
  let r : V → ℝ := fun x => p x + ε * u x ^ 2
  have hr (x : V) : 0 < r x := add_pos_of_nonneg_of_pos ((hsimplex hpK).1 x)
    (mul_pos hε (sq_pos_of_pos (hu x)))
  let v : V → ℝ := fun x => Real.sqrt (r x) / u x
  have hv (x : V) : 0 < v x := div_pos (Real.sqrt_pos.2 (hr x)) (hu x)
  have hQ (x : V) := transition_mulVec_pos C v hv x
  let a := gradient (C.similarTransition u) r
  have ha (x : V) : a x = 1 - (C.transition *ᵥ v) x / v x :=
    gradient_chain C u r hu hr x
  have ha1 (x : V) : a x ≤ 1 := by
    rw [ha]
    have ht := div_pos (hQ x) (hv x)
    linarith
  have hag (x : V) : a x ≤ Real.log (v x / (C.transition *ᵥ v) x) := by
    rw [ha]
    simpa only [inv_div] using Real.one_sub_inv_le_log_of_pos (div_pos (hv x) (hQ x))
  refine ⟨p, hpK, v, hv, hmin, ?_⟩
  intro q hq
  have hs := minimizer_gradient_support (C.similarTransition u) hA (fun x => u x ^ 2)
    ε K hc p hpK hr hmin q hq
  have he := gradient_euler (C.similarTransition u) r hr
  have hpi : (∑ x, u x ^ 2 * a x) ≤ 1 := by
    rw [← hnorm]
    exact Finset.sum_le_sum fun x _ => mul_le_of_le_one_right (sq_nonneg _) (ha1 x)
  have hid : energy (C.similarTransition u) r =
      (∑ x, p x * a x) + ε * ∑ x, u x ^ 2 * a x := by
    rw [← he, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [r, a]
    ring
  have hlow : energy (C.similarTransition u) r - ε ≤ ∑ x, q x * a x := by
    change (∑ x, p x * a x) ≤ ∑ x, q x * a x at hs
    nlinarith
  exact hlow.trans (Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left (hag x) ((hsimplex hq).1 x))

end Erdos642.Joint20261019.Energy
