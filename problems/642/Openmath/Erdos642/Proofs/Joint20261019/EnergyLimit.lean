import Openmath.Erdos642.Proofs.Joint20261019.Energy

namespace Erdos642.Joint20261019.Energy
open Set Filter
open scoped Topology
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Uniform continuity pays both the regularization error and its epsilon penalty. -/
theorem exists_small_regularization (A : Matrix V V ℝ) (π : V → ℝ)
    (K : Set (V → ℝ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ K,
      energy A q - δ ≤ energy A (fun x => q x + ε * π x) - ε := by
  have hev : ∀ᶠ ε : ℝ in 𝓝 0, ∀ q ∈ K,
      |energy A (fun x => q x + ε * π x) - energy A q| < δ / 2 := by
    apply hK.eventually_forall_of_forall_eventually
    intro q hq
    have hc : Continuous (fun z : ℝ × (V → ℝ) =>
        |energy A (fun x => z.2 x + z.1 * π x) - energy A z.2|) := by
      apply Continuous.abs
      exact ((continuous_energy A).comp (by fun_prop)).sub
        ((continuous_energy A).comp continuous_snd)
    have he := (hc.continuousAt (x := ((0 : ℝ),q))).eventually_lt_const (show
      |energy A (fun x => q x + (0 : ℝ) * π x) - energy A q| < δ / 2 by
        simpa using half_pos hδ)
    exact he
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hev
  let ε := min r δ / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεr : ε < r := by dsimp [ε]; have := min_le_left r δ; linarith
  have hεδ : ε ≤ δ / 2 := by dsimp [ε]; have := min_le_right r δ; linarith
  have hm : ε ∈ Metric.ball (0 : ℝ) r := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hε] using hεr
  refine ⟨ε,hε,?_⟩
  intro q hq
  have hh := (abs_lt.mp (hball hm q hq)).1
  linarith

end Erdos642.Joint20261019.Energy
