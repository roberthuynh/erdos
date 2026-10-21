import Openmath.Attempt6.PublicBernoulli

namespace Erdos585.Attempt6.BoundedDifferences

open MeasureTheory ProbabilityTheory Real OAI.ErdosGallai.Sampling

universe u

def CoordinateBound {V : Type u} (f : (V → Bool) → ℝ) (c : V → ℝ) : Prop :=
  ∀ i ω η, (∀ j, j ≠ i → ω j = η j) → |f ω - f η| ≤ c i

theorem integral_cube_succ {n : ℕ} (q : unitInterval)
    (f : (Fin (n + 1) → Bool) → ℝ) :
    (∫ ω, f ω ∂sampleMeasure (Fin (n + 1)) q) =
      ∫ x, (∫ b, f (Fin.cons b x) ∂bernoulliMeasure true false q)
        ∂sampleMeasure (Fin n) q := by
  unfold sampleMeasure
  rw [← ((measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => bernoulliMeasure true false q) 0).symm).integral_comp
      (MeasurableEquiv.measurableEmbedding _) f]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove]
  exact integral_prod_symm _ Integrable.of_finite

theorem averaged_coordinateBound {n : ℕ} (q : unitInterval)
    (f : (Fin (n + 1) → Bool) → ℝ) (c : Fin (n + 1) → ℝ)
    (hf : CoordinateBound f c) :
    CoordinateBound
      (fun x => ∫ b, f (Fin.cons b x) ∂bernoulliMeasure true false q)
      (fun i => c i.succ) := by
  intro i x y hxy
  rw [← integral_sub Integrable.of_finite Integrable.of_finite]
  have h : ∀ b, |f (Fin.cons b x) - f (Fin.cons b y)| ≤ c i.succ := by
    intro b
    apply hf i.succ
    intro j
    refine Fin.cases ?_ (fun k hj => ?_) j
    · simp
    · simp only [Fin.cons_succ]
      exact hxy k (fun h => hj (congrArg Fin.succ h))
  have hi := norm_integral_le_of_norm_le_const
    (μ := bernoulliMeasure true false q) (f := fun b => f (Fin.cons b x) - f (Fin.cons b y))
    (C := c i.succ) (ae_of_all _ (fun b => by simpa only [Real.norm_eq_abs] using h b))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hi

theorem coordinate_mgf {n : ℕ} (q : unitInterval)
    (f : (Fin (n + 1) → Bool) → ℝ) (c : Fin (n + 1) → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hf : CoordinateBound f c) (x : Fin n → Bool) (t : ℝ) :
    (∫ b, exp (t * (f (Fin.cons b x) -
      ∫ z, f (Fin.cons z x) ∂bernoulliMeasure true false q))
      ∂bernoulliMeasure true false q) ≤ exp ((c 0) ^ 2 * t ^ 2 / 2) := by
  let a := f (Fin.cons false x)
  have hb : ∀ b, f (Fin.cons b x) ∈ Set.Icc (a - c 0) (a + c 0) := by
    intro b
    have h := hf 0 (Fin.cons b x) (Fin.cons false x) (by
      intro j
      refine Fin.cases ?_ (fun k hj => ?_) j
      · intro hj; exact False.elim (hj rfl)
      · simp)
    exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩
  have hs := hasSubgaussianMGF_of_mem_Icc
    (μ := bernoulliMeasure true false q) (measurable_of_finite _).aemeasurable
    (ae_of_all _ hb)
  have hnorm : (‖(a + c 0) - (a - c 0)‖₊ : ℝ) = 2 * c 0 := by
    simp only [coe_nnnorm, Real.norm_eq_abs]
    rw [show a + c 0 - (a - c 0) = 2 * c 0 by ring,
      abs_of_nonneg (mul_nonneg (by norm_num) (hc 0))]
  simpa only [mgf, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, hnorm,
    mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hs.mgf_le t

/-- Integrating successive coordinates gives the actual centered MGF bound. -/
theorem centered_mgf_fin (n : ℕ) (q : unitInterval)
    (f : (Fin n → Bool) → ℝ) (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hf : CoordinateBound f c) (t : ℝ) :
    (∫ ω, exp (t * (f ω - ∫ η, f η ∂sampleMeasure (Fin n) q))
      ∂sampleMeasure (Fin n) q) ≤ exp ((∑ i, (c i) ^ 2) * t ^ 2 / 2) := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext x
      congr 1
      exact Subsingleton.elim _ _
    obtain ⟨d, hd⟩ : ∃ d : ℝ, f = fun _ => d := ⟨_, he⟩
    rw [hd]
    simp
  | succ n ih =>
    let g : (Fin n → Bool) → ℝ := fun x =>
      ∫ b, f (Fin.cons b x) ∂bernoulliMeasure true false q
    let a : ℝ := ∫ x, g x ∂sampleMeasure (Fin n) q
    have he : (∫ ω, f ω ∂sampleMeasure (Fin (n + 1)) q) = a :=
      integral_cube_succ q f
    have hg := averaged_coordinateBound q f c hf
    have hi := ih g (fun i => c i.succ) (fun i => hc i.succ) hg
    rw [he, integral_cube_succ]
    calc
      _ = ∫ x, exp (t * (g x - a)) *
          (∫ b, exp (t * (f (Fin.cons b x) - g x)) ∂bernoulliMeasure true false q)
          ∂sampleMeasure (Fin n) q := by
        apply integral_congr_ae
        apply ae_of_all
        intro x
        dsimp only
        rw [← integral_const_mul]
        congr 1
        funext b
        rw [← exp_add]
        congr 1
        ring
      _ ≤ ∫ x, exp (t * (g x - a)) * exp ((c 0) ^ 2 * t ^ 2 / 2)
          ∂sampleMeasure (Fin n) q := by
        apply integral_mono Integrable.of_finite Integrable.of_finite
        intro x
        exact mul_le_mul_of_nonneg_left (coordinate_mgf q f c hc hf x t) (exp_pos _).le
      _ = exp ((c 0) ^ 2 * t ^ 2 / 2) *
          (∫ x, exp (t * (g x - a)) ∂sampleMeasure (Fin n) q) := by
        rw [integral_mul_const, mul_comm]
      _ ≤ exp ((c 0) ^ 2 * t ^ 2 / 2) *
          exp ((∑ i : Fin n, (c i.succ) ^ 2) * t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hi (exp_pos _).le
      _ = _ := by
        rw [← exp_add, Fin.sum_univ_succ]
        congr 1
        ring

/-- The centered MGF bound for the actual Bernoulli product on any finite type. -/
theorem centered_mgf {V : Type u} [Fintype V] [DecidableEq V] (q : unitInterval)
    (f : (V → Bool) → ℝ) (c : V → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hf : CoordinateBound f c) (t : ℝ) :
    (∫ ω, exp (t * (f ω - ∫ η, f η ∂sampleMeasure V q))
      ∂sampleMeasure V q) ≤ exp ((∑ i, (c i) ^ 2) * t ^ 2 / 2) := by
  classical
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let g : (Fin (Fintype.card V) → Bool) → ℝ := fun ω => f (fun v => ω (e.symm v))
  let d : Fin (Fintype.card V) → ℝ := fun i => c (e i)
  have hg : CoordinateBound g d := by
    intro i ω η h
    apply hf (e i)
    intro v hv
    apply h (e.symm v)
    intro he
    apply hv
    simpa only [Equiv.apply_symm_apply] using congrArg e he
  have hI (h : (V → Bool) → ℝ) :
      (∫ ω, h (fun v => ω (e.symm v)) ∂sampleMeasure (Fin (Fintype.card V)) q) =
        ∫ ω, h ω ∂sampleMeasure V q := by
    have hp := measurePreserving_piCongrLeft
      (fun _ : V => bernoulliMeasure true false q) e
    have he (ω : Fin (Fintype.card V) → Bool) :
        (MeasurableEquiv.piCongrLeft (fun _ : V => Bool) e) ω =
          fun v => ω (e.symm v) := by
      funext v
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simpa only [sampleMeasure, he] using
      hp.integral_comp (MeasurableEquiv.measurableEmbedding _) h
  have hi := centered_mgf_fin (Fintype.card V) q g d (fun i => hc (e i)) hg t
  dsimp only [g, d] at hi
  rw [hI f, hI (fun ω => exp (t * (f ω - ∫ η, f η ∂sampleMeasure V q)))] at hi
  simpa only [e.sum_comp (fun v => (c v) ^ 2)] using hi

/-- A finite-product bounded-differences lower tail with a fixed weaker constant.
The sum includes zero oscillations, so unused coordinates cost nothing. -/
theorem lower_tail {V : Type u} [Fintype V] [DecidableEq V] (q : unitInterval)
    (f : (V → Bool) → ℝ) (c : V → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hf : CoordinateBound f c) {t : ℝ} (ht : 0 ≤ t) :
    (sampleMeasure V q).real {ω | f ω ≤ (∫ η, f η ∂sampleMeasure V q) - t} ≤
      exp (-t ^ 2 / (2 * ∑ i, (c i) ^ 2)) := by
  classical
  let S : ℝ := ∑ i, (c i) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hzero : S = 0
  · change _ ≤ exp (-t ^ 2 / (2 * S))
    simpa only [hzero, mul_zero, div_zero, exp_zero] using
      (measureReal_le_one (μ := sampleMeasure V q)
        (s := {ω | f ω ≤ (∫ η, f η ∂sampleMeasure V q) - t}))
  have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
  let a : ℝ := ∫ η, f η ∂sampleMeasure V q
  have he : {ω | f ω ≤ a - t} = {ω | f ω - a ≤ -t} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  have hm := measure_le_le_exp_mul_mgf (μ := sampleMeasure V q)
    (X := fun ω => f ω - a) (-t)
    (show -t / S ≤ 0 by exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hS)
    Integrable.of_finite
  have hb := centered_mgf q f c hc hf (-t / S)
  rw [he]
  refine hm.trans ?_
  calc
    _ ≤ exp (-(-t / S) * -t) * exp (S * (-t / S) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hb (exp_pos _).le
    _ = exp (-t ^ 2 / (2 * S)) := by
      rw [← exp_add]
      congr 1
      field_simp
      ring

/-- A lower bound on the actual mean supplies a tail at an explicit threshold. -/
theorem lower_tail_of_mean_ge {V : Type u} [Fintype V] [DecidableEq V]
    (q : unitInterval) (f : (V → Bool) → ℝ) (c : V → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hf : CoordinateBound f c)
    {a t : ℝ} (ht : 0 ≤ t)
    (hmean : a + t ≤ ∫ η, f η ∂sampleMeasure V q) :
    (sampleMeasure V q).real {ω | f ω ≤ a} ≤
      exp (-t ^ 2 / (2 * ∑ i, (c i) ^ 2)) := by
  refine (measureReal_mono (fun ω h => ?_)).trans (lower_tail q f c hc hf ht)
  change f ω ≤ a at h
  change f ω ≤ _
  linarith

/-- The same theorem for functions of the sampled vertex set. -/
theorem finset_lower_tail {V : Type u} [Fintype V] [DecidableEq V]
    (q : unitInterval) (f : Finset V → ℝ) (c : V → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hf : ∀ i A B, (∀ j, j ≠ i → (j ∈ A ↔ j ∈ B)) → |f A - f B| ≤ c i)
    {t : ℝ} (ht : 0 ≤ t) :
    (sampleMeasure V q).real {ω | f (sampleVertices ω) ≤
      (∫ η, f (sampleVertices η) ∂sampleMeasure V q) - t} ≤
      exp (-t ^ 2 / (2 * ∑ i, (c i) ^ 2)) := by
  apply lower_tail q (fun ω => f (sampleVertices ω)) c hc _ ht
  intro i ω η h
  apply hf i
  intro j hj
  simp only [sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and, h j hj]

/-- Row caps on a subset of coordinates give the coverage-tail constant used
by the bipartite reachability branch. -/
theorem lower_tail_row_cap {V : Type u} [Fintype V] [DecidableEq V]
    (q : unitInterval) (f : (V → Bool) → ℝ) (U : Finset V) (cap x : ℝ)
    (hcap : 0 ≤ cap) (hx : 0 ≤ x)
    (hf : CoordinateBound f (fun i => if i ∈ U then cap else 0))
    (hmean : x / 8 ≤ ∫ η, f η ∂sampleMeasure V q) :
    (sampleMeasure V q).real {ω | f ω ≤ x / 16} ≤
      exp (-x ^ 2 / (512 * cap ^ 2 * U.card)) := by
  have hc (i : V) : 0 ≤ if i ∈ U then cap else 0 := by
    split_ifs <;> positivity
  have hm : x / 16 + x / 16 ≤ ∫ η, f η ∂sampleMeasure V q := by linarith
  have ht := lower_tail_of_mean_ge q f (fun i => if i ∈ U then cap else 0) hc hf
    (show 0 ≤ x / 16 by positivity) hm
  have hs : (∑ i : V, (if i ∈ U then cap else 0) ^ 2) = cap ^ 2 * U.card := by
    simp [mul_comm]
  rw [hs] at ht
  convert ht using 1
  congr 1
  ring

end Erdos585.Attempt6.BoundedDifferences
