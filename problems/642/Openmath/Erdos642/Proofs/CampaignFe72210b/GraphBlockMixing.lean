import Openmath.Erdos642.Proofs.CampaignFe72210b.HeatKernel

/-! Actual graph power rows, columns, and a logarithmic block mixing bound. -/

namespace Erdos642.CampaignFe72210b

open Matrix

/-- Natural powers of the spectral remainder are bounded by a real exponential,
including the endpoint `γ = 1` and power zero. -/
theorem gap_power_le_exp (γ : ℝ) (hγone : γ ≤ 1) (n : ℕ) :
    (1 - γ) ^ n ≤ Real.exp (-(γ * (n : ℝ))) := by
  have hbase : 1 - γ ≤ Real.exp (-γ) := by linarith [Real.add_one_le_exp (-γ)]
  calc
    (1 - γ) ^ n ≤ Real.exp (-γ) ^ n :=
      pow_le_pow_left₀ (sub_nonneg.mpr hγone) hbase n
    _ = Real.exp (-(γ * (n : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem gap_power_le_inv_order (γ : ℝ) (hγone : γ ≤ 1) (N : ℝ) (hN : 0 < N)
    (n : ℕ) (hlog : Real.log N ≤ γ * (n : ℝ)) :
    (1 - γ) ^ n ≤ 1 / N := by
  calc
    (1 - γ) ^ n ≤ Real.exp (-(γ * (n : ℝ))) := gap_power_le_exp γ hγone n
    _ ≤ Real.exp (-Real.log N) := Real.exp_le_exp.mpr (neg_le_neg hlog)
    _ = 1 / N := by rw [Real.exp_neg, Real.exp_log hN]; simp only [one_div]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Actual finite path endpoint marginals make every transition power nonnegative. -/
theorem graphTransition_pow_nonneg (hdeg : ∀ x : V, 0 < G.degree x)
    (t : ℕ) (x y : V) : 0 ≤ (graphTransition G ^ t) x y := by
  classical
  let C := graphChain G hdeg
  calc
    0 ≤ C.eventMass t (fun z p => C.endpoint z p = y) x := C.eventMass_nonneg _ _ _
    _ = (graphTransition G ^ t) x y := by
      unfold Erdos642.FiniteMarkov.Chain.eventMass
      calc
        _ = ∑ p : Erdos642.FiniteMarkov.Path V t,
            if C.endpoint x p = y then C.weight x p else 0 := by
          apply Finset.sum_congr rfl
          intro p _
          by_cases hp : C.endpoint x p = y <;> simp [hp]
        _ = (graphTransition G ^ t) x y := C.endpoint_marginal t x y

/-- Every actual transition power has row sum one. -/
theorem graphTransition_pow_row_sum (hdeg : ∀ x : V, 0 < G.degree x)
    (t : ℕ) (x : V) : (∑ y, (graphTransition G ^ t) x y) = 1 := by
  induction t with
  | zero => simp [Matrix.one_apply]
  | succ t ih =>
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, graphTransition_row_sum G hdeg, mul_one]
    exact ih

/-- Genuine degree detailed balance propagates to every matrix power. -/
theorem graphTransition_pow_degree_balance (hdeg : ∀ x : V, 0 < G.degree x)
    (t : ℕ) (x y : V) :
    (G.degree x : ℝ) * (graphTransition G ^ t) x y =
      (G.degree y : ℝ) * (graphTransition G ^ t) y x := by
  induction t generalizing x y with
  | zero =>
    by_cases hxy : x = y
    · subst y
      rfl
    · simp [hxy, Ne.symm hxy]
  | succ t ih =>
    conv_lhs => rw [pow_succ, Matrix.mul_apply, Finset.mul_sum]
    conv_rhs => rw [pow_succ', Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    calc
      (G.degree x : ℝ) * ((graphTransition G ^ t) x z * graphTransition G z y) =
          ((G.degree x : ℝ) * (graphTransition G ^ t) x z) * graphTransition G z y := by ring
      _ = ((G.degree z : ℝ) * (graphTransition G ^ t) z x) * graphTransition G z y := by
        rw [ih x z]
      _ = (graphTransition G ^ t) z x * ((G.degree z : ℝ) * graphTransition G z y) := by ring
      _ = (graphTransition G ^ t) z x * ((G.degree y : ℝ) * graphTransition G y z) := by
        rw [graphTransition_degree_balance G hdeg z y]
      _ = (G.degree y : ℝ) * (graphTransition G y z * (graphTransition G ^ t) z x) := by ring

/-- Actual degree ratio and reversibility bound every power column sum. -/
theorem graphTransition_pow_column_sum_le (hdeg : ∀ x : V, 0 < G.degree x)
    (d R : ℝ) (hd : 0 < d) (hR : 1 ≤ R)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ R * d)
    (t : ℕ) (a : V) : (∑ v, (graphTransition G ^ t) v a) ≤ R := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hpoint (v : V) : (graphTransition G ^ t) v a ≤ R * (graphTransition G ^ t) a v := by
    have hv : 0 < (G.degree v : ℝ) := lt_of_lt_of_le hd (hmin v)
    have hr : (G.degree a : ℝ) / (G.degree v : ℝ) ≤ R := by
      apply (div_le_iff₀ hv).2
      exact (hmax a).trans (mul_le_mul_of_nonneg_left (hmin v) hR0)
    have hb := graphTransition_pow_degree_balance G hdeg t v a
    calc
      (graphTransition G ^ t) v a =
          ((G.degree a : ℝ) / (G.degree v : ℝ)) * (graphTransition G ^ t) a v := by
        apply (mul_left_cancel₀ (ne_of_gt hv))
        field_simp
        nlinarith [hb]
      _ ≤ R * (graphTransition G ^ t) a v :=
        mul_le_mul_of_nonneg_right hr (graphTransition_pow_nonneg G hdeg t a v)
  calc
    (∑ v, (graphTransition G ^ t) v a) ≤ ∑ v, R * (graphTransition G ^ t) a v :=
      Finset.sum_le_sum fun v _ => hpoint v
    _ = R := by rw [← Finset.mul_sum, graphTransition_pow_row_sum G hdeg, mul_one]

section Nonempty

variable [Nonempty V]

/-- The actual ordinary graph walk satisfies the block pointwise premise at
the stated logarithmic block length, with no assumed mixing inequality. -/
theorem graphTransition_block_mixing (γ d R : ℝ)
    (hgap : HasBipartiteSpectralGap G γ) (hbip : G.IsBipartite)
    (hd1 : 1 ≤ d) (hR : 1 ≤ R)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ R * d)
    (k : ℕ) (hklog : (2 : ℝ) + Real.log (Fintype.card V : ℝ) / γ ≤ (k : ℝ))
    (x y : V) :
    (graphTransition G ^ k) x y ≤ (2 * R + Real.sqrt R) / (Fintype.card V : ℝ) := by
  have hγ : 0 < γ := hgap.1
  have hγone : γ ≤ 1 := hgap.2.1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have hN : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hN1 : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast (show 1 ≤ Fintype.card V by have := Fintype.card_pos (α := V); omega)
  have hlognonneg : 0 ≤ Real.log (Fintype.card V : ℝ) := Real.log_nonneg hN1
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by
    have := div_nonneg hlognonneg hγ.le
    linarith
  have hk : 2 ≤ k := by exact_mod_cast hkreal
  have hcast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
    rw [Nat.cast_sub hk]
    norm_num
  have hlog : Real.log (Fintype.card V : ℝ) ≤ γ * ((k - 2 : ℕ) : ℝ) := by
    rw [hcast]
    have hdiv : Real.log (Fintype.card V : ℝ) / γ ≤ (k : ℝ) - 2 := by linarith
    have := (div_le_iff₀ hγ).mp hdiv
    nlinarith
  have hpower : (1 - γ) ^ (k - 2) ≤ 1 / (Fintype.card V : ℝ) :=
    gap_power_le_inv_order γ hγone _ hN (k - 2) hlog
  have hfrac : (1 - γ) ^ (k - 2) / d ≤ 1 / (Fintype.card V : ℝ) := by
    apply le_trans _ hpower
    simpa only [div_one] using div_le_div_of_nonneg_left
      (pow_nonneg (sub_nonneg.mpr hγone) (k - 2)) zero_lt_one hd1
  have hscaled : Real.sqrt R * (1 - γ) ^ (k - 2) / d ≤
      Real.sqrt R / (Fintype.card V : ℝ) := by
    calc
      _ = Real.sqrt R * ((1 - γ) ^ (k - 2) / d) := by ring
      _ ≤ Real.sqrt R * (1 / (Fintype.card V : ℝ)) :=
        mul_le_mul_of_nonneg_left hfrac (Real.sqrt_nonneg _)
      _ = Real.sqrt R / (Fintype.card V : ℝ) := by ring
  calc
    (graphTransition G ^ k) x y ≤
        2 * R / (Fintype.card V : ℝ) + Real.sqrt R * (1 - γ) ^ (k - 2) / d :=
      graphTransition_pow_heatKernel G γ d R hgap hbip hd hR hmin hmax k hk x y
    _ ≤ 2 * R / (Fintype.card V : ℝ) + Real.sqrt R / (Fintype.card V : ℝ) :=
      add_le_add le_rfl hscaled
    _ = (2 * R + Real.sqrt R) / (Fintype.card V : ℝ) := by ring

end Nonempty

end Erdos642.CampaignFe72210b
