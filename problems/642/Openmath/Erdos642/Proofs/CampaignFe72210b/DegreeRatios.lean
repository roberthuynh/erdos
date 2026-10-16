import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphEigenvectors

/-! Actual finite graph degree-volume and projector normalization estimates. -/

namespace Erdos642.CampaignFe72210b

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Summing the actual lower degree bound controls the actual degree volume. -/
theorem degreeVolume_lower_bound (d : ℝ)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ)) :
    (Fintype.card V : ℝ) * d ≤ degreeVolume G := by
  classical
  calc
    (Fintype.card V : ℝ) * d = ∑ _x : V, d := by simp
    _ ≤ degreeVolume G := Finset.sum_le_sum fun x _ => hmin x

section Nonempty

variable [Nonempty V]

/-- The stationary degree mass is at most the degree ratio divided by order. -/
theorem degree_mass_le (d R : ℝ) (hd : 0 < d) (hR : 1 ≤ R)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ R * d) (y : V) :
    (G.degree y : ℝ) / degreeVolume G ≤ R / (Fintype.card V : ℝ) := by
  have hdeg : ∀ x : V, 0 < G.degree x := by
    intro x
    exact_mod_cast lt_of_lt_of_le hd (hmin x)
  have hv : 0 < degreeVolume G := degreeVolume_positive G hdeg
  have hn : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  apply (div_le_div_iff₀ hv hn).2
  calc
    (G.degree y : ℝ) * (Fintype.card V : ℝ) ≤
        (R * d) * (Fintype.card V : ℝ) :=
      mul_le_mul_of_nonneg_right (hmax y) hn.le
    _ = R * ((Fintype.card V : ℝ) * d) := by ring
    _ ≤ R * degreeVolume G :=
      mul_le_mul_of_nonneg_left (degreeVolume_lower_bound G d hmin) hR0

omit [Nonempty V] in
/-- The similarity factor is controlled by the actual graph degree bounds. -/
theorem degree_sqrt_ratio_le (d R : ℝ) (hd : 0 < d) (hR : 1 ≤ R)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ R * d) (x y : V) :
    Real.sqrt (G.degree y : ℝ) / Real.sqrt (G.degree x : ℝ) ≤ Real.sqrt R := by
  have hx : 0 < (G.degree x : ℝ) := lt_of_lt_of_le hd (hmin x)
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hratio : (G.degree y : ℝ) / (G.degree x : ℝ) ≤ R := by
    apply (div_le_iff₀ hx).2
    exact (hmax y).trans (mul_le_mul_of_nonneg_left (hmin x) hR0)
  rw [← Real.sqrt_div (by positivity : 0 ≤ (G.degree y : ℝ))]
  exact Real.sqrt_le_sqrt hratio

/-- Genuine transition similarity sends the positive root projector to degree mass. -/
theorem degree_root_projector_similarity (hdeg : ∀ x : V, 0 < G.degree x)
    (x y : V) :
    (Real.sqrt (G.degree y : ℝ) / Real.sqrt (G.degree x : ℝ)) *
        unitDegreeRoot G x * unitDegreeRoot G y =
      (G.degree y : ℝ) / degreeVolume G := by
  have hv : 0 < degreeVolume G := degreeVolume_positive G hdeg
  have hx : 0 < Real.sqrt (G.degree x : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hdeg x)
  have hr : 0 < Real.sqrt (degreeVolume G) := Real.sqrt_pos.2 hv
  have hxnz : Real.sqrt (G.degree x : ℝ) ≠ 0 := ne_of_gt hx
  have hrnz : Real.sqrt (degreeVolume G) ≠ 0 := ne_of_gt hr
  calc
    _ = Real.sqrt (G.degree y : ℝ) ^ 2 / Real.sqrt (degreeVolume G) ^ 2 := by
      unfold unitDegreeRoot degreeRoot
      field_simp
    _ = (G.degree y : ℝ) / degreeVolume G := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ (G.degree y : ℝ)), Real.sq_sqrt hv.le]

/-- The signed root projector has exactly the two endpoint sign factors. -/
theorem signed_degree_root_projector_similarity (hdeg : ∀ x : V, 0 < G.degree x)
    (σ : V → ℝ) (x y : V) :
    (Real.sqrt (G.degree y : ℝ) / Real.sqrt (G.degree x : ℝ)) *
        signedUnitDegreeRoot G σ x * signedUnitDegreeRoot G σ y =
      (σ x * σ y) * ((G.degree y : ℝ) / degreeVolume G) := by
  unfold signedUnitDegreeRoot
  calc
    _ = (σ x * σ y) *
        ((Real.sqrt (G.degree y : ℝ) / Real.sqrt (G.degree x : ℝ)) *
          unitDegreeRoot G x * unitDegreeRoot G y) := by ring
    _ = _ := by rw [degree_root_projector_similarity G hdeg x y]

end Nonempty

end Erdos642.CampaignFe72210b
