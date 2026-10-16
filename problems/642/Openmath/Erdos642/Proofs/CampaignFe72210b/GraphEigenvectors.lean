import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphNormalization

/-! Actual positive and signed degree-root eigenvectors of normalized adjacency. -/
namespace Erdos642.CampaignFe72210b

open SimpleGraph Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def degreeRoot (x : V) : ℝ := Real.sqrt (G.degree x : ℝ)
noncomputable def degreeVolume : ℝ := ∑ x : V, (G.degree x : ℝ)
noncomputable def unitDegreeRoot (x : V) : ℝ := degreeRoot G x / Real.sqrt (degreeVolume G)
noncomputable def signedUnitDegreeRoot (σ : V → ℝ) (x : V) : ℝ := σ x * unitDegreeRoot G x

omit [DecidableEq V] in
theorem degreeRoot_sq (x : V) : degreeRoot G x ^ 2 = (G.degree x : ℝ) :=
  Real.sq_sqrt (by positivity)

 theorem degreeRoot_positive (hdeg : ∀ x : V, 0 < G.degree x) (x : V) :
    0 < degreeRoot G x := degree_sqrt_pos G hdeg x

omit [DecidableEq V] in
theorem degreeVolume_positive [Nonempty V] (hdeg : ∀ x : V, 0 < G.degree x) :
    0 < degreeVolume G := by
  apply Finset.sum_pos
  · intro x _
    exact_mod_cast hdeg x
  · exact Finset.univ_nonempty

 theorem unitDegreeRoot_positive [Nonempty V] (hdeg : ∀ x : V, 0 < G.degree x)
    (x : V) : 0 < unitDegreeRoot G x :=
  div_pos (degreeRoot_positive G hdeg x)
    (Real.sqrt_pos.2 (degreeVolume_positive G hdeg))

omit [DecidableEq V] in
theorem unitDegreeRoot_sum_sq [Nonempty V] (hdeg : ∀ x : V, 0 < G.degree x) :
    (∑ x : V, unitDegreeRoot G x ^ 2) = 1 := by
  have hv := degreeVolume_positive G hdeg
  have hr : Real.sqrt (degreeVolume G) ^ 2 = degreeVolume G := Real.sq_sqrt (le_of_lt hv)
  simp only [unitDegreeRoot, div_pow, degreeRoot_sq, hr]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hv)

/-- The graph transition similarity and genuine row sums give the positive eigenvector. -/
 theorem normalizedAdjacency_degreeRoot (hdeg : ∀ x : V, 0 < G.degree x) :
    normalizedAdjacency G *ᵥ degreeRoot G = degreeRoot G := by
  funext x
  have hx := ne_of_gt (degreeRoot_positive G hdeg x)
  have he (y : V) : normalizedAdjacency G x y * degreeRoot G y =
      degreeRoot G x * graphTransition G x y := by
    rw [graphTransition_normalized G hdeg]
    change normalizedAdjacency G x y * degreeRoot G y =
      degreeRoot G x * (degreeRoot G y / degreeRoot G x * normalizedAdjacency G x y)
    field_simp
  change (∑ y, normalizedAdjacency G x y * degreeRoot G y) = degreeRoot G x
  simp_rw [he]
  rw [← Finset.mul_sum, graphTransition_row_sum G hdeg, mul_one]

 theorem normalizedAdjacency_unitDegreeRoot (hdeg : ∀ x : V, 0 < G.degree x) :
    normalizedAdjacency G *ᵥ unitDegreeRoot G = unitDegreeRoot G := by
  funext x
  have he := congrFun (normalizedAdjacency_degreeRoot G hdeg) x
  change (∑ y, normalizedAdjacency G x y *
    (degreeRoot G y / Real.sqrt (degreeVolume G))) =
      degreeRoot G x / Real.sqrt (degreeVolume G)
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  exact congrArg (fun z : ℝ => z / Real.sqrt (degreeVolume G)) he

omit [DecidableEq V] in
theorem signedUnitDegreeRoot_sum_sq [Nonempty V]
    (hdeg : ∀ x : V, 0 < G.degree x) (σ : V → ℝ) (hσ : ∀ x, σ x ^ 2 = 1) :
    (∑ x : V, signedUnitDegreeRoot G σ x ^ 2) = 1 := by
  simp only [signedUnitDegreeRoot, mul_pow, hσ, one_mul]
  exact unitDegreeRoot_sum_sq G hdeg

/-- The sign-flip assumption is only about actual adjacent pairs. -/
 theorem normalizedAdjacency_signedUnitDegreeRoot (hdeg : ∀ x : V, 0 < G.degree x)
    (σ : V → ℝ) (hflip : ∀ x y, G.Adj x y → σ y = -σ x) :
    normalizedAdjacency G *ᵥ signedUnitDegreeRoot G σ = -signedUnitDegreeRoot G σ := by
  funext x
  have he (y : V) : normalizedAdjacency G x y * signedUnitDegreeRoot G σ y =
      (-σ x) * (normalizedAdjacency G x y * unitDegreeRoot G y) := by
    by_cases hxy : G.Adj x y
    · simp only [signedUnitDegreeRoot, hflip x y hxy]
      ring
    · simp [normalizedAdjacency, SimpleGraph.adjMatrix_apply, hxy]
  change (∑ y, normalizedAdjacency G x y * signedUnitDegreeRoot G σ y) =
    -(signedUnitDegreeRoot G σ x)
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hu := congrFun (normalizedAdjacency_unitDegreeRoot G hdeg) x
  change (-σ x) * ((normalizedAdjacency G *ᵥ unitDegreeRoot G) x) = _
  rw [hu]
  simp [signedUnitDegreeRoot]

omit [DecidableEq V] in
theorem unitDegreeRoot_euclidean_norm [Nonempty V] (hdeg : ∀ x : V, 0 < G.degree x) :
    ‖(WithLp.toLp 2 (unitDegreeRoot G) : EuclideanSpace ℝ V)‖ = 1 := by
  have hs : ‖(WithLp.toLp 2 (unitDegreeRoot G) : EuclideanSpace ℝ V)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact unitDegreeRoot_sum_sq G hdeg
  nlinarith [norm_nonneg (WithLp.toLp 2 (unitDegreeRoot G) : EuclideanSpace ℝ V)]

omit [DecidableEq V] in
theorem signedUnitDegreeRoot_euclidean_norm [Nonempty V]
    (hdeg : ∀ x : V, 0 < G.degree x) (σ : V → ℝ) (hσ : ∀ x, σ x ^ 2 = 1) :
    ‖(WithLp.toLp 2 (signedUnitDegreeRoot G σ) : EuclideanSpace ℝ V)‖ = 1 := by
  have hs : ‖(WithLp.toLp 2 (signedUnitDegreeRoot G σ) : EuclideanSpace ℝ V)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact signedUnitDegreeRoot_sum_sq G hdeg σ hσ
  nlinarith [norm_nonneg (WithLp.toLp 2 (signedUnitDegreeRoot G σ) : EuclideanSpace ℝ V)]

end Erdos642.CampaignFe72210b
