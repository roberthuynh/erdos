import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.FiniteCoarea
import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphEigenvectors

/-! Literal adjacency weights and normalized graph Dirichlet identities. -/
namespace Erdos642.CampaignFe72210bContinuation3.GraphDirichlet
open Matrix Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.FiniteCoarea
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem energy_eq_normSq_sub_correlation (w : V → V → ℝ)
    (hsym : ∀ x y, w x y = w y x) (f : V → ℝ) :
    energy w f = normSq w f - ∑ x, ∑ y, w x y * f x * f y := by
  have hfirst : (∑ x, ∑ y, w x y * f x ^ 2) = normSq w f := by
    simp [normSq, mass, FiniteCoarea.row, Finset.sum_mul]
  have hsecond : (∑ x, ∑ y, w x y * f y ^ 2) = normSq w f := by
    rw [Finset.sum_comm]
    apply Eq.trans _ hfirst
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hsym y x]
  have ht (x y : V) : w x y * (f x - f y) ^ 2 =
      w x y * f x ^ 2 + w x y * f y ^ 2 - 2 * (w x y * f x * f y) := by ring
  unfold energy
  simp_rw [ht, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hfirst, hsecond]
  ring

omit [DecidableEq V] in
theorem correlation_abs_le_normSq (w : V → V → ℝ) (hw : ∀ x y, 0 ≤ w x y)
    (hsym : ∀ x y, w x y = w y x) (f : V → ℝ) :
    |∑ x, ∑ y, w x y * f x * f y| ≤ normSq w f := by
  have hfirst : (∑ x, ∑ y, w x y * f x ^ 2) = normSq w f := by
    simp [normSq, mass, FiniteCoarea.row, Finset.sum_mul]
  have hsecond : (∑ x, ∑ y, w x y * f y ^ 2) = normSq w f := by
    rw [Finset.sum_comm]
    apply Eq.trans _ hfirst
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hsym y x]
  have ht (x y : V) : |w x y * f x * f y| ≤
      (1 / 2 : ℝ) * (w x y * f x ^ 2 + w x y * f y ^ 2) := by
    have ha : 2 * |f x| * |f y| ≤ f x ^ 2 + f y ^ 2 := by
      nlinarith [sq_nonneg (|f x| - |f y|), sq_abs (f x), sq_abs (f y)]
    have hh := mul_le_mul_of_nonneg_left ha (hw x y)
    rw [abs_mul, abs_mul, abs_of_nonneg (hw x y)]
    nlinarith only [hh]
  calc
    _ ≤ ∑ x, |∑ y, w x y * f x * f y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, |w x y * f x * f y| :=
      Finset.sum_le_sum (fun x _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ x, ∑ y, (1 / 2 : ℝ) * (w x y * f x ^ 2 + w x y * f y ^ 2) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ht x y))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
      rw [hfirst, hsecond]
      ring

variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable def adjWeight (x y : V) : ℝ := G.adjMatrix ℝ x y
noncomputable def normalizedFunction (z : V → ℝ) (x : V) : ℝ := z x / degreeRoot G x

omit [Fintype V] [DecidableEq V] in
theorem adjWeight_nonneg (x y : V) : 0 ≤ adjWeight G x y := by
  simp only [adjWeight, SimpleGraph.adjMatrix_apply]
  split_ifs <;> norm_num
omit [Fintype V] [DecidableEq V] in
theorem adjWeight_symmetric (x y : V) : adjWeight G x y = adjWeight G y x := by
  simp [adjWeight, SimpleGraph.adjMatrix_apply, G.adj_comm]
omit [DecidableEq V] in
@[simp] theorem adjWeight_row (x : V) : FiniteCoarea.row (adjWeight G) x = (G.degree x : ℝ) := by
  simpa [FiniteCoarea.row, adjWeight, Matrix.mulVec, dotProduct] using
    G.adjMatrix_mulVec_const_apply (a := (1 : ℝ)) (v := x)

omit [DecidableEq V] in
@[simp] theorem adjWeight_total : (∑ x, FiniteCoarea.row (adjWeight G) x) = degreeVolume G := by
  simp [degreeVolume]

omit [DecidableEq V] in
theorem adjWeight_total_pos [Nonempty V] (hdeg : ∀ x : V, 0 < G.degree x) :
    0 < ∑ x, FiniteCoarea.row (adjWeight G) x := by
  rw [adjWeight_total]
  exact degreeVolume_positive G hdeg

theorem normalizedFunction_norm (hdeg : ∀ x : V, 0 < G.degree x) (z : V → ℝ) :
    normSq (adjWeight G) (normalizedFunction G z) = dotProduct z z := by
  unfold normSq mass
  simp only [adjWeight_row, normalizedFunction, dotProduct]
  apply Finset.sum_congr rfl
  intro x _
  have hx : degreeRoot G x ≠ 0 := ne_of_gt (degreeRoot_positive G hdeg x)
  rw [← degreeRoot_sq G x]
  field_simp

theorem normalizedFunction_mean (hdeg : ∀ x : V, 0 < G.degree x) (z : V → ℝ) :
    mass (adjWeight G) (normalizedFunction G z) = dotProduct z (degreeRoot G) := by
  unfold mass
  simp only [adjWeight_row, normalizedFunction, dotProduct]
  apply Finset.sum_congr rfl
  intro x _
  have hx : degreeRoot G x ≠ 0 := ne_of_gt (degreeRoot_positive G hdeg x)
  rw [← degreeRoot_sq G x]
  field_simp

theorem normalizedFunction_correlation (hdeg : ∀ x : V, 0 < G.degree x) (z : V → ℝ) :
    (∑ x, ∑ y, adjWeight G x y * normalizedFunction G z x * normalizedFunction G z y) =
      dotProduct z (normalizedAdjacency G *ᵥ z) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  unfold adjWeight normalizedFunction normalizedAdjacency degreeRoot
  have hx := ne_of_gt (degree_sqrt_pos G hdeg x)
  have hy := ne_of_gt (degree_sqrt_pos G hdeg y)
  field_simp

theorem normalized_dirichlet (hdeg : ∀ x : V, 0 < G.degree x) (z : V → ℝ) :
    energy (adjWeight G) (normalizedFunction G z) =
      dotProduct z z - dotProduct z (normalizedAdjacency G *ᵥ z) := by
  rw [energy_eq_normSq_sub_correlation _ (adjWeight_symmetric G),
    normalizedFunction_norm G hdeg, normalizedFunction_correlation G hdeg]

theorem normalized_quadratic_abs_le (hdeg : ∀ x : V, 0 < G.degree x) (z : V → ℝ) :
    |dotProduct z (normalizedAdjacency G *ᵥ z)| ≤ dotProduct z z := by
  rw [← normalizedFunction_correlation G hdeg, ← normalizedFunction_norm G hdeg]
  exact correlation_abs_le_normSq _ (adjWeight_nonneg G) (adjWeight_symmetric G) _

end Erdos642.CampaignFe72210bContinuation3.GraphDirichlet
