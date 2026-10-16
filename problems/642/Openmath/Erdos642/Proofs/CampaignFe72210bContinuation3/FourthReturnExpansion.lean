import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphEnergy

/-! Unconditional fourth returns of the actual ordinary graph transition. -/
namespace Erdos642.CampaignFe72210bContinuation3.FourthReturnExpansion
open Matrix Erdos642.CampaignFe72210b

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def commonNeighborFinset (v w : V) : Finset V :=
  G.neighborFinset v ∩ G.neighborFinset w

@[simp] theorem mem_commonNeighborFinset (v w x : V) :
    x ∈ commonNeighborFinset G v w ↔ G.Adj v x ∧ G.Adj w x := by
  simp [commonNeighborFinset]

 theorem commonNeighborFinset_card (v w : V) :
    (commonNeighborFinset G v w).card = Fintype.card (G.commonNeighbors v w) := by
  have he : commonNeighborFinset G v w = (G.commonNeighbors v w).toFinset := by
    ext x
    simp only [mem_commonNeighborFinset, Set.mem_toFinset, SimpleGraph.mem_commonNeighbors]
  rw [he, Set.toFinset_card]

 theorem common_neighbor_card_symm (v w : V) :
    Fintype.card (G.commonNeighbors v w) = Fintype.card (G.commonNeighbors w v) := by
  rw [← commonNeighborFinset_card G v w, ← commonNeighborFinset_card G w v]
  simp only [commonNeighborFinset, Finset.inter_comm]

/-- Every surviving two-step term has the original degrees of its departure states. -/
 theorem graphTransition_sq_commonNeighbors (v w : V) :
    (graphTransition G ^ 2) v w =
      ∑ x ∈ commonNeighborFinset G v w,
        1 / ((G.degree v : ℝ) * (G.degree x : ℝ)) := by
  have he : commonNeighborFinset G v w =
      Finset.univ.filter (fun x => G.Adj v x ∧ G.Adj w x) := by
    ext x
    simp
  rw [he, Finset.sum_filter, pow_two, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hvx : G.Adj v x
  · by_cases hxw : G.Adj x w
    · have hwx : G.Adj w x := hxw.symm
      simp only [graphTransition, SimpleGraph.adjMatrix_apply, hvx, hxw, hwx,
        and_self, if_true]
      simp only [one_div, mul_inv]
    · have hwx : ¬G.Adj w x := fun h => hxw h.symm
      simp [graphTransition, SimpleGraph.adjMatrix_apply, hvx, hxw, hwx]
  · simp [graphTransition, SimpleGraph.adjMatrix_apply, hvx]

 theorem graphTransition_sq_nonneg (v w : V) : 0 ≤ (graphTransition G ^ 2) v w := by
  rw [pow_two, Matrix.mul_apply]
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (graphTransition_nonneg G v x) (graphTransition_nonneg G x w)

/-- Original minimum degree bounds every actual common-neighbor denominator. -/
 theorem graphTransition_sq_le_codegree (d : ℝ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ)) (v w : V) :
    (graphTransition G ^ 2) v w ≤ (Fintype.card (G.commonNeighbors v w) : ℝ) / d ^ 2 := by
  rw [graphTransition_sq_commonNeighbors]
  calc
    _ ≤ ∑ x ∈ commonNeighborFinset G v w, (1 : ℝ) / d ^ 2 := by
      apply Finset.sum_le_sum
      intro x _
      have hv : (0 : ℝ) ≤ G.degree v := by positivity
      have hh : d ^ 2 ≤ (G.degree v : ℝ) * (G.degree x : ℝ) := by
        simpa only [pow_two] using mul_le_mul (hmin v) (hmin x) hd.le hv
      exact one_div_le_one_div_of_le (sq_pos_of_pos hd) hh
    _ = _ := by simp [commonNeighborFinset_card, div_eq_mul_inv]

/-- The midpoint-v return is bounded more sharply than the codegree bound. -/
 theorem graphTransition_sq_diag_le (d : ℝ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ)) (v : V) :
    (graphTransition G ^ 2) v v ≤ 1 / d := by
  have hdeg : ∀ x : V, 0 < G.degree x := by
    intro x
    exact_mod_cast lt_of_lt_of_le hd (hmin x)
  rw [pow_two, Matrix.mul_apply]
  calc
    _ ≤ ∑ x, graphTransition G v x * (1 / d) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
        (transition_entry_le G d hd hmin x v) (graphTransition_nonneg G v x)
    _ = (∑ x, graphTransition G v x) * (1 / d) := (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [graphTransition_row_sum G hdeg v, one_mul]

 theorem graphTransition_sq_product_le_codegree (d : ℝ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ)) (v w : V) :
    (graphTransition G ^ 2) v w * (graphTransition G ^ 2) w v ≤
      (Fintype.card (G.commonNeighbors v w) : ℝ) ^ 2 / d ^ 4 := by
  have hv := graphTransition_sq_le_codegree G d hd hmin v w
  have hw := graphTransition_sq_le_codegree G d hd hmin w v
  rw [← common_neighbor_card_symm G v w] at hw
  have hcn : (0 : ℝ) ≤ (Fintype.card (G.commonNeighbors v w) : ℝ) / d ^ 2 := by positivity
  calc
    _ ≤ ((Fintype.card (G.commonNeighbors v w) : ℝ) / d ^ 2) *
        ((Fintype.card (G.commonNeighbors v w) : ℝ) / d ^ 2) :=
      mul_le_mul hv hw (graphTransition_sq_nonneg G w v) hcn
    _ = _ := by field_simp

/-- Exact midpoint split for the actual fourth matrix power, before any bounds. -/
 theorem graphTransition_fourth_midpoint_split (v : V) :
    (graphTransition G ^ 4) v v = (graphTransition G ^ 2) v v ^ 2 +
      ∑ w ∈ Finset.univ.erase v,
        (graphTransition G ^ 2) v w * (graphTransition G ^ 2) w v := by
  have hp : graphTransition G ^ 4 = (graphTransition G ^ 2) * (graphTransition G ^ 2) := by
    rw [← pow_add]
  rw [hp]
  change (∑ w, (graphTransition G ^ 2) v w * (graphTransition G ^ 2) w v) = _
  calc
    _ = (graphTransition G ^ 2) v v * (graphTransition G ^ 2) v v +
        ∑ w ∈ Finset.univ.erase v,
          (graphTransition G ^ 2) v w * (graphTransition G ^ 2) w v :=
      (Finset.add_sum_erase Finset.univ
        (fun w => (graphTransition G ^ 2) v w * (graphTransition G ^ 2) w v)
        (Finset.mem_univ v)).symm
    _ = _ := by ring

/-- Unconditional original-graph fourth-return expansion; no moment or square-sum premise. -/
 theorem graphTransition_fourth_return_le_codegree (d : ℝ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ)) (v : V) :
    (graphTransition G ^ 4) v v ≤ 1 / d ^ 2 +
      (∑ w ∈ Finset.univ.erase v, (Fintype.card (G.commonNeighbors v w) : ℝ) ^ 2) / d ^ 4 := by
  have hdiag : (graphTransition G ^ 2) v v ^ 2 ≤ 1 / d ^ 2 := by
    calc
      _ ≤ ((1 : ℝ) / d) ^ 2 := pow_le_pow_left₀ (graphTransition_sq_nonneg G v v)
        (graphTransition_sq_diag_le G d hd hmin v) 2
      _ = _ := by rw [div_pow]; norm_num
  rw [graphTransition_fourth_midpoint_split]
  calc
    _ ≤ 1 / d ^ 2 + ∑ w ∈ Finset.univ.erase v,
        (Fintype.card (G.commonNeighbors v w) : ℝ) ^ 2 / d ^ 4 :=
      add_le_add hdiag (Finset.sum_le_sum fun w _ =>
        graphTransition_sq_product_le_codegree G d hd hmin v w)
    _ = _ := by rw [Finset.sum_div]

end Erdos642.CampaignFe72210bContinuation3.FourthReturnExpansion
