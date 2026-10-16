import Openmath.Erdos642.Proofs.CampaignFe72210b.ShoreChain
import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphNormalization
import Openmath.Erdos642.Proofs.CampaignFe72210b.ReversibleMoment
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Actual stationary degree weights and square-root similarity on a bipartite shore. -/
namespace Erdos642.CampaignFe72210b
open SimpleGraph Matrix
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (s : Set V) [DecidablePred (· ∈ s)]

omit [DecidableEq V] in
 theorem shore_degree_sum (t : Set V) (hbi : G.IsBipartiteWith s t) :
    (∑ x : s, (G.degree x.val : ℝ)) = (G.edgeFinset.card : ℝ) := by
  classical
  have hn : (∑ x : s, G.degree x.val) = G.edgeFinset.card := by
    calc
      _ = ∑ x ∈ s.toFinset, G.degree x :=
        (Finset.sum_subtype s.toFinset (fun _ => Set.mem_toFinset)
          (fun x => G.degree x)).symm
      _ = _ := G.isBipartiteWith_sum_degrees_eq_card_edges
        (s := s.toFinset) (t := t.toFinset) (by simpa using hbi)
  exact_mod_cast hn

omit [DecidableEq V] in
 theorem shore_edge_pos [Nonempty s] (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) : 0 < (G.edgeFinset.card : ℝ) := by
  rw [← shore_degree_sum G s t hbi]
  exact Finset.sum_pos (fun x _ => by exact_mod_cast hdeg x.val) Finset.univ_nonempty

noncomputable def shoreRoot (x : s) : ℝ :=
  Real.sqrt (G.degree x.val : ℝ) / Real.sqrt (G.edgeFinset.card : ℝ)

 theorem shoreRoot_pos [Nonempty s] (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) (x : s) : 0 < shoreRoot G s x := by
  exact div_pos (degree_sqrt_pos G hdeg x.val)
    (Real.sqrt_pos.2 (shore_edge_pos G s t hbi hdeg))

omit [DecidableEq V] [DecidablePred (· ∈ s)] in
 theorem shoreRoot_sq (x : s) :
    shoreRoot G s x ^ 2 = (G.degree x.val : ℝ) / (G.edgeFinset.card : ℝ) := by
  rw [shoreRoot, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]

omit [DecidableEq V] in
 theorem shoreRoot_normalized [Nonempty s] (t : Set V)
    (hbi : G.IsBipartiteWith s t) (hdeg : ∀ x : V, 0 < G.degree x) :
    (∑ x : s, shoreRoot G s x ^ 2) = 1 := by
  simp_rw [shoreRoot_sq]
  rw [← Finset.sum_div, shore_degree_sum G s t hbi,
    div_self (ne_of_gt (shore_edge_pos G s t hbi hdeg))]

 theorem shore_similarTransition [Nonempty s] (t : Set V)
    (hbi : G.IsBipartiteWith s t) (hdeg : ∀ x : V, 0 < G.degree x) :
    (shoreChain G s t hbi hdeg).similarTransition (shoreRoot G s) =
      (normalizedAdjacency G ^ 2).submatrix Subtype.val Subtype.val := by
  ext x y
  change (shoreRoot G s x * (graphTransition G ^ 2) x.val y.val / shoreRoot G s y) = _
  rw [graphTransition_pow_normalized G hdeg]
  have hx := ne_of_gt (degree_sqrt_pos G hdeg x.val)
  have hy := ne_of_gt (degree_sqrt_pos G hdeg y.val)
  have he := ne_of_gt (Real.sqrt_pos.2 (shore_edge_pos G s t hbi hdeg))
  simp only [shoreRoot, Matrix.submatrix_apply]
  field_simp

omit [DecidablePred (· ∈ s)] in
 theorem shore_normalized_posSemidef :
    ((normalizedAdjacency G ^ 2).submatrix (Subtype.val : s → V) Subtype.val).PosSemidef := by
  have hB := normalizedAdjacency_isHermitian G
  have hp := Matrix.posSemidef_conjTranspose_mul_self (normalizedAdjacency G)
  rw [hB.eq, ← pow_two] at hp
  exact hp.submatrix Subtype.val

 theorem graphTransition_sq_degree_balance (hdeg : ∀ x : V, 0 < G.degree x)
    (x y : V) :
    (G.degree x : ℝ) * (graphTransition G ^ 2) x y =
      (G.degree y : ℝ) * (graphTransition G ^ 2) y x := by
  simp only [pow_two, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  calc
    (G.degree x : ℝ) * (graphTransition G x z * graphTransition G z y) =
        ((G.degree z : ℝ) * graphTransition G z x) * graphTransition G z y := by
      rw [← mul_assoc, graphTransition_degree_balance G hdeg]
    _ = ((G.degree y : ℝ) * graphTransition G y z) * graphTransition G z x := by
      calc
        _ = ((G.degree z : ℝ) * graphTransition G z y) * graphTransition G z x := by ring
        _ = _ := by rw [graphTransition_degree_balance G hdeg]
    _ = _ := by ring

 theorem shore_degree_stationary [Nonempty s] (t : Set V)
    (hbi : G.IsBipartiteWith s t) (hdeg : ∀ x : V, 0 < G.degree x) (y : s) :
    (∑ x : s, ((G.degree x.val : ℝ) / (G.edgeFinset.card : ℝ)) *
      shoreTransition G s x y) = (G.degree y.val : ℝ) / (G.edgeFinset.card : ℝ) := by
  have hb (x : s) : ((G.degree x.val : ℝ) / (G.edgeFinset.card : ℝ)) *
      shoreTransition G s x y = ((G.degree y.val : ℝ) / (G.edgeFinset.card : ℝ)) *
      shoreTransition G s y x := by
    unfold shoreTransition
    have hh := graphTransition_sq_degree_balance G hdeg x.val y.val
    calc
      _ = ((G.degree x.val : ℝ) * (graphTransition G ^ 2) x.val y.val) /
          (G.edgeFinset.card : ℝ) := by ring
      _ = ((G.degree y.val : ℝ) * (graphTransition G ^ 2) y.val x.val) /
          (G.edgeFinset.card : ℝ) := by rw [hh]
      _ = _ := by ring
  simp_rw [hb]
  rw [← Finset.mul_sum, shoreTransition_row_sum G s t hbi hdeg, mul_one]

end Erdos642.CampaignFe72210b
