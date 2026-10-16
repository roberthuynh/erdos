import Openmath.Erdos642.Proofs.CampaignFe72210b.ShoreNormalization
import Openmath.Erdos642.Proofs.CampaignFe72210b.TiltedOperator

namespace Erdos642.CampaignFe72210b
open SimpleGraph Matrix
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
 theorem graph_edge_upper (d : ℝ) (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100 * d) :
    (G.edgeFinset.card : ℝ) ≤ 50 * d * (Fintype.card V : ℝ) := by
  have he : (∑ x : V, (G.degree x : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hmax x)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  nlinarith

variable (s : Set V) [DecidablePred (· ∈ s)] [Nonempty s]

omit [DecidableEq V] in
 theorem shoreRoot_sq_lower (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) (d : ℝ) (_hd : 0 < d)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100 * d) (x : s) :
    1 / (50 * (Fintype.card V : ℝ)) ≤ shoreRoot G s x ^ 2 := by
  have : Nonempty V := ⟨(Classical.choice (inferInstance : Nonempty s)).val⟩
  have hN : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have he := shore_edge_pos G s t hbi hdeg
  rw [shoreRoot_sq]
  apply (div_le_div_iff₀ (by positivity : 0 < 50 * (Fintype.card V : ℝ)) he).2
  have hu := graph_edge_upper G d hmax
  have hl := mul_le_mul_of_nonneg_right (hmin x.val) hN.le
  nlinarith

 theorem shoreRoot_prefactor_upper (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) (d : ℝ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100 * d) (x : s) :
    2 / shoreRoot G s x ^ 2 ≤ 100 * (Fintype.card V : ℝ) := by
  have : Nonempty V := ⟨x.val⟩
  have hN : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hp := shoreRoot_sq_lower G s t hbi hdeg d hd hmin hmax x
  have hh : 1 ≤ shoreRoot G s x ^ 2 * (50 * (Fintype.card V : ℝ)) :=
    (div_le_iff₀ (by positivity : 0 < 50 * (Fintype.card V : ℝ))).mp hp
  apply (div_le_iff₀ (sq_pos_of_pos (shoreRoot_pos G s t hbi hdeg x))).2
  nlinarith

 theorem shore_mass_lower (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) (d : ℝ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x : V, (G.degree x : ℝ) ≤ 100 * d) (S : Finset s) :
    (S.card : ℝ) / (50 * (Fintype.card V : ℝ)) ≤
      Erdos642.TiltedOperator.mass S (shoreRoot G s) := by
  have hm : Erdos642.TiltedOperator.mass S (shoreRoot G s) =
      ∑ x ∈ S, shoreRoot G s x ^ 2 := by
    simp [Erdos642.TiltedOperator.mass]
  rw [hm]
  calc
    _ = ∑ _x ∈ S, 1 / (50 * (Fintype.card V : ℝ)) := by simp; ring
    _ ≤ _ := Finset.sum_le_sum fun x _ => shoreRoot_sq_lower G s t hbi hdeg d hd hmin hmax x

end Erdos642.CampaignFe72210b
