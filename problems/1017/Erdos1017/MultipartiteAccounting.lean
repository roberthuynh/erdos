import Erdos1017.LowPartSector

namespace Erdos1017
open scoped BigOperators
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

theorem sum_partSize (part : V → ι) : (∑ i, partSize part i) = Fintype.card V := by
  simp only [partSize, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem sum_partSize_square (part : V → ι) :
    (∑ i, (partSize part i)^2) = ∑ v, partSize part (part v) := by
  calc
    _ = ∑ i : ι, ∑ v : V, if part v = i then partSize part i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Finset.sum_ite, partSize, pow_two]
    _ = ∑ v : V, ∑ i : ι, if part v = i then partSize part i else 0 := Finset.sum_comm
    _ = _ := by simp

theorem multipartite_edge_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (part : V → ι) (hG : ∀ u v, G.Adj u v ↔ part u ≠ part v) :
    2*G.edgeFinset.card + (∑ i, (partSize part i)^2) = (Fintype.card V)^2 := by
  have hd (v : V) : G.degree v + partSize part (part v) = Fintype.card V := by
    have hn : G.neighborFinset v = Finset.univ.filter (fun u => part u ≠ part v) := by
      ext u
      simp [hG, ne_comm]
    rw [← G.card_neighborFinset_eq_degree, hn]
    dsimp [partSize]
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (fun u => part u = part v)
    simpa [add_comm] using hc
  rw [sum_partSize_square, ← G.sum_degrees_eq_twice_card_edges, ← Finset.sum_add_distrib]
  simp [hd, pow_two]

theorem rooted_part_accounting (G : SimpleGraph V) [DecidableRel G.Adj]
    (part : V → Option ι) (hG : ∀ u v, G.Adj u v ↔ part u ≠ part v)
    (ha : 0 < partSize part none) :
    (partSize part none : ℝ) *
      ((∑ i : ι, (partSize part (some i) : ℝ)/partSize part none)+1) = Fintype.card V ∧
    (partSize part none : ℝ)^2 *
      (∑ i : ι, ((partSize part (some i) : ℝ)/partSize part none)^2) =
        ∑ i : ι, (partSize part (some i) : ℝ)^2 ∧
    2*(G.edgeFinset.card : ℝ)+(partSize part none : ℝ)^2+
      (∑ i : ι, (partSize part (some i) : ℝ)^2) = (Fintype.card V : ℝ)^2 := by
  have ha0 : (partSize part none : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hn := sum_partSize part
  rw [Fintype.sum_option] at hn
  have hn' : (partSize part none : ℝ)+(∑ i : ι, (partSize part (some i) : ℝ)) = Fintype.card V := by
    exact_mod_cast hn
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_add, Finset.mul_sum, mul_one]
    have ht : (∑ i : ι, (partSize part none : ℝ)*((partSize part (some i) : ℝ)/partSize part none)) =
        ∑ i : ι, (partSize part (some i) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    rw [ht]
    linarith
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  · have he := multipartite_edge_identity G part hG
    rw [Fintype.sum_option] at he
    have he' : (2:ℝ)*G.edgeFinset.card+((partSize part none : ℝ)^2+
        ∑ i : ι, (partSize part (some i) : ℝ)^2) = (Fintype.card V : ℝ)^2 := by exact_mod_cast he
    linarith

end Erdos1017
