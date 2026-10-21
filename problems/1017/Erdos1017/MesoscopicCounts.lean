import Erdos1017.MesoscopicGraph

namespace Erdos1017.Mesoscopic
open scoped BigOperators

theorem sum_off_diagonal_ite (s : ℕ) (k : ℝ) :
    (∑ i : Fin s, ∑ j : Fin s, if i=j then 0 else if i=j then 0 else k) =
      (∑ i : Fin s, ∑ j : Fin s, if i ≠ j then k else 0) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i=j <;> simp [h]

theorem sum_off_diagonal (s : ℕ) (k : ℝ) :
    (∑ i : Fin s, ∑ j : Fin s, if i ≠ j then k else 0) = (s:ℝ)*(s-1)*k := by
  have he (i j : Fin s) : (if i ≠ j then k else 0) = k - if i=j then k else 0 := by
    by_cases h : i=j <;> simp [h]
  simp_rw [he, Finset.sum_sub_distrib]
  simp
  ring

theorem sum_neutral {b : ℕ} (T : Finset (Fin 2 × Fin b)) (k : ℝ) :
    (∑ d : Fin 2, ∑ j : Fin b, if (d,j) ∈ T then k else 0) = (T.card:ℝ)*k := by
  rw [← Fintype.sum_prod_type (fun p : Fin 2 × Fin b => if p ∈ T then k else 0)]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun p : Fin 2 × Fin b => p ∈ T) = T := by ext; simp
  rw [hf]
  simp

theorem sum_neutral_rev {b : ℕ} (T : Finset (Fin 2 × Fin b)) (k : ℝ) :
    (∑ j : Fin b, ∑ d : Fin 2, if (d,j) ∈ T then k else 0) = (T.card:ℝ)*k := by
  rw [Finset.sum_comm]
  exact sum_neutral T k

theorem graph_order (a b s : ℕ) : Fintype.card (Vertex a b s)=a+b+s+2 := by
  simp [Vertex, add_assoc]

theorem graph_edge_count (a b s : ℕ) (T : Finset (Fin 2 × Fin b)) :
    ((graph a b s T).edgeFinset.card : ℝ) =
      (a:ℝ)*b + (a+b)*s + s*(s-1)/2 + 2*(a+s) + T.card := by
  let G := graph a b s T
  have hd : (∑ u, ∑ v, if G.Adj u v then (1:ℝ) else 0)=2*(G.edgeFinset.card:ℝ) := by
    have hrow (u : Vertex a b s) :
        (∑ v, if G.Adj u v then (1:ℝ) else 0)=(G.degree u:ℝ) := by
      rw [← G.card_neighborFinset_eq_degree]
      simp [← SimpleGraph.mem_neighborFinset]
    simp_rw [hrow]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have he : (∑ u, ∑ v, if G.Adj u v then (1:ℝ) else 0)=
      2*((a:ℝ)*b + (a+b)*s + s*(s-1)/2 + 2*(a+s) + T.card) := by
    simp only [Fintype.sum_sum_type, Finset.sum_add_distrib]
    norm_num only [G, graph, color, allowed, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, ne_eq, not_false_eq_true, not_true_eq_false,
      and_true, and_false, true_and, false_and, or_true, true_or, false_or, or_false,
      if_true, if_false, (show (0 : Fin 4) ≠ 1 from by decide), (show (0 : Fin 4) ≠ 2 from by decide), (show (0 : Fin 4) ≠ 3 from by decide), (show (1 : Fin 4) ≠ 0 from by decide), (show (1 : Fin 4) ≠ 2 from by decide), (show (1 : Fin 4) ≠ 3 from by decide), (show (2 : Fin 4) ≠ 0 from by decide), (show (2 : Fin 4) ≠ 1 from by decide), (show (2 : Fin 4) ≠ 3 from by decide), (show (3 : Fin 4) ≠ 0 from by decide), (show (3 : Fin 4) ≠ 1 from by decide), (show (3 : Fin 4) ≠ 2 from by decide)]
    simp only [sum_off_diagonal, sum_neutral, sum_neutral_rev,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  linarith

theorem graph_weight_total (a b s : ℕ) (T : Finset (Fin 2 × Fin b)) :
    total (graph a b s T) weight =
      (a:ℝ)*b + (2:ℝ)/3*(a-b)*s - (1:ℝ)/6*s*(s-1) +
        2*a - T.card - (4:ℝ)/3*s := by
  unfold total
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib]
  norm_num only [graph, color, allowed, weight, coefficient,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, ne_eq, not_false_eq_true, not_true_eq_false,
    and_true, and_false, true_and, false_and, or_true, true_or, false_or, or_false,
    if_true, if_false, ite_not, ite_self, (show (0 : Fin 4) ≠ 1 from by decide), (show (0 : Fin 4) ≠ 2 from by decide), (show (0 : Fin 4) ≠ 3 from by decide), (show (1 : Fin 4) ≠ 0 from by decide), (show (1 : Fin 4) ≠ 2 from by decide), (show (1 : Fin 4) ≠ 3 from by decide), (show (2 : Fin 4) ≠ 0 from by decide), (show (2 : Fin 4) ≠ 1 from by decide), (show (2 : Fin 4) ≠ 3 from by decide), (show (3 : Fin 4) ≠ 0 from by decide), (show (3 : Fin 4) ≠ 1 from by decide), (show (3 : Fin 4) ≠ 2 from by decide)]
  simp only [sum_off_diagonal_ite, sum_off_diagonal, sum_neutral, sum_neutral_rev,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Choosing any prescribed number of the two special vertices' possible
B-neighbors changes the original edge count by exactly that number. -/
theorem neutral_choice (b t : ℕ) (ht : t ≤ 2*b) :
    ∃ T : Finset (Fin 2 × Fin b), T.card=t := by
  have hc : t ≤ (Finset.univ : Finset (Fin 2 × Fin b)).card := by simpa using ht
  obtain ⟨T, _, hT⟩ := Finset.exists_subset_card_eq hc
  exact ⟨T,hT⟩

end Erdos1017.Mesoscopic
