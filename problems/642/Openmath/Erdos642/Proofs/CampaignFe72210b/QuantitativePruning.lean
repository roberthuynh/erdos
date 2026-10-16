import Openmath.Erdos642.Proofs.CampaignFe72210b.FinitePruning

/-! Quantitative actual root deletion, pruning, and bipartite shore counting. -/
namespace Erdos642.CampaignFe72210b

open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- Original pointwise minimum degree gives the actual edge density. -/
theorem card_edges_lower_of_min_degree (d : ℕ) (hmin : ∀ x : V, d ≤ G.degree x) :
    (Fintype.card V : ℝ) * (d : ℝ) / 2 ≤ (G.edgeFinset.card : ℝ) := by
  have hsum : Fintype.card V * d ≤ ∑ x : V, G.degree x := by
    calc
      _ = ∑ _x : V, d := by simp
      _ ≤ _ := Finset.sum_le_sum (fun x _ => hmin x)
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  have hsum' : (Fintype.card V : ℝ) * (d : ℝ) ≤ 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hsum
  linarith

/-- The allowed-set potential is bounded below by actual density minus the root charge. -/
theorem pruningPotential_compl_lower (U : Finset V) (d D : ℕ)
    (hmin : ∀ x : V, d ≤ G.degree x) (hmax : ∀ x : V, G.degree x ≤ D) :
    (Fintype.card V : ℝ) * (d : ℝ) / 4 - (U.card : ℝ) * (D : ℝ) ≤
      pruningPotential G ((d : ℝ) / 4) (Finset.univ \ U) := by
  have hdensity := card_edges_lower_of_min_degree G d hmin
  have hcharge := card_edges_delete_charge G U
  have hsum : (∑ x ∈ U, G.degree x) ≤ U.card * D := by
    calc
      _ ≤ ∑ _x ∈ U, D := Finset.sum_le_sum (fun x _ => hmax x)
      _ = _ := by simp
  have hcharge' : (G.edgeFinset.card : ℝ) ≤
      (inducedEdges G (Finset.univ \ U) : ℝ) + (U.card : ℝ) * (D : ℝ) := by
    exact_mod_cast (hcharge.trans (Nat.add_le_add_left hsum _))
  have hcardNat : (Finset.univ \ U).card ≤ Fintype.card V := by
    simpa only [Finset.card_univ] using Finset.card_le_card (Finset.sdiff_subset
      (s := Finset.univ) (t := U))
  have hcard : ((Finset.univ \ U).card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast hcardNat
  have hproduct := mul_le_mul_of_nonneg_left hcard
    (div_nonneg (Nat.cast_nonneg d) (by norm_num : (0 : ℝ) ≤ 4))
  unfold pruningPotential
  nlinarith

attribute [-instance] FinsetCoe.fintype in
/-- Positive retained budget supplies a genuine nonempty induced graph avoiding all roots. -/
theorem exists_quantitative_pruning (U : Finset V) (d D : ℕ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ G.degree x) (hmax : ∀ x : V, G.degree x ≤ D)
    (hpos : 0 < (Fintype.card V : ℝ) * (d : ℝ) / 4 - (U.card : ℝ) * (D : ℝ)) :
    ∃ W : Finset V,
      W ⊆ Finset.univ \ U ∧ W.Nonempty ∧
      (∀ x : (W : Set V), (d : ℝ) / 4 ≤ ((G.induce (W : Set V)).degree x : ℝ)) ∧
      (Fintype.card V : ℝ) * (d : ℝ) / 4 - (U.card : ℝ) * (D : ℝ) ≤
        ((G.induce (W : Set V)).edgeFinset.card : ℝ) ∧
      (∀ x : (W : Set V), (G.induce (W : Set V)).degree x ≤ D) ∧
      (∀ x ∈ W, (d : ℝ) / 4 ≤ ((mask G W).degree x : ℝ)) := by
  have hinitial := pruningPotential_compl_lower G U d D hmin hmax
  have hdreal : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have ha : 0 ≤ (d : ℝ) / 4 := le_of_lt (div_pos hdreal (by norm_num))
  have hpositive : 0 < pruningPotential G ((d : ℝ) / 4) (Finset.univ \ U) :=
    hpos.trans_le hinitial
  obtain ⟨W, hsub, hne, _hpot, hdegree, hedge⟩ :=
    exists_induced_min_degree_preserving_potential G (Finset.univ \ U) ((d : ℝ) / 4) ha hpositive
  refine ⟨W, hsub, hne, hdegree, hinitial.trans hedge, ?_, ?_⟩
  · intro x
    rw [← mask_degree_eq_induce G W x]
    exact (mask_degree_le G W x.val).trans (hmax x.val)
  · intro x hx
    have h := hdegree ⟨x, hx⟩
    rw [← mask_degree_eq_induce G W ⟨x, hx⟩] at h
    exact h

omit [Fintype V] [DecidableRel G.Adj] in
/-- Actual mask edges cross exactly the intersected original shores. -/
theorem mask_isBipartiteWith (W A B : Finset V)
    (hbi : G.IsBipartiteWith (A : Set V) (B : Set V)) :
    (mask G W).IsBipartiteWith (↑(A ∩ W) : Set V) (↑(B ∩ W) : Set V) where
  disjoint := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact Set.disjoint_left.mp hbi.disjoint
      (Finset.mem_inter.mp hxA).1 (Finset.mem_inter.mp hxB).1
  mem_of_adj := by
    intro x y h
    rcases hbi.mem_of_adj h.1 with hAB | hBA
    · exact Or.inl ⟨Finset.mem_inter.mpr ⟨hAB.1, h.2.1⟩,
        Finset.mem_inter.mpr ⟨hAB.2, h.2.2⟩⟩
    · exact Or.inr ⟨Finset.mem_inter.mpr ⟨hBA.1, h.2.1⟩,
        Finset.mem_inter.mpr ⟨hBA.2, h.2.2⟩⟩

/-- The exact left-shore degree sum counts each literal masked edge once. -/
theorem inducedEdges_eq_sum_shore_degrees (W A B : Finset V)
    (hbi : G.IsBipartiteWith (A : Set V) (B : Set V)) :
    inducedEdges G W = ∑ x ∈ A ∩ W, (mask G W).degree x := by
  exact (SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges
    (mask_isBipartiteWith G W A B hbi)).symm

/-- Upper degrees give a direct actual left-shore cardinal bound on edges. -/
theorem inducedEdges_le_shore_card_mul (W A B : Finset V)
    (hbi : G.IsBipartiteWith (A : Set V) (B : Set V))
    (D : ℕ) (hmax : ∀ x : V, G.degree x ≤ D) :
    inducedEdges G W ≤ (A ∩ W).card * D := by
  rw [inducedEdges_eq_sum_shore_degrees G W A B hbi]
  calc
    _ ≤ ∑ _x ∈ A ∩ W, D := Finset.sum_le_sum
      (fun x _ => (mask_degree_le G W x).trans (hmax x))
    _ = _ := by simp

attribute [-instance] FinsetCoe.fintype in
/-- One actual pruned bipartite mask carries both the budget and direct shore-size bound. -/
theorem exists_quantitative_bipartite_pruning (U A B : Finset V) (d D : ℕ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ G.degree x) (hmax : ∀ x : V, G.degree x ≤ D)
    (hbi : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hpos : 0 < (Fintype.card V : ℝ) * (d : ℝ) / 4 - (U.card : ℝ) * (D : ℝ)) :
    ∃ W : Finset V,
      W ⊆ Finset.univ \ U ∧ W.Nonempty ∧
      (∀ x ∈ W, (d : ℝ) / 4 ≤ ((mask G W).degree x : ℝ)) ∧
      (∀ x : V, (mask G W).degree x ≤ D) ∧
      (Fintype.card V : ℝ) * (d : ℝ) / 4 - (U.card : ℝ) * (D : ℝ) ≤
        (inducedEdges G W : ℝ) ∧
      (mask G W).IsBipartiteWith (↑(A ∩ W) : Set V) (↑(B ∩ W) : Set V) ∧
      (Fintype.card V : ℝ) * (d : ℝ) / 4 - (U.card : ℝ) * (D : ℝ) ≤
        ((A ∩ W).card : ℝ) * (D : ℝ) := by
  obtain ⟨W, hsub, hne, _hdegree, hedge, _hupper, hmask⟩ :=
    exists_quantitative_pruning G U d D hd hmin hmax hpos
  rw [← inducedEdges_eq_induce G W] at hedge
  have hshore : (inducedEdges G W : ℝ) ≤ ((A ∩ W).card : ℝ) * (D : ℝ) := by
    exact_mod_cast inducedEdges_le_shore_card_mul G W A B hbi D hmax
  exact ⟨W, hsub, hne, hmask,
    fun x => (mask_degree_le G W x).trans (hmax x), hedge,
    mask_isBipartiteWith G W A B hbi, hedge.trans hshore⟩

end Erdos642.CampaignFe72210b
