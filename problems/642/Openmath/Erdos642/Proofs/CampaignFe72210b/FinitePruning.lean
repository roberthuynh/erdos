import Mathlib

/-! Finite induced-graph pruning by maximizing the actual edge potential. -/
namespace Erdos642.CampaignFe72210b

open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
private theorem edgeCard_of_graph_eq {K L : SimpleGraph V}
    [Fintype K.edgeSet] [Fintype L.edgeSet] (h : K = L) :
    K.edgeFinset.card = L.edgeFinset.card := by
  rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
  exact @Fintype.card_congr _ _ _ _
    (Equiv.cast (congrArg (fun H : SimpleGraph V => ↥H.edgeSet) h))

omit [Fintype V] [DecidableEq V] in
private theorem degree_of_graph_eq {K L : SimpleGraph V} (h : K = L) (x : V)
    [Fintype (K.neighborSet x)] [Fintype (L.neighborSet x)] :
    K.degree x = L.degree x := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact @Fintype.card_congr _ _ _ _
    (Equiv.cast (congrArg (fun H : SimpleGraph V => ↥(H.neighborSet x)) h))

/-- The actual induced graph on W, with the other ambient vertices isolated. -/
def mask (W : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ W ∧ y ∈ W
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro x h; exact G.irrefl h.1⟩

instance maskDecidableRel (W : Finset V) : DecidableRel (mask G W).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x y ∧ x ∈ W ∧ y ∈ W))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem mask_le (W : Finset V) : mask G W ≤ G := fun _ _ h => h.1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem mask_support_subset (W : Finset V) : (mask G W).support ⊆ (W : Set V) := by
  rintro x ⟨y, h⟩
  exact h.2.1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem mask_induce (W : Finset V) :
    (mask G W).induce (W : Set V) = G.induce (W : Set V) := by
  ext x y
  change (G.Adj x.val y.val ∧ x.val ∈ W ∧ y.val ∈ W) ↔ G.Adj x.val y.val
  exact ⟨fun h => h.1, fun h => ⟨h, x.property, y.property⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem mask_empty : mask G ∅ = ⊥ := by
  ext x y
  simp [mask]

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem mask_univ : mask G Finset.univ = G := by
  ext x y
  simp [mask]

/-- An actual unordered edge count, on a fixed ambient vertex type. -/
def inducedEdges (W : Finset V) : ℕ := (mask G W).edgeFinset.card

attribute [-instance] FinsetCoe.fintype in
theorem inducedEdges_eq_induce (W : Finset V) :
    inducedEdges G W = (G.induce (W : Set V)).edgeFinset.card := by
  have h := (mask G W).card_edgeFinset_induce_of_support_subset
    (mask_support_subset G W)
  change (mask G W).edgeFinset.card = _
  apply Eq.trans h.symm
  rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
  exact @Fintype.card_congr _ _ _ _
    (Equiv.cast (congrArg (fun H : SimpleGraph (W : Set V) => ↥H.edgeSet) (mask_induce G W)))

attribute [-instance] FinsetCoe.fintype in
theorem mask_degree_eq_induce (W : Finset V) (x : (W : Set V)) :
    (mask G W).degree x.val = (G.induce (W : Set V)).degree x := by
  have h := (mask G W).degree_induce_of_support_subset (mask_support_subset G W) x
  apply Eq.trans h.symm
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact @Fintype.card_congr _ _ _ _
    (Equiv.cast (congrArg (fun H : SimpleGraph (W : Set V) => ↥(H.neighborSet x))
      (mask_induce G W)))

theorem mask_degree_le (W : Finset V) (x : V) :
    (mask G W).degree x ≤ G.degree x :=
  SimpleGraph.degree_le_of_le (mask_le G W)

omit [Fintype V] [DecidableRel G.Adj] in
theorem mask_erase (W : Finset V) (x : V) :
    mask G (W.erase x) = (mask G W).deleteIncidenceSet x := by
  ext y z
  simp only [mask, deleteIncidenceSet_adj, Finset.mem_erase]
  tauto

/-- Deleting a vertex loses exactly its current degree, in additive natural form. -/
theorem inducedEdges_erase_add_degree (W : Finset V) (x : V) :
    inducedEdges G (W.erase x) + (mask G W).degree x = inducedEdges G W := by
  unfold inducedEdges
  have h := (mask G W).card_edgeFinset_deleteIncidenceSet x
  have hdeg := (mask G W).degree_le_card_edgeFinset (v := x)
  have hadd := Nat.sub_add_cancel hdeg
  rw [← h] at hadd
  have heq := @edgeCard_of_graph_eq V _ _ _ _ (mask_erase G W x)
  omega

/-- The real potential has no integer rounding of its degree threshold. -/
def pruningPotential (a : ℝ) (W : Finset V) : ℝ :=
  (inducedEdges G W : ℝ) - a * (W.card : ℝ)

theorem pruningPotential_erase (a : ℝ) (W : Finset V) (x : V) (hx : x ∈ W) :
    pruningPotential G a (W.erase x) = pruningPotential G a W + a -
      ((mask G W).degree x : ℝ) := by
  have he := inducedEdges_erase_add_degree G W x
  have hv := Finset.card_erase_add_one hx
  have he' : (inducedEdges G (W.erase x) : ℝ) + ((mask G W).degree x : ℝ) =
      (inducedEdges G W : ℝ) := by exact_mod_cast he
  have hv' : ((W.erase x).card : ℝ) + 1 = (W.card : ℝ) := by exact_mod_cast hv
  unfold pruningPotential
  rw [← he', ← hv']
  ring

attribute [-instance] FinsetCoe.fintype in
/-- Positive initial potential yields a nonempty actual induced graph above the threshold. -/
theorem exists_induced_min_degree_preserving_potential (W0 : Finset V) (a : ℝ)
    (ha : 0 ≤ a) (hpos : 0 < pruningPotential G a W0) :
    ∃ W : Finset V,
      W ⊆ W0 ∧ W.Nonempty ∧
      pruningPotential G a W0 ≤ pruningPotential G a W ∧
      (∀ x : (W : Set V), a ≤ ((G.induce (W : Set V)).degree x : ℝ)) ∧
      pruningPotential G a W0 ≤ ((G.induce (W : Set V)).edgeFinset.card : ℝ) := by
  classical
  obtain ⟨W, hW, hmax⟩ := Finset.exists_max_image W0.powerset
    (pruningPotential G a) (Finset.powerset_nonempty W0)
  have hsub : W ⊆ W0 := Finset.mem_powerset.mp hW
  have hpot := hmax W0 (Finset.mem_powerset_self W0)
  have hne : W.Nonempty := by
    by_contra h
    have hzero : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hempty : pruningPotential G a W = 0 := by
      rw [hzero]
      simp [pruningPotential, inducedEdges, mask_empty]
    linarith
  have hdeg : ∀ x : (W : Set V), a ≤ ((G.induce (W : Set V)).degree x : ℝ) := by
    intro x
    have herase := hmax (W.erase x.val)
      (Finset.mem_powerset.mpr ((Finset.erase_subset x.val W).trans hsub))
    rw [pruningPotential_erase G a W x.val x.property] at herase
    rw [← mask_degree_eq_induce G W x]
    linarith
  refine ⟨W, hsub, hne, hpot, hdeg, ?_⟩
  rw [← inducedEdges_eq_induce G W]
  have hc : 0 ≤ a * (W.card : ℝ) := mul_nonneg ha (Nat.cast_nonneg _)
  unfold pruningPotential at hpot ⊢
  linarith

/-- Removing any finite forbidden set costs at most its original degree sum. -/
theorem inducedEdges_delete_charge (W U : Finset V) :
    inducedEdges G W ≤ inducedEdges G (W \ U) + ∑ x ∈ U, G.degree x := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert x U hx ih =>
    rw [Finset.sdiff_insert, Finset.sum_insert hx]
    have he := inducedEdges_erase_add_degree G (W \ U) x
    have hd := mask_degree_le G (W \ U) x
    omega

/-- The root-deletion charge uses actual edges of the original graph. -/
theorem card_edges_delete_charge (U : Finset V) :
    G.edgeFinset.card ≤ inducedEdges G (Finset.univ \ U) + ∑ x ∈ U, G.degree x := by
  have h := inducedEdges_delete_charge G Finset.univ U
  have heq := @edgeCard_of_graph_eq V _ _ _ _ (mask_univ G)
  unfold inducedEdges at h ⊢
  omega

end Erdos642.CampaignFe72210b
