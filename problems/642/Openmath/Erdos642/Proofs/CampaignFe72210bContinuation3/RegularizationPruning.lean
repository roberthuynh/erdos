import Openmath.Erdos642.Proofs.CampaignFe72210b.FinitePruning

/-! Actual induced pruning from a nonnegative edge potential, including initial potential zero. -/
namespace Erdos642.CampaignFe72210bContinuation3.RegularizationPruning

open Erdos642.CampaignFe72210b

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

attribute [-instance] FinsetCoe.fintype in
/-- Nonnegative actual potential pays the literal induced average-degree bound. -/
theorem average_le_of_nonnegative_potential (W : Finset V) (hW : W.Nonempty)
    (a : ℝ) (hpot : 0 ≤ pruningPotential G a W) :
    2 * a ≤ 2 * ((G.induce (W : Set V)).edgeFinset.card : ℝ) / (W.card : ℝ) := by
  have hc : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
  have he : a * (W.card : ℝ) ≤
      ((G.induce (W : Set V)).edgeFinset.card : ℝ) := by
    unfold pruningPotential at hpot
    rw [inducedEdges_eq_induce] at hpot
    linarith
  apply (le_div_iff₀ hc).2
  nlinarith

attribute [-instance] FinsetCoe.fintype in
/-- A zero initial potential is allowed; a bad deletion creates the positive-potential input. -/
theorem exists_induced_min_degree_nonnegative_potential
    (W0 : Finset V) (hW0 : W0.Nonempty) (a : ℝ) (ha : 0 ≤ a)
    (hpot : 0 ≤ pruningPotential G a W0) :
    ∃ W : Finset V,
      W ⊆ W0 ∧ W.Nonempty ∧
      pruningPotential G a W0 ≤ pruningPotential G a W ∧
      (∀ x : (W : Set V), a ≤ ((G.induce (W : Set V)).degree x : ℝ)) ∧
      2 * a ≤ 2 * ((G.induce (W : Set V)).edgeFinset.card : ℝ) / (W.card : ℝ) := by
  classical
  by_cases hgood : ∀ x : (W0 : Set V),
      a ≤ ((G.induce (W0 : Set V)).degree x : ℝ)
  · exact ⟨W0, Finset.Subset.refl W0, hW0, le_rfl, hgood,
      average_le_of_nonnegative_potential G W0 hW0 a hpot⟩
  · push Not at hgood
    obtain ⟨x, hx⟩ := hgood
    have hbad : ((mask G W0).degree x.val : ℝ) < a := by
      rw [mask_degree_eq_induce G W0 x]
      exact hx
    have hpositive : 0 < pruningPotential G a (W0.erase x.val) := by
      rw [pruningPotential_erase G a W0 x.val x.property]
      linarith
    obtain ⟨W, hsub, hne, hretain, hdeg, _⟩ :=
      exists_induced_min_degree_preserving_potential G (W0.erase x.val) a ha hpositive
    have hstep : pruningPotential G a W0 ≤ pruningPotential G a (W0.erase x.val) := by
      rw [pruningPotential_erase G a W0 x.val x.property]
      linarith
    have hfinal : pruningPotential G a W0 ≤ pruningPotential G a W :=
      hstep.trans hretain
    refine ⟨W, hsub.trans (Finset.erase_subset x.val W0), hne, hfinal, hdeg, ?_⟩
    exact average_le_of_nonnegative_potential G W hne a (hpot.trans hfinal)

attribute [-instance] FinsetCoe.fintype in
/-- Pruning at half the actual original average starts at potential exactly zero. -/
theorem exists_induced_min_degree_half_average
    (W0 : Finset V) (hW0 : W0.Nonempty) :
    ∃ W : Finset V,
      W ⊆ W0 ∧ W.Nonempty ∧
      (∀ x : (W : Set V),
        ((G.induce (W0 : Set V)).edgeFinset.card : ℝ) / (W0.card : ℝ) ≤
          ((G.induce (W : Set V)).degree x : ℝ)) ∧
      2 * ((G.induce (W0 : Set V)).edgeFinset.card : ℝ) / (W0.card : ℝ) ≤
        2 * ((G.induce (W : Set V)).edgeFinset.card : ℝ) / (W.card : ℝ) := by
  classical
  let a : ℝ := ((G.induce (W0 : Set V)).edgeFinset.card : ℝ) / (W0.card : ℝ)
  have hc : (W0.card : ℝ) ≠ 0 := by exact_mod_cast hW0.card_pos.ne'
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpot : 0 ≤ pruningPotential G a W0 := by
    unfold pruningPotential
    rw [inducedEdges_eq_induce]
    dsimp [a]
    simp only [div_mul_cancel₀ _ hc, sub_self, le_refl]
  obtain ⟨W, hsub, hne, _, hdeg, havg⟩ :=
    exists_induced_min_degree_nonnegative_potential G W0 hW0 a ha hpot
  refine ⟨W, hsub, hne, hdeg, ?_⟩
  simpa only [a, mul_div_assoc] using havg

end Erdos642.CampaignFe72210bContinuation3.RegularizationPruning
