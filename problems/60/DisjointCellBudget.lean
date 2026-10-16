import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Erdos60.Completion

/-- Actual disjoint-cell aggregate budget. Each cell disjoint from D costs
at least two distinct S-points; each contaminated cell costs a distinct
D-point. No low-vertex witnesses or graph conclusions are assumed. -/
theorem disjoint_cell_budget {I V : Type*} [DecidableEq I] [DecidableEq V]
    (J : Finset I) (C : I → Finset V) (S D : Finset V)
    (hd : (J : Set I).PairwiseDisjoint C)
    (hclean : ∀ i ∈ J, Disjoint (C i) D → 2 ≤ ((C i) ∩ S).card) :
    2 * J.card ≤ S.card + 2 * D.card := by
  classical
  let bad := J.filter (fun i => ¬Disjoint (C i) D)
  let good := J.filter (fun i => Disjoint (C i) D)
  have hex : ∀ i : bad, ∃ x : D, x.val ∈ C i.val := by
    intro i
    have hn := (Finset.mem_filter.mp i.property).2
    obtain ⟨x,hxC,hxD⟩ := by
      simpa only [Finset.disjoint_left,not_forall,not_not] using hn
    exact ⟨⟨x,hxD⟩,hxC⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j heq
    by_contra hne
    have hij : i.val ≠ j.val := fun h => hne (Subtype.ext h)
    have hdis := hd (Finset.mem_filter.mp i.property).1
      (Finset.mem_filter.mp j.property).1 hij
    have hx : (f i).val = (f j).val := congrArg Subtype.val heq
    exact Finset.disjoint_left.mp hdis (hf i) (hx ▸ hf j)
  have hbad : bad.card ≤ D.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj
  have hsub : good.biUnion (fun i => C i ∩ S) ⊆ S := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hxi).2
  have hsum : (∑ i ∈ good, (C i ∩ S).card) ≤ S.card := by
    rw [← Finset.card_biUnion (by
      intro i hi j hj hne
      apply Finset.disjoint_left.mpr
      intro x hxi hxj
      exact Finset.disjoint_left.mp
        (hd (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hne)
        (Finset.mem_inter.mp hxi).1 (Finset.mem_inter.mp hxj).1)]
    exact Finset.card_le_card hsub
  have hl := Finset.sum_le_sum (s := good) (f := fun _ => 2)
    (g := fun i => (C i ∩ S).card) (fun i hi =>
      hclean i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2)
  have hgood : 2 * good.card ≤ S.card := by
    simpa only [Finset.sum_const,smul_eq_mul,Nat.mul_comm] using hl.trans hsum
  have hsplit := Finset.card_filter_add_card_filter_not (s := J) (p := fun i => Disjoint (C i) D)
  change good.card + bad.card = J.card at hsplit
  omega

#print axioms disjoint_cell_budget
end Erdos60.Completion
