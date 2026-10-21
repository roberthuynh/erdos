import Erdos1017.WeightedClique

namespace Erdos1017
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A weighted form of the Zykov averaging argument. The graph stays fixed;
each branch transfers weight between two nonadjacent vertices and strictly
decreases positive support. No optimal LP solution or symmetrization axiom is assumed. -/
theorem weighted_graph_sharp (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℝ) (hx : ∀ i,0 ≤ x i) :
    ∃ P : WeightedPartition G x,P.cost ≤ graphBudget G x := by
  classical
  have main : ∀ n : ℕ,∀ y : V → ℝ,(∀ i,0 ≤ y i) → (positiveSupport y).card=n →
      ∃ P : WeightedPartition G y,P.cost ≤ graphBudget G y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro y hy hn
      by_cases hc : G.IsClique (positiveSupport y : Set V)
      · exact clique_support_partition G y hy hc
      · change ¬ (∀ i,i ∈ positiveSupport y → ∀ j,j ∈ positiveSupport y → i ≠ j → G.Adj i j) at hc
        push_neg at hc
        obtain ⟨u,hu,v,hv,huv,hnon⟩ := hc
        have hu' : 0 < y u := (Finset.mem_filter.mp hu).2
        have hv' : 0 < y v := (Finset.mem_filter.mp hv).2
        let y₀ := mergeWeight y u v
        let y₁ := mergeWeight y v u
        have hc₀ : (positiveSupport y₀).card < n := by
          rw [← hn]
          exact mergeWeight_card_lt y u v huv hu' hv'
        have hc₁ : (positiveSupport y₁).card < n := by
          rw [← hn]
          exact mergeWeight_card_lt y v u huv.symm hv' hu'
        obtain ⟨P,hP⟩ := ih _ hc₀ y₀ (mergeWeight_nonneg y hy u v) rfl
        obtain ⟨Q,hQ⟩ := ih _ hc₁ y₁ (mergeWeight_nonneg y hy v u) rfl
        let t := y u/(y u+y v)
        let s := y v/(y u+y v)
        have hd : 0 < y u+y v := add_pos hu' hv'
        have ht : 0 ≤ t := div_nonneg hu'.le hd.le
        have hs : 0 ≤ s := div_nonneg hv'.le hd.le
        have hts : t+s=1 := by dsimp [t,s]; rw [← add_div,div_self (ne_of_gt hd)]
        have hp : ∀ i j,G.Adj i j → t*(y₀ i*y₀ j)+s*(y₁ i*y₁ j)=y i*y j :=
          mergeWeight_pair_average G y u v huv hnon hu' hv'
        let R := P.mix Q t s ht hs hp
        refine ⟨R,?_⟩
        calc
          R.cost=t*P.cost+s*Q.cost := WeightedPartition.mix_cost P Q t s ht hs hp
          _ ≤ t*graphBudget G y₀+s*graphBudget G y₁ :=
            add_le_add (mul_le_mul_of_nonneg_left hP ht) (mul_le_mul_of_nonneg_left hQ hs)
          _ = graphBudget G y := graphBudget_average G y y₀ y₁ t s hts
            (mergeWeight_sum y u v huv) (mergeWeight_sum y v u huv.symm) hp
  exact main (positiveSupport x).card x hx rfl

end Erdos1017
