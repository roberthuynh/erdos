import Erdos1017.DenseWeights
import Mathlib.Data.Finset.Max

namespace Erdos1017.Dense
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem clique_support_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℝ) (hx : ∀ i,0 ≤ x i)
    (hc : G.IsClique (positiveSupport x : Set V)) :
    2*weightedEdges G x=(∑ i,x i)^2-∑ i,(x i)^2 := by
  have ht (i j : V) : (if G.Adj i j then x i*x j else 0)=
      x i*x j-(if i=j then (x i)^2 else 0) := by
    by_cases hij : i=j
    · subst j; simp [pow_two]
    · by_cases ha : G.Adj i j
      · simp [ha,hij]
      · have hz : x i=0 ∨ x j=0 := by
          by_contra hn
          push_neg at hn
          exact ha (hc (by simp [positiveSupport,lt_of_le_of_ne (hx i) (Ne.symm hn.1)])
            (by simp [positiveSupport,lt_of_le_of_ne (hx j) (Ne.symm hn.2)]) hij)
        rcases hz with hi | hj
        · simp [ha,hij,hi]
        · simp [ha,hij,hj]
  unfold weightedEdges
  simp_rw [ht,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true,← Finset.mul_sum,← Finset.sum_mul]
  ring

/-- On a positive-support clique, independent selection at probabilities x_i/a
has pair loads x_i*x_j and total mass a^2, where a is a largest weight. -/
theorem dense_clique_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℝ) (hx : ∀ i,0 ≤ x i)
    (hc : G.IsClique (positiveSupport x : Set V)) :
    ∃ P : WeightedPartition G x,P.cost ≤ graphBudget G x := by
  classical
  by_cases hz : ∀ i,x i=0
  · let P : WeightedPartition G x := {
      mass := fun _ => 0
      nonneg := fun _ => le_rfl
      supported := fun _ h => (h rfl).elim
      edge_load := fun i j _ => by simp [subsetMoment,hz] }
    refine ⟨P,?_⟩
    simp [WeightedPartition.cost,P,graphBudget,weightedEdges,hz]
  · obtain ⟨v,hv⟩ := not_forall.mp hz
    obtain ⟨r,_,hr⟩ := Finset.exists_max_image Finset.univ x ⟨v,Finset.mem_univ v⟩
    have ha : 0 < x r := lt_of_lt_of_le (lt_of_le_of_ne (hx v) (Ne.symm hv)) (hr v (Finset.mem_univ v))
    let a := x r
    let p : V → ℝ := fun i => x i/a
    let C : (V → Bool) → Finset V := fun b => Finset.univ.filter (fun i => b i=true)
    let m : (V → Bool) → ℝ := fun b => a^2*selectorMass p b
    have hp0 (i : V) : 0 ≤ p i := div_nonneg (hx i) ha.le
    have hp1 (i : V) : p i ≤ 1 := (div_le_one ha).mpr (hr i (Finset.mem_univ i))
    have hm (b : V → Bool) : 0 ≤ m b := mul_nonneg (sq_nonneg a) (selectorMass_nonneg p hp0 hp1 b)
    have hmem (i : V) (b : V → Bool) : i ∈ C b ↔ b i=true := by simp [C]
    have hsupport (b : V → Bool) (hb : m b ≠ 0) : G.IsClique (C b : Set V) := by
      have hpos (i : V) (hi : i ∈ C b) : 0 < x i := by
        have hne : x i ≠ 0 := by
          intro hi0
          have hpz : selectorMass p b=0 := by
            apply Finset.prod_eq_zero (Finset.mem_univ i)
            simp [p,hi0,(hmem i b).mp hi]
          exact hb (by simp [m,hpz])
        exact lt_of_le_of_ne (hx i) (Ne.symm hne)
      intro i hi j hj hij
      exact hc (by simp [positiveSupport,hpos i hi]) (by simp [positiveSupport,hpos j hj]) hij
    have hload (i j : V) (hij : G.Adj i j) :
        (∑ b : V → Bool,if i ∈ C b ∧ j ∈ C b then m b else 0)=x i*x j := by
      have hcell (b : V → Bool) :
          (if i ∈ C b ∧ j ∈ C b then m b else 0)=
            a^2*(selectorMass p b*((if b i then 1 else 0)*(if b j then 1 else 0))) := by
        cases hi : b i <;> cases hj : b j <;> simp [m,C,hi,hj]
      simp_rw [hcell]
      rw [← Finset.mul_sum,selector_pair p i j hij.ne]
      dsimp [p,a]
      field_simp
    let P : WeightedPartition G x := {
      mass := aggregateMass C m
      nonneg := aggregateMass_nonneg C m hm
      supported := fun S h => by
        obtain ⟨b,_,hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
        by_cases he : C b=S
        · have hb' : m b ≠ 0 := by simpa [he] using hb
          simpa [he] using hsupport b hb'
        · simp [he] at hb
      edge_load := fun i j hij => by
        have h := aggregate_observable C m (fun S => if i ∈ S ∧ j ∈ S then (1:ℝ) else 0)
        simp only [mul_ite,mul_one,mul_zero] at h
        simpa only [subsetMoment,Finset.insert_subset_iff,Finset.singleton_subset_iff] using h.trans (hload i j hij) }
    have hcost : P.cost=a^2 := by
      have h := aggregate_observable C m (fun _ => (1:ℝ))
      simp only [mul_one] at h
      change (∑ S,aggregateMass C m S)=a^2
      rw [h]
      simp [m,← Finset.mul_sum,selector_total]
    have hsq : a^2 ≤ ∑ i : V,(x i)^2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ r)
    have he := clique_support_edges G x hx hc
    refine ⟨P,?_⟩
    rw [hcost]
    unfold graphBudget
    linarith

/-- A weighted form of the Zykov averaging argument. The graph stays fixed;
each branch transfers weight between two nonadjacent vertices and strictly
decreases positive support. No optimal LP solution or symmetrization axiom is assumed. -/
theorem weighted_graph_dense (G : SimpleGraph V) [DecidableRel G.Adj]
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
      · exact dense_clique_partition G y hy hc
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

/-- Finite universal near-complete line, with exact original-edge loads. -/
theorem near_complete (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P : FractionalPartition G,
      P.cost+2*(G.edgeFinset.card:ℝ) ≤ (Fintype.card V:ℝ)^2 := by
  obtain ⟨P,hP⟩ := weighted_graph_dense G (fun _ => 1) (fun _ => by norm_num)
  obtain ⟨Q,hQ⟩ := WeightedPartition.to_unit_graph G P
  refine ⟨Q,?_⟩
  simp only [graphBudget,weightedEdges_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hP
  linarith

end Erdos1017.Dense
