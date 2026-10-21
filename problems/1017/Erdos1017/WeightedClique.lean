import Erdos1017.WeightMerge

namespace Erdos1017
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_positiveSupport (x : V → ℝ) (hx : ∀ i,0 ≤ x i) :
    (∑ i : positiveSupport x,x i)=∑ i : V,x i := by
  rw [Finset.sum_coe_sort]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have h : ¬ 0 < x i := by simpa [positiveSupport] using hi
  exact le_antisymm (le_of_not_gt h) (hx i)

theorem sum_sq_positiveSupport (x : V → ℝ) (hx : ∀ i,0 ≤ x i) :
    (∑ i : positiveSupport x,(x i)^2)=∑ i : V,(x i)^2 := by
  rw [Finset.sum_coe_sort (positiveSupport x) (fun i => (x i)^2)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have h : ¬ 0 < x i := by simpa [positiveSupport] using hi
  have hz : x i=0 := le_antisymm (le_of_not_gt h) (hx i)
  simp [hz]

theorem clique_support_edge_identity (G : SimpleGraph V) [DecidableRel G.Adj]
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

theorem clique_support_type_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℝ) (hx : ∀ i,0 ≤ x i)
    (hc : G.IsClique (positiveSupport x : Set V)) :
    typeBudget (fun i : positiveSupport x => x i)=graphBudget G x := by
  have he := clique_support_edge_identity G x hx hc
  unfold typeBudget graphBudget
  rw [sum_positiveSupport x hx,sum_sq_positiveSupport x hx]
  have he' := congrArg (fun z : ℝ => (Real.sqrt 7/3)*z) he
  nlinarith

/-- Embed a partition on the positive-weight clique into the unchanged original graph. -/
theorem clique_support_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℝ) (hx : ∀ i,0 ≤ x i)
    (hc : G.IsClique (positiveSupport x : Set V)) :
    ∃ P : WeightedPartition G x,P.cost ≤ graphBudget G x := by
  classical
  let A := positiveSupport x
  let y : A → ℝ := fun i => x i
  have hy : ∀ i,0 < y i := fun i => (Finset.mem_filter.mp i.property).2
  obtain ⟨T,hT⟩ := multipartite_weight_partition y hy
  let C : Finset A → Finset V := fun S => S.image Subtype.val
  have hC (S : Finset A) : G.IsClique (C S : Set V) := by
    intro i hi j hj hij
    obtain ⟨i',_,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j',_,rfl⟩ := Finset.mem_image.mp hj
    exact hc i'.property j'.property hij
  have hm (i : A) (S : Finset A) : (i.val ∈ C S) ↔ i ∈ S := by
    simp [C,Subtype.val_injective]
  have hn (i : V) (hi : i ∉ A) (S : Finset A) : i ∉ C S := by
    intro h
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
    exact hi j.property
  have hl (i j : V) (hij : G.Adj i j) :
      (∑ S : Finset A,if i ∈ C S ∧ j ∈ C S then T.mass S else 0)=x i*x j := by
    by_cases hi : i ∈ A
    · by_cases hj : j ∈ A
      · have ht := T.pair_exact ⟨i,hi⟩ ⟨j,hj⟩ (fun h => hij.ne (congrArg Subtype.val h))
        simpa only [← hm,subsetMoment,Finset.insert_subset_iff,Finset.singleton_subset_iff,y] using ht
      · have hz : x j=0 := by
          have h : ¬ 0 < x j := by simpa [A,positiveSupport] using hj
          exact le_antisymm (le_of_not_gt h) (hx j)
        simp [hn j hj,hz]
    · have hz : x i=0 := by
        have h : ¬ 0 < x i := by simpa [A,positiveSupport] using hi
        exact le_antisymm (le_of_not_gt h) (hx i)
      simp [hn i hi,hz]
  let P : WeightedPartition G x := {
    mass := aggregateMass C T.mass
    nonneg := aggregateMass_nonneg C T.mass T.nonneg
    supported := fun S h => by
      obtain ⟨S',_,hS'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      by_cases hC' : C S'=S
      · simpa only [hC'] using hC S'
      · simp [hC'] at hS'
    edge_load := fun i j hij => by
      have h := aggregate_observable C T.mass (fun S => if i ∈ S ∧ j ∈ S then (1:ℝ) else 0)
      simp only [mul_ite,mul_one,mul_zero] at h
      simpa only [subsetMoment,Finset.insert_subset_iff,Finset.singleton_subset_iff] using h.trans (hl i j hij) }
  have hp : P.cost=T.cost y := by
    have h := aggregate_observable C T.mass (fun _ => (1:ℝ))
    simpa only [WeightedPartition.cost,P,TypePartition.cost,mul_one] using h
  refine ⟨P,hp.trans_le (hT.trans_eq ?_)⟩
  exact clique_support_type_budget G x hx hc

end Erdos1017
