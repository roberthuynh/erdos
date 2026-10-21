import Erdos1017.MultipartiteWeights

namespace Erdos1017
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Product edge demands on a fixed graph. Small clique masses may be discarded. -/
structure WeightedPartition (G : SimpleGraph V) (x : V → ℝ) where
  mass : Finset V → ℝ
  nonneg : ∀ S, 0 ≤ mass S
  supported : ∀ S, mass S ≠ 0 → G.IsClique (S : Set V)
  edge_load : ∀ i j, G.Adj i j → subsetMoment mass {i,j}=x i*x j

noncomputable def WeightedPartition.cost {G : SimpleGraph V} {x : V → ℝ}
    (P : WeightedPartition G x) : ℝ := ∑ S,P.mass S

noncomputable def weightedEdges (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) : ℝ :=
  (∑ i,∑ j,if G.Adj i j then x i*x j else 0)/2

noncomputable def graphBudget (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) : ℝ :=
  (1+Real.sqrt 7/3)*(∑ i,x i)^2/4-(Real.sqrt 7/3)*weightedEdges G x

noncomputable def WeightedPartition.mix {G : SimpleGraph V} {x y z : V → ℝ}
    (P : WeightedPartition G y) (Q : WeightedPartition G z) (t s : ℝ)
    (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hp : ∀ i j,G.Adj i j → t*(y i*y j)+s*(z i*z j)=x i*x j) :
    WeightedPartition G x where
  mass S := t*P.mass S+s*Q.mass S
  nonneg S := add_nonneg (mul_nonneg ht (P.nonneg S)) (mul_nonneg hs (Q.nonneg S))
  supported S h := by
    by_cases hP : P.mass S=0
    · apply Q.supported S
      intro hQ
      simp [hP,hQ] at h
    · exact P.supported S hP
  edge_load i j hij := by
    rw [subsetMoment_add,subsetMoment_mul,subsetMoment_mul,P.edge_load i j hij,Q.edge_load i j hij]
    exact hp i j hij

theorem WeightedPartition.mix_cost {G : SimpleGraph V} {x y z : V → ℝ}
    (P : WeightedPartition G y) (Q : WeightedPartition G z) (t s : ℝ)
    (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hp : ∀ i j,G.Adj i j → t*(y i*y j)+s*(z i*z j)=x i*x j) :
    (P.mix Q t s ht hs hp).cost=t*P.cost+s*Q.cost := by
  simp [WeightedPartition.cost,WeightedPartition.mix,Finset.sum_add_distrib,Finset.mul_sum]

theorem weightedEdges_average (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y z : V → ℝ) (t s : ℝ)
    (hp : ∀ i j,G.Adj i j → t*(y i*y j)+s*(z i*z j)=x i*x j) :
    t*weightedEdges G y+s*weightedEdges G z=weightedEdges G x := by
  have he : t*(∑ i,∑ j,if G.Adj i j then y i*y j else 0)+
      s*(∑ i,∑ j,if G.Adj i j then z i*z j else 0)=
      ∑ i,∑ j,if G.Adj i j then x i*x j else 0 := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : G.Adj i j
    · simpa only [if_pos h] using hp i j h
    · simp [h]
  unfold weightedEdges
  linarith

theorem graphBudget_average (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y z : V → ℝ) (t s : ℝ) (hts : t+s=1)
    (hy : (∑ i,y i)=∑ i,x i) (hz : (∑ i,z i)=∑ i,x i)
    (hp : ∀ i j,G.Adj i j → t*(y i*y j)+s*(z i*z j)=x i*x j) :
    t*graphBudget G y+s*graphBudget G z=graphBudget G x := by
  have he := weightedEdges_average G x y z t s hp
  unfold graphBudget
  rw [hy,hz]
  calc
    _ = (t+s)*((1+Real.sqrt 7/3)*(∑ i,x i)^2/4)-
        (Real.sqrt 7/3)*(t*weightedEdges G y+s*weightedEdges G z) := by ring
    _ = _ := by rw [hts,he,one_mul]

theorem weightedEdges_one (G : SimpleGraph V) [DecidableRel G.Adj] :
    weightedEdges G (fun _ => 1)=(G.edgeFinset.card : ℝ) := by
  have hi (i : V) : (∑ j : V, if G.Adj i j then (1:ℝ) else 0)=G.degree i := by
    rw [← G.card_neighborFinset_eq_degree]
    simp [← SimpleGraph.mem_neighborFinset]
  have hd : (∑ i : V,(G.degree i : ℝ))=2*(G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  unfold weightedEdges
  simp only [one_mul,hi]
  linarith

theorem WeightedPartition.to_unit_graph (G : SimpleGraph V)
    (P : WeightedPartition G (fun _ => 1)) :
    ∃ Q : FractionalPartition G,Q.cost ≤ P.cost := by
  let Q := partitionOfCliqueLaw G id (pruneMass id P.mass)
    (fun S => by dsimp [pruneMass]; split_ifs; exact P.nonneg S; exact le_rfl)
    (fun S h => by
      have hc : 2 ≤ S.card := by by_contra hc; simp [pruneMass,hc] at h
      have hm : P.mass S ≠ 0 := by simpa [pruneMass,hc] using h
      exact ⟨P.supported S hm,hc⟩)
    (fun i j hij => by
      simp_rw [pruneMass_edge id P.mass hij]
      simpa only [id_eq,subsetMoment,Finset.insert_subset_iff,Finset.singleton_subset_iff,
        one_mul] using P.edge_load i j hij)
  refine ⟨Q,?_⟩
  change (partitionOfCliqueLaw G id (pruneMass id P.mass) _ _ _).cost ≤ _
  rw [partitionOfCliqueLaw_cost]
  apply Finset.sum_le_sum
  intro S _
  dsimp [pruneMass]
  split_ifs
  · exact le_rfl
  · exact P.nonneg S

end Erdos1017
