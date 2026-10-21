import Erdos1017.GraphSelector

/-! Lift arbitrary nonnegative multipartite clique-type masses to actual graph cliques.
All original edges are checked. No independence between selected part labels is assumed. -/
namespace Erdos1017
open scoped BigOperators
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

noncomputable def maskedVertices (part : V → ι) (S : Finset ι) (x : ι → Option V) : Finset V :=
  (chosenVertices part x).filter (fun v => part v ∈ S)

/-- A partition of product capacities on part pairs lifts to a graph partition of no larger cost.
Part sizes are unnormalized integer cardinalities; every part is required nonempty. -/
theorem multipartite_partition_of_type_masses (G : SimpleGraph V) (part : V → ι)
    (hG : ∀ u v, G.Adj u v ↔ part u ≠ part v)
    (hpos : ∀ i, 0 < partSize part i)
    (W : Finset ι → ℝ) (hW : ∀ S, 0 ≤ W S)
    (hload : ∀ i j, i ≠ j →
      (∑ S : Finset ι, if i ∈ S ∧ j ∈ S then W S else 0) =
        (partSize part i : ℝ) * partSize part j) :
    ∃ P : FractionalPartition G, P.cost ≤ ∑ S, W S := by
  let q : ι → Option V → ℝ := fun i => vertexChoiceProb (partSize part i) part i
  have hq (i : ι) : ∑ b, q i b = 1 := vertexChoice_total _ part i
  have hqn (i : ι) (b : Option V) : 0 ≤ q i b := by
    have ha : (0 : ℝ) < partSize part i := by exact_mod_cast hpos i
    cases b with
    | none =>
      change 0 ≤ 1 - (partSize part i : ℝ) / partSize part i
      simp [ne_of_gt ha]
    | some v =>
      dsimp [q, vertexChoiceProb]
      split_ifs
      · exact div_nonneg (by norm_num) ha.le
      · exact le_rfl
  let C : Finset ι × (ι → Option V) → Finset V := fun z => maskedVertices part z.1 z.2
  let w : Finset ι × (ι → Option V) → ℝ := fun z => W z.1 * categoricalMass q z.2
  have hw (z) : 0 ≤ w z := mul_nonneg (hW _) (Finset.prod_nonneg (fun i _ => hqn i _))
  have hc (z) : G.IsClique (C z : Set V) := by
    apply (chosenVertices_clique G part hG z.2).subset
    intro v hv
    exact (Finset.mem_filter.mp hv).1
  have he (u v : V) (huv : G.Adj u v) :
      (∑ z, if u ∈ C z ∧ v ∈ C z then w z else 0) = 1 := by
    have hpair := categorical_pair q hq (part u) (part v) ((hG u v).mp huv) (some u) (some v)
    have hinner (S : Finset ι) :
        (∑ x : ι → Option V, if u ∈ maskedVertices part S x ∧ v ∈ maskedVertices part S x
          then W S * categoricalMass q x else 0) =
        (if part u ∈ S ∧ part v ∈ S then W S else 0) *
          (1 / (partSize part (part u) : ℝ)) * (1 / (partSize part (part v) : ℝ)) := by
      calc
        _ = (if part u ∈ S ∧ part v ∈ S then W S else 0) *
            ∑ x : ι → Option V, categoricalMass q x *
              ((if x (part u) = some u then 1 else 0) *
               (if x (part v) = some v then 1 else 0)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          by_cases huS : part u ∈ S <;> by_cases hvS : part v ∈ S <;>
            by_cases hux : x (part u) = some u <;> by_cases hvx : x (part v) = some v <;>
            simp [maskedVertices, chosenVertices, huS, hvS, hux, hvx]
        _ = _ := by rw [hpair]; simp [q, vertexChoiceProb, mul_assoc]
    change (∑ z : Finset ι × (ι → Option V),
      if u ∈ maskedVertices part z.1 z.2 ∧ v ∈ maskedVertices part z.1 z.2
      then W z.1 * categoricalMass q z.2 else 0) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [hinner]
    rw [← Finset.sum_mul, ← Finset.sum_mul, hload _ _ ((hG u v).mp huv)]
    have hu : (partSize part (part u) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hpos _))
    have hv : (partSize part (part v) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hpos _))
    field_simp
  let P := partitionOfCliqueLawPruned G C w hw hc he
  refine ⟨P, ?_⟩
  change (partitionOfCliqueLawPruned G C w hw hc he).cost ≤ ∑ S, W S
  rw [partitionOfCliqueLawPruned_cost]
  calc
    _ ≤ ∑ z, w z := by
      apply Finset.sum_le_sum
      intro z _
      split_ifs
      · exact le_rfl
      · exact hw z
    _ = ∑ S, W S := by
      simp only [w, Fintype.sum_prod_type, ← Finset.mul_sum]
      simp [categorical_total q hq]

end Erdos1017
