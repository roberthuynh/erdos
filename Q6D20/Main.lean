import Q6D20.Family
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Finset SimpleGraph
namespace Erdos585.Q6D20R31

/-- The closed graph-valued literal family; no input graph or feasibility supplier. -/
noncomputable def familyGraph (n : ℕ) : SimpleGraph (Fin n) := (familyData n).graph
instance familyGraphDecidable (n : ℕ) : DecidableRel (familyGraph n).Adj := (familyData n).decAdj

def familyA (n : ℕ) : Finset (Fin n) := (familyData n).A
def familyB (n : ℕ) : Finset (Fin n) := (familyData n).B
def birthNeighbors (n : ℕ) : Finset (Fin n) := selectedNeighbors (familyData n)
noncomputable def eligibleOpposite (n : ℕ) : Finset (Fin n) :=
  (if (familyA n).card < (familyB n).card then familyB n else familyA n).filter
    (fun v => (familyGraph n).degree v ≤ 9)

/-- Literal original q6 family on exactly n integer labels, every support free. -/
theorem all_orders (n : ℕ) (hn : 22 ≤ n) :
    (familyGraph n).IsBipartite ∧
    (∀ v : Fin n, 5 ≤ (familyGraph n).degree v ∧ (familyGraph n).degree v ≤ 10) ∧
    (familyGraph n).maxDegree ≤ 10 ∧
    (familyGraph n).edgeFinset.card = 5*n-20 ∧
    ¬ (∃ H : (familyGraph n).Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 6) := by
  have h := familyData_good n hn
  refine ⟨h.bipartite.isBipartite, h.degrees, ?_, ?_, h.no_regular⟩
  · exact (familyGraph n).maxDegree_le_of_forall_degree_le 10 (fun v => (h.degrees v).2)
  · have he := Nat.eq_sub_of_add_eq h.density
    simp only [Fintype.card_fin] at he
    convert he using 1
    apply congrArg Finset.card
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rfl

def LowerEndpoint : Prop := ∀ n : ℕ, 22 ≤ n →
    (familyGraph n).IsBipartite ∧
    (∀ v : Fin n, 5 ≤ (familyGraph n).degree v ∧ (familyGraph n).degree v ≤ 10) ∧
    (familyGraph n).maxDegree ≤ 10 ∧
    (familyGraph n).edgeFinset.card = 5*n-20 ∧
    ¬ (∃ H : (familyGraph n).Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 6)

theorem lowerEndpoint : LowerEndpoint := all_orders

/-- Every original old vertex and unit adjacency is retained exactly. -/
theorem old_adjacency (n : ℕ) (hn : 22 ≤ n) (v w : Fin n) :
    (familyGraph (n+1)).Adj (Fin.castSucc v) (Fin.castSucc w) ↔
      (familyGraph n).Adj v w := by
  change (familyData (n+1)).graph.Adj _ _ ↔ _
  rw [familyData_succ n hn]
  simp [step, BqLowerFamily.extendGraph, familyGraph]

/-- Exactly the literal five priority-first ascending eligible opposite labels are new unit neighbors. -/
theorem new_adjacency (n : ℕ) (hn : 22 ≤ n) (v : Fin n) :
    (familyGraph (n+1)).Adj (Fin.last n) (Fin.castSucc v) ↔ v ∈ birthNeighbors n := by
  change (familyData (n+1)).graph.Adj _ _ ↔ _
  rw [familyData_succ n hn]
  simp [step, BqLowerFamily.extendGraph, birthNeighbors]

theorem birthNeighbors_card (n : ℕ) (hn : 22 ≤ n) : (birthNeighbors n).card = 5 :=
  selectedNeighbors_card (familyData n) (familyData_good n hn) (familyData_low_le_two n hn)

theorem birthNeighbors_eligible (n : ℕ) (v : Fin n) (hv : v ∈ birthNeighbors n) :
    v ∈ eligibleOpposite n := selectedNeighbors_subset (familyData n) hv

theorem birthNeighbors_original_degree (n : ℕ) (v : Fin n) (hv : v ∈ birthNeighbors n) :
    (familyGraph n).degree v ≤ 9 := (mem_filter.mp (birthNeighbors_eligible n v hv)).2

/-- All original degree-five opposite endpoints have priority over other labels. -/
theorem birthNeighbors_mandatory (n : ℕ) (hn : 22 ≤ n) :
    selectedLow (familyData n) ⊆ birthNeighbors n :=
  selectedNeighbors_mandatory _ (familyData_low_le_two n hn)

theorem birthNeighbors_exact_labels (n : ℕ) :
    (birthNeighbors n).image Fin.val =
      (((priorityList (selectedEligible (familyData n)) (selectedLow (familyData n))).take 5).map
        Fin.val).toFinset := by
  change (priorityFive _ _).image Fin.val = _
  ext x
  simp only [priorityFive, Finset.mem_image, List.mem_toFinset, List.mem_map]

theorem old_A_membership (n : ℕ) (hn : 22 ≤ n) (v : Fin n) :
    Fin.castSucc v ∈ familyA (n+1) ↔ v ∈ familyA n := by
  change Fin.castSucc v ∈ (familyData (n+1)).A ↔ _
  rw [familyData_succ n hn]
  by_cases hsmall : (familyData n).A.card < (familyData n).B.card <;>
    simp [hsmall, step, nextA, familyA]

theorem old_B_membership (n : ℕ) (hn : 22 ≤ n) (v : Fin n) :
    Fin.castSucc v ∈ familyB (n+1) ↔ v ∈ familyB n := by
  change Fin.castSucc v ∈ (familyData (n+1)).B ↔ _
  rw [familyData_succ n hn]
  by_cases hsmall : (familyData n).A.card < (familyData n).B.card <;>
    simp [hsmall, step, nextB, familyB]

theorem new_A_membership (n : ℕ) (hn : 22 ≤ n) :
    Fin.last n ∈ familyA (n+1) ↔ (familyA n).card < (familyB n).card := by
  change Fin.last n ∈ (familyData (n+1)).A ↔ _
  rw [familyData_succ n hn]
  by_cases hsmall : (familyData n).A.card < (familyData n).B.card <;>
    simp [hsmall, step, nextA, familyA, familyB]

theorem new_B_membership (n : ℕ) (hn : 22 ≤ n) :
    Fin.last n ∈ familyB (n+1) ↔ (familyB n).card ≤ (familyA n).card := by
  change Fin.last n ∈ (familyData (n+1)).B ↔ _
  rw [familyData_succ n hn]
  by_cases hsmall : (familyData n).A.card < (familyData n).B.card
  · simp [hsmall, step, nextB, familyA, familyB]
  · simp [hsmall, step, nextB, familyA, familyB]
    omega

@[simp] theorem familyGraph_twenty_two : familyGraph 22 = Counter90.graph := rfl

theorem seed_original_incidence (i : Fin 10) (j : Fin 12) :
    (familyGraph 22).Adj (Fin.castAdd 12 i) (Fin.natAdd 10 j) ↔ Counter90.rel i j :=
  Counter90.original_incidence i j

/-- Exact original startup, including the tie clearing BOTH degree-five rows. -/
theorem startup_literal :
    (familyA 22).card = 10 ∧ (familyB 22).card = 12 ∧
    birthNeighbors 22 = {10,11,12,13,14} ∧
    birthNeighbors 23 = {11,12,13,14,15} ∧
    (familyA 24).card = 12 ∧ (familyB 24).card = 12 ∧
    birthNeighbors 24 = {0,1,2,22,23} ∧
    birthNeighbors 25 = {15,16,17,18,24} ∧
    lowAll (familyData 25) = {24} := by decide

end Erdos585.Q6D20R31
