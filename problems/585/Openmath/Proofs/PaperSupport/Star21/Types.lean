import Openmath.Proofs.PaperSupport.BqCircularLowerDirect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.Star21

abbrev SeedVertex := Fin 9 ⊕ Fin 12

/-- Actual disjoint three-hole groups on four original rows. -/
def holes (i : Fin 9) : Finset (Fin 12) :=
  univ.filter fun j => i.val < 4 ∧ j.val / 3 = i.val

def seedRel (i : Fin 9) (j : Fin 12) : Prop := j ∉ holes i

instance seedRelDecidable : ∀ i j, Decidable (seedRel i j) := by
  intro i j
  unfold seedRel
  infer_instance

def seedAdj (x y : SeedVertex) : Prop :=
  match x, y with
  | .inl i, .inr j => seedRel i j
  | .inr j, .inl i => seedRel i j
  | _, _ => False

def seedGraph : SimpleGraph SeedVertex where
  Adj := seedAdj
  symm := ⟨by intro x y; cases x <;> cases y <;> simp [seedAdj]⟩
  loopless := ⟨by intro x; cases x <;> simp [seedAdj]⟩

instance seedGraphDecidable : DecidableRel seedGraph.Adj := fun x y => by
  cases x <;> cases y <;> dsimp [seedGraph, seedAdj] <;> infer_instance

def seedLeft : Finset SeedVertex := univ.image Sum.inl
def seedRight : Finset SeedVertex := univ.image Sum.inr

def seedLabel : SeedVertex → ℕ
  | .inl i => i.val
  | .inr j => 9 + j.val

def seedLabels : BqCircularLowerFamily.Labeling SeedVertex where
  label := seedLabel
  injective := by
    intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (Fin.ext h)
      | inr j =>
        change i.val = 9 + j.val at h
        have hi := i.isLt
        omega
    | inr i =>
      cases y with
      | inl j =>
        change 9 + i.val = j.val at h
        have hj := j.isLt
        omega
      | inr j =>
        change 9 + i.val = 9 + j.val at h
        exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel h))
  bounded := by
    intro x
    simp only [Fintype.card_sum, Fintype.card_fin]
    cases x with
    | inl i =>
      change i.val < 9 + 12
      have hi := i.isLt
      omega
    | inr j =>
      change 9 + j.val < 9 + 12
      have hj := j.isLt
      omega

/-- Data only: no avoiding seed, invariant or success proof is a field. -/
structure GraphData where
  Carrier : Type
  fintype : Fintype Carrier
  decEq : DecidableEq Carrier
  graph : SimpleGraph Carrier
  decAdj : DecidableRel graph.Adj
  left : Finset Carrier
  right : Finset Carrier
  labels : @BqCircularLowerFamily.Labeling Carrier fintype

instance (D : GraphData) : Fintype D.Carrier := D.fintype
instance (D : GraphData) : DecidableEq D.Carrier := D.decEq
instance (D : GraphData) : DecidableRel D.graph.Adj := D.decAdj

abbrev seedData : GraphData where
  Carrier := SeedVertex
  fintype := inferInstance
  decEq := inferInstance
  graph := seedGraph
  decAdj := inferInstance
  left := seedLeft
  right := seedRight
  labels := seedLabels

abbrev GraphData.add (D : GraphData) (toLeft : Bool) (N : Finset D.Carrier) : GraphData where
  Carrier := Option D.Carrier
  fintype := inferInstance
  decEq := inferInstance
  graph := BqCircularLowerFamily.extendGraph D.graph N
  decAdj := inferInstance
  left := if toLeft then insert none (D.left.image some) else D.left.image some
  right := if toLeft then D.right.image some else insert none (D.right.image some)
  labels := D.labels.extend

def Star21Endpoint : Prop :=
  ∀ (n : ℕ), 21 ≤ n →
    ∃ (V : Type) (vf : Fintype V) (vd : DecidableEq V),
      letI := vf
      letI := vd
      ∃ (G : SimpleGraph V) (gd : DecidableRel G.Adj),
        letI := gd
        Fintype.card V = n ∧ G.IsBipartite ∧
          (∀ v, 6 ≤ G.degree v) ∧ G.maxDegree ≤ 12 ∧
          G.edgeFinset.card = 6*n-30 ∧
          ¬ (∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 7)

end Erdos585.Star21
