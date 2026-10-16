import Openmath.Proofs.PaperSupport.Star21.SeedMatrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Cascade29

abbrev SeedVertex := Fin 12 ⊕ Fin 13
abbrev GraphData := Erdos585.Star21.GraphData

/-- The exact original 12-by-13 cascade seed, including its seven-edge birth. -/
def seedRel (i : Fin 12) (j : Fin 13) : Prop :=
  if j.val < 12 then
    if i.val < 9 then ¬ (i.val < 4 ∧ j.val / 3 = i.val)
    else if i.val = 10 then 6 ≤ j.val else j.val < 6
  else i.val < 4 ∨ 9 ≤ i.val

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
  | .inl i => if i.val < 9 then i.val else 12+i.val
  | .inr j => if j.val < 12 then 9+j.val else 24

def seedLabels : BqCircularLowerFamily.Labeling SeedVertex where
  label := seedLabel
  injective := by
    intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        apply congrArg Sum.inl
        apply Fin.ext
        change (if i.val < 9 then i.val else 12+i.val) =
          (if j.val < 9 then j.val else 12+j.val) at h
        have hi := i.isLt
        have hj := j.isLt
        split_ifs at h <;> omega
      | inr j =>
        change (if i.val < 9 then i.val else 12+i.val) =
          (if j.val < 12 then 9+j.val else 24) at h
        have hi := i.isLt
        have hj := j.isLt
        split_ifs at h <;> omega
    | inr i =>
      cases y with
      | inl j =>
        change (if i.val < 12 then 9+i.val else 24) =
          (if j.val < 9 then j.val else 12+j.val) at h
        have hi := i.isLt
        have hj := j.isLt
        split_ifs at h <;> omega
      | inr j =>
        apply congrArg Sum.inr
        apply Fin.ext
        change (if i.val < 12 then 9+i.val else 24) =
          (if j.val < 12 then 9+j.val else 24) at h
        have hi := i.isLt
        have hj := j.isLt
        split_ifs at h <;> omega
  bounded := by
    intro x
    simp only [Fintype.card_sum, Fintype.card_fin]
    cases x with
    | inl i =>
      change (if i.val < 9 then i.val else 12+i.val) < 12+13
      have hi := i.isLt
      split_ifs <;> omega
    | inr j =>
      change (if j.val < 12 then 9+j.val else 24) < 12+13
      have hj := j.isLt
      split_ifs <;> omega

abbrev seedData : GraphData where
  Carrier := SeedVertex
  fintype := inferInstance
  decEq := inferInstance
  graph := seedGraph
  decAdj := inferInstance
  left := seedLeft
  right := seedRight
  labels := seedLabels

def Cascade29Endpoint : Prop :=
  ∀ (n : ℕ), 25 ≤ n →
    ∃ (V : Type) (vf : Fintype V) (vd : DecidableEq V),
      letI := vf
      letI := vd
      ∃ (G : SimpleGraph V) (gd : DecidableRel G.Adj),
        letI := gd
        Fintype.card V = n ∧ G.IsBipartite ∧
          (∀ v, 6 ≤ G.degree v) ∧ G.maxDegree ≤ 12 ∧
          G.edgeFinset.card = 6*n-29 ∧
          ¬ (∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 7)

end Erdos585.Cascade29
