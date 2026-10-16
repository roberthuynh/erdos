import L17HCq.Counts
import Mathlib.Data.Nat.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.GeneralStar

/-- Original graph data, with no success or invariant proof stored. -/
structure GraphData where
  Carrier : Type
  fintype : Fintype Carrier
  decEq : DecidableEq Carrier
  graph : SimpleGraph Carrier
  decAdj : DecidableRel graph.Adj
  A : Finset Carrier
  B : Finset Carrier
  labels : @BqLowerFamily.Labeling Carrier fintype

instance (D : GraphData) : Fintype D.Carrier := D.fintype
instance (D : GraphData) : DecidableEq D.Carrier := D.decEq
instance (D : GraphData) : DecidableRel D.graph.Adj := D.decAdj

def GraphData.order (D : GraphData) : ℕ := Fintype.card D.Carrier
def GraphData.label (D : GraphData) : D.Carrier → ℕ := D.labels.label

def GraphData.add (D : GraphData) (toA : Bool) (N : Finset D.Carrier) : GraphData where
  Carrier := Option D.Carrier
  fintype := inferInstance
  decEq := inferInstance
  graph := BqLowerFamily.extendGraph D.graph N
  decAdj := inferInstance
  A := if toA then insert none (D.A.image some) else D.A.image some
  B := if toA then D.B.image some else insert none (D.B.image some)
  labels := D.labels.extend

def seedSlot (q : ℕ) (D : GraphData) (z : ℕ) : ℕ :=
  ∑ v ∈ D.B, if D.label v = z then 2*(q-1)-D.graph.degree v else 0

/-- Greedy truncation in the actual original label order. -/
def allocateWord (slot : ℕ → ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | remaining, z :: zs =>
      List.replicate (min (slot z) remaining) z ++
        allocateWord slot (remaining-min (slot z) remaining) zs

def startupWord (q : ℕ) (D : GraphData) : List ℕ :=
  allocateWord (seedSlot q D) ((q-1)*(q-1)) ((D.B.image D.label).sort (· ≤ ·))

def startupLabels (q : ℕ) (D : GraphData) (t : ℕ) : Finset ℕ :=
  (range (q-1)).image fun j => (startupWord q D).getD (t+j*(q-1)) 0

def prescribedLabels (q : ℕ) (D : GraphData) (t : ℕ) : Finset ℕ :=
  if t < q-1 then startupLabels q D t else
    (range (q-1)).image fun j => D.order+(t/(q-1)-1)*(q-1)+j

def receivingA (q t : ℕ) : Bool :=
  decide (t < q-1 ∨ (t/(q-1)) % 2 = 0)

def transferNeighbors (q : ℕ) (seed D : GraphData) (t : ℕ) : Finset D.Carrier :=
  univ.filter fun v => D.label v ∈ prescribedLabels q seed t

def transferState (q : ℕ) (seed : GraphData) : ℕ → GraphData
  | 0 => seed
  | t+1 =>
      let D := transferState q seed t
      D.add (receivingA q t) (transferNeighbors q seed D t)

def FamilyConclusion (q n c : ℕ) (D : GraphData) : Prop :=
  D.order = n ∧ D.graph.IsBipartite ∧
    (∀ v, q-1 ≤ D.graph.degree v) ∧ D.graph.maxDegree ≤ 2*q-2 ∧
    D.graph.edgeFinset.card = (q-1)*n-c ∧
    ¬ (∃ H : D.graph.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q)

def SeedHyp (q : ℕ) (D : GraphData) : Prop :=
  Disjoint D.A D.B ∧ D.A ∪ D.B = univ ∧
    D.graph.IsBipartiteWith (D.A : Set D.Carrier) (D.B : Set D.Carrier) ∧
    (∀ v, q-1 ≤ D.graph.degree v ∧ D.graph.degree v ≤ 2*(q-1)) ∧
    BqLowerFamily.NoRegular q D.graph ∧
    (q-1)^2 ≤ ∑ v ∈ D.B, (2*(q-1)-D.graph.degree v)

def uniformRel (q s p h b : ℕ) (i : Fin (q+s)) (j : Fin b) : Prop :=
  ¬ (i.val < p ∧ i.val*h ≤ j.val ∧ j.val < (i.val+1)*h)

instance uniformRelDecidable (q s p h b : ℕ) : DecidableRel (uniformRel q s p h b) :=
  fun _ _ => by unfold uniformRel; infer_instance

def uniformLabel (a b : ℕ) : (Fin a ⊕ Fin b) → ℕ
  | .inl i => i.val
  | .inr j => a+j.val

def uniformLabeling (a b : ℕ) : BqLowerFamily.Labeling (Fin a ⊕ Fin b) where
  label := uniformLabel a b
  injective := by
    intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (Fin.ext h)
      | inr j => change i.val=a+j.val at h; have := i.isLt; omega
    | inr i =>
      cases y with
      | inl j => change a+i.val=j.val at h; have := j.isLt; omega
      | inr j =>
        change a+i.val=a+j.val at h
        exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel h))
  bounded := by
    intro x
    simp only [Fintype.card_sum,Fintype.card_fin]
    cases x with
    | inl i => change i.val<a+b; have := i.isLt; omega
    | inr j => change a+j.val<a+b; have := j.isLt; omega

def uniformSeed (q s p h b : ℕ) : GraphData where
  Carrier := Fin (q+s) ⊕ Fin b
  fintype := inferInstance
  decEq := inferInstance
  graph := L17HCq.crossGraph (uniformRel q s p h b)
  decAdj := inferInstance
  A := univ.image Sum.inl
  B := univ.image Sum.inr
  labels := uniformLabeling (q+s) b

def hcqLabel (q : ℕ) : L17HCq.SeedVertex q → ℕ
  | .inl (.inl i) => i.val
  | .inl (.inr i) => q+1+i.val
  | .inr (.inl j) => q+3+j.val
  | .inr (.inr _) => 2*q+6

def hcqLabels (q : ℕ) : BqLowerFamily.Labeling (L17HCq.SeedVertex q) where
  label := hcqLabel q
  injective := by
    intro x y h
    rcases x with (i | a) | (j | u) <;> rcases y with (i' | a') | (j' | u')
    all_goals simp only [hcqLabel] at h
    all_goals try (simp only [Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,Fin.ext_iff])
    all_goals first | exact Subsingleton.elim _ _ | omega
  bounded := by
    intro x
    have hc : Fintype.card (L17HCq.SeedVertex q)=2*q+7 := by
      simp [L17HCq.SeedVertex,L17HCq.SeedLeft,L17HCq.SeedRight,Fintype.card_sum];omega
    rw [hc]
    rcases x with (i | a) | (j | u) <;> dsimp [hcqLabel] <;> omega

def hcqSeed (q : ℕ) : GraphData where
  Carrier := L17HCq.SeedVertex q
  fintype := inferInstance
  decEq := inferInstance
  graph := L17HCq.hcqSeedGraph q
  decAdj := inferInstance
  A := L17HCq.hcqSeedA q
  B := L17HCq.hcqSeedB q
  labels := hcqLabels q

def UParams (q s p h b : ℕ) : Prop :=
  1 ≤ s ∧ s+1 ≤ p ∧ s+1 ≤ h ∧ p ≤ q+s ∧ q+s ≤ b ∧ b ≤ 2*(q-1) ∧
    p*h ≤ b ∧ q-1 ≤ b-h ∧ b-q < (p-s)*h ∧ b-q-s < p*(h-s)

def uniformStart (q s b : ℕ) : ℕ := q+s+b
def uniformDeficit (q s p h b : ℕ) : ℕ :=
  (q-1)*(q+s+b)-(q+s)*b+p*h
def uniformFamily (q s p h b n : ℕ) : GraphData :=
  transferState q (uniformSeed q s p h b) (n-uniformStart q s b)

def ceilDiv (x y : ℕ) : ℕ := (x+y-1)/y
def closedD (q : ℕ) : ℕ := Nat.sqrt ((q-1)/2)
def exceptional (q : ℕ) : Prop :=
  1 ≤ q-1-2*(closedD q)^2 ∧ q-1-2*(closedD q)^2 ≤ closedD q-1
instance exceptionalDecidable (q : ℕ) : Decidable (exceptional q) := by
  unfold exceptional; infer_instance
def closedS (q : ℕ) : ℕ := if q=7 ∨ q=8 then 2 else closedD q
def closedH (q : ℕ) : ℕ := if q=7 ∨ q=8 then 3 else 2*closedD q
def closedP (q : ℕ) : ℕ :=
  if q=7 ∨ q=8 then 4 else if exceptional q then 2*closedD q else
    max (closedD q+ceilDiv (q-1) (2*closedD q)) (ceilDiv (q-1) (closedD q)-1)
def closedB (q : ℕ) : ℕ :=
  if q=7 then 12 else if q=8 then 13 else
    if exceptional q then q-1+2*(closedD q)^2 else 2*(q-1)
def closedStart (q : ℕ) : ℕ :=
  if q=5 ∨ q=6 then 2*q+7 else q+closedS q+closedB q
def closedDeficit (q : ℕ) : ℕ :=
  if q=5 ∨ q=6 then (q-1)^2-3 else
    if q=7 then 30 else if q=8 then 43 else
      if exceptional q then (q-1)^2-2*(closedD q)^2*(closedD q-1) else
        (q-1)^2-(q-1)*(closedD q+1)+2*closedD q*closedP q
def closedSeed (q : ℕ) : GraphData :=
  if q=5 ∨ q=6 then hcqSeed q else uniformSeed q (closedS q) (closedP q) (closedH q) (closedB q)
def closedState (q t : ℕ) : GraphData := transferState q (closedSeed q) t
def closedFamily (q n : ℕ) : GraphData := closedState q (n-closedStart q)
def C24Endpoint : Prop :=
  ∀ (q n : ℕ), 5 ≤ q → closedStart q ≤ n →
    FamilyConclusion q n (closedDeficit q) (closedFamily q n)

end Erdos585.GeneralStar
