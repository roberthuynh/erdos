import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.Counter90

abbrev CoreVertex := Fin 10 ⊕ Fin 12

/-- Original row order and the literal twelve incidence bits. -/
def rowMask (i : Fin 10) : ℕ :=
  [3769,3399,3543,3951,3775,1535,1023,1023,1023,2744][i.val]!

def rel (i : Fin 10) (j : Fin 12) : Prop := (rowMask i).testBit j.val = true

instance relDecidable : ∀ i j, Decidable (rel i j) := by
  intro i j
  unfold rel
  infer_instance

def coreAdj (x y : CoreVertex) : Prop :=
  match x, y with
  | .inl i, .inr j => rel i j
  | .inr j, .inl i => rel i j
  | _, _ => False

def coreGraph : SimpleGraph CoreVertex where
  Adj := coreAdj
  symm := ⟨by intro x y; cases x <;> cases y <;> simp [coreAdj]⟩
  loopless := ⟨by intro x; cases x <;> simp [coreAdj]⟩

instance coreGraphDecidable : DecidableRel coreGraph.Adj := fun x y => by
  cases x <;> cases y <;> dsimp [coreGraph,coreAdj] <;> infer_instance

def labelEquiv : CoreVertex ≃ Fin 22 := finSumFinEquiv

/-- Actual original graph on Fin22; this record contains no success proposition. -/
def graph : SimpleGraph (Fin 22) := coreGraph.comap labelEquiv.symm

instance graphDecidable : DecidableRel graph.Adj := fun x y => by
  dsimp [graph]
  infer_instance

noncomputable instance finiteSubgraphLocallyFinite {V : Type*} [Finite V]
    (G : SimpleGraph V) (H : G.Subgraph) : H.coe.LocallyFinite := fun _ => Fintype.ofFinite _

def rowNeighbors (i : Fin 10) : Finset (Fin 12) := univ.filter fun j => rel i j
def columnNeighbors (j : Fin 12) : Finset (Fin 10) := univ.filter fun i => rel i j
def rowDegree (Q : Finset (Fin 12)) (i : Fin 10) : ℕ := (Q ∩ rowNeighbors i).card
def columnDegree (P : Finset (Fin 10)) (j : Fin 12) : ℕ := (P ∩ columnNeighbors j).card
def baseColumns : Finset (Fin 12) := univ.filter fun j => j.val < 10
def baseNeighbors (i : Fin 10) : Finset (Fin 12) := baseColumns ∩ rowNeighbors i
def holes (i : Fin 10) : Finset (Fin 12) := baseColumns \ rowNeighbors i
def exceptional : Finset (Fin 10) := {2,3,4,5}
def remainingRows : Finset (Fin 10) := {2,3,4,5,6,7,8}

@[simp] theorem mem_rowNeighbors (i : Fin 10) (j : Fin 12) : j ∈ rowNeighbors i ↔ rel i j := by
  simp [rowNeighbors]
@[simp] theorem mem_columnNeighbors (i : Fin 10) (j : Fin 12) : i ∈ columnNeighbors j ↔ rel i j := by
  simp [columnNeighbors]

end Erdos585.Counter90
