import AllHLargestNonstrict.Main
import AllHNextNonstrict.Main

/-! R149: the literal all-height original top-critical input and derived outputs. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHTopCritical
open QB4 B5 L34 H3Unequal
universe u

def offset (h : ℕ) : ℕ := h ^ 2 + 5 * h + 8
def constant (h q : ℕ) : ℕ := h * q - offset h
def selectorOffset (h : ℕ) : ℕ := offset h - 1

structure Parameters (h q : ℕ) : Prop where
  height : 3 ≤ h
  large : 1024 * (h + 1) ^ 2 ≤ q

/-- No arbitrary-support original regular subgraph, including noninduced/disconnected ones. -/
def Noq (q : ℕ) {V : Type u} [Fintype V] (G : SimpleGraph V) : Prop :=
  ¬ ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q

/-- Complete original balanced input. The strict floor starts ONLY at order 2q. -/
structure Host (h q : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) : Prop where
  parameters : Parameters h q
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  balanced : #A = #B
  bipartite : G.IsBipartiteWith (A : Set V) (B : Set V)
  order : 2 * q ≤ Fintype.card V
  min_degree : ∀ v : V, q ≤ G.degree v
  cap_degree : ∀ v : V, G.degree v ≤ 2 * q - 2
  edges : G.edgeSet.ncard + constant h q = (q - 1) * Fintype.card V
  no_regular : Noq q G
  proper : ∀ X : Finset V, 2 * q ≤ #X → #X < Fintype.card V →
    (constant h q : ℤ) + 1 ≤ ((q : ℤ) - 1) * #X -
      ((G.induce (X : Set V)).edgeSet.ncard : ℤ)

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Literal strict canonical definitions and specified values, without block consequences. -/
structure TopCore (h q : ℕ) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B R T : Finset V) : Prop where
  T_subset : T ⊆ B
  canonical : R = B5.canonical q G A B T
  eligible : 2 * q ≤ #R + #T
  proper : #R + #T < Fintype.card V
  imbalance : #R = #T + (h - 1)
  height : thetaJ q 0 G A B T = (h : ℤ) - 2
  captured : deficiency (2 * (q : ℤ) - 2) G B R = constant h q
  potential : B5.potential (2 * (q : ℤ) - 2) G R T = 2 * ((constant h q : ℤ) + 1)

/-- ALL original larger-shore degree-(q-1) vertices, with no selected root supplier. -/
def lowRoots (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) : Finset V := X.filter fun v => dg G Y v = q - 1

def retained (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) : Finset V := (X \ lowRoots q G X Y) ∪ Y

/-- The actual maximal induced minimum-q original support inside a diagonal. -/
def IsOriginalQCore (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (W S : Finset V) : Prop :=
  S ⊆ W ∧ S.Nonempty ∧ (∀ v ∈ S, q ≤ dg G S v) ∧
    ∀ Z ⊆ W, (∀ v ∈ Z, q ≤ dg G Z v) → Z ⊆ S

/-- Derived original rigidity of BOTH diagonal blocks, not an input interface. -/
structure Rigidity (h q : ℕ) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B R T : Finset V) : Prop where
  T_saturated : ∀ v ∈ T, G.degree v = 2 * q - 2
  complement_saturated : ∀ v ∈ A \ R, G.degree v = 2 * q - 2
  reverse_imbalance : #(B \ T) = #(A \ R) + (h - 1)
  forward : (ec G R (B \ T) : ℤ) = ((h : ℤ) - 1) * q - h + 2
  reverse : (ec G (A \ R) T : ℤ) = (q : ℤ) + h - offset h
  first_deficit : coreDefect q G R T = (constant h q : ℤ) + 1
  second_deficit : coreDefect q G (A \ R) (B \ T) = (constant h q : ℤ) + 1
  T_order : 2 * q - h - 1 ≤ #T
  complement_order : 2 * q - h - 1 ≤ #(A \ R)
  whole_order : 8 * q - 2 * h - 6 ≤ Fintype.card V

/-- All low-root, retained incidence, missing-floor and actual q-core conclusions. -/
structure DiagonalConclusion (h q : ℕ) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) : Prop where
  surplus : #X = #Y + (h - 1)
  smaller_order : 2 * q - h - 1 ≤ #Y
  block_deficit : coreDefect q G X Y = (constant h q : ℤ) + 1
  minimum_X : ∀ v ∈ X, q - 1 ≤ dg G Y v
  minimum_Y : ∀ v ∈ Y, q - 1 ≤ dg G X v
  exact_minimum : ∃ v ∈ X, dg G Y v = q - 1
  deleted_count : 2 ≤ #(lowRoots q G X Y) ∧ #(lowRoots q G X Y) ≤ 2 * h - 4
  retained_deficit : coreDefect q G (X \ lowRoots q G X Y) Y = (constant h q : ℤ) + 1
  retained_minimum : ∀ v ∈ retained q G X Y, q ≤ dg G (retained q G X Y) v
  retained_cap : ∀ v ∈ retained q G X Y, dg G (retained q G X Y) v ≤ 2 * q - 2
  retained_order : 4 * q - 3 * h - 1 ≤ #(retained q G X Y)
  retained_eligible : 2 * q ≤ #(retained q G X Y)
  retained_floor : ∀ Z ⊆ retained q G X Y, h ≤ #Z →
    (constant h q : ℤ) + 1 ≤ ((q : ℤ) - 1) * #Z -
      ((G.induce (Z : Set V)).edgeSet.ncard : ℤ)
  actual_qcore : IsOriginalQCore q G (X ∪ Y) (retained q G X Y)

end Erdos585.AllHTopCritical
