import AllHTopTwo.Selection
import AllHTopTwo.PetalEscape

/-! R172: exact strict third-surplus original-host fragile-free contract. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHThirdFragileFree
open QB4 B5 L34 H3Unequal
universe u

def offset (h : ℕ) : ℕ := h^2+5*h+8

def constant (h q a : ℕ) : ℕ := h * q - a

structure Parameters (h q a j : ℕ) : Prop where
  height : 4 ≤ h
  large : 1024 * (h + 1) ^ 2 ≤ q
  lower : 8 * h ≤ a
  upper : a ≤ h ^ 2 + 5 * h + 8
  surplus : j = h - 3

/-- Exact public parameters; the offset is fixed internally. -/
structure HostParameters (h q j : ℕ) : Prop where
  height : 4 ≤ h
  large : 1024*(h+1)^2 ≤ q
  surplus : j=h-3

/-- Literal original graph contract; no selected success or factor premise. -/
structure Host (h q j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) : Prop where
  parameters : HostParameters h q j
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  bipartite : G.IsBipartiteWith (A : Set V) (B : Set V)
  card : #B = #A + j
  order : 2 * q ≤ Fintype.card V
  min_degree : ∀ v : V, q ≤ G.degree v
  cap_degree : ∀ v : V, G.degree v ≤ 2 * q - 2
  edges : G.edgeSet.ncard + constant h q (offset h) = (q - 1) * Fintype.card V
  proper : ∀ X : Finset V, h ≤ #X → #X < Fintype.card V →
    (constant h q (offset h) : ℤ) + 1 ≤ ((q : ℤ) - 1) * #X -
      ((G.induce (X : Set V)).edgeSet.ncard : ℤ)

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Original paired resources, internally derived from Host. -/
structure Data (h q a j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Prop where
  parameters : Parameters h q a j
  disjoint : Disjoint A B
  card : #B = #A + j
  minA : ∀ v ∈ A, q ≤ dg G B v
  capA : ∀ v ∈ A, dg G B v ≤ 2 * q - 2
  minB : ∀ v ∈ B, q ≤ dg G A v
  capB : ∀ v ∈ B, dg G A v ≤ 2 * q - 2
  highA : ∀ v ∈ A, q+2*h-4 ≤ dg G B v
  deficient : deficiency (2 * (q : ℤ) - 2) G B A =
    (h : ℤ) * q - a - ((q : ℤ) - 1) * j
  sparse : ∀ X ⊆ A, ∀ Y ⊆ B, h ≤ #X + #Y → #X + #Y < #A + #B →
    2 * ((h : ℤ) * q - a + 1) ≤ potential (2 * (q : ℤ) - 2) G X Y

/-- Two-unit escape at actual locally maximal height at least two. -/
def PetalEscapeClaim : Prop :=
  ∀ (h q a j : ℕ) (A B K ban : Finset V), Data h q a j G A B →
    K ⊆ B → q - 1 ≤ #K → 2 ≤ thetaJ q j G A B K →
    (∀ T ⊆ B, K ⊆ T → K ≠ T → thetaJ q j G A B T ≤ thetaJ q j G A B K - 1) →
    ban ⊆ B \ K → #ban ≤ 3 * h →
    ∃ z ∈ B \ K, z ∉ ban ∧
      ∀ P ⊆ B \ K, z ∈ P → 2 ≤ extensionCost q j G A B K P

/-- Three-unit escape ONLY at the actual top height 2j+1. -/
def TopEscapeClaim : Prop :=
  ∀ (h q a j : ℕ) (A B K ban : Finset V), Data h q a j G A B →
    K ⊆ B → q - 1 ≤ #K → thetaJ q j G A B K = 2 * (j : ℤ) + 1 →
    (∀ T ⊆ B, K ⊆ T → K ≠ T → thetaJ q j G A B T ≤ thetaJ q j G A B K - 1) →
    ban ⊆ B \ K → #ban ≤ j →
    ∃ z ∈ B \ K, z ∉ ban ∧
      ∀ P ⊆ B \ K, z ∈ P → 3 ≤ extensionCost q j G A B K P

end Erdos585.AllHThirdFragileFree
