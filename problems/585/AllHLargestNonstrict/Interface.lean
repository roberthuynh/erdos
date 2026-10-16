import AllHTopTwo.Selection
import AllHTopTwo.PetalEscape

/-! R119: variable-offset, nonstrict largest-surplus original-host contract. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHLargestNonstrict
open QB4 B5 L34 H3Unequal
universe u

def constant (h q a : ℕ) : ℕ := h * q - a

structure Parameters (h q a j : ℕ) : Prop where
  height : 3 ≤ h
  large : 1024 * (h + 1) ^ 2 ≤ q
  lower : 8 * h ≤ a
  upper : a ≤ h ^ 2 + 5 * h + 8
  surplus : j = h - 1

/-- Literal original fields only. The proper support floor is NONSTRICT. -/
structure Host (h q a j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) : Prop where
  parameters : Parameters h q a j
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  bipartite : G.IsBipartiteWith (A : Set V) (B : Set V)
  card : #B = #A + j
  order : 2 * q ≤ Fintype.card V
  min_degree : ∀ v : V, q ≤ G.degree v
  cap_degree : ∀ v : V, G.degree v ≤ 2 * q - 2
  edges : G.edgeSet.ncard + constant h q a = (q - 1) * Fintype.card V
  proper : ∀ X : Finset V, h ≤ #X → #X < Fintype.card V →
    (constant h q a : ℤ) ≤ ((q : ℤ) - 1) * #X -
      ((G.induce (X : Set V)).edgeSet.ncard : ℤ)

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Internal original paired resources, derived from Host at the public endpoint. -/
structure Data (h q a j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Prop where
  parameters : Parameters h q a j
  disjoint : Disjoint A B
  card : #B = #A + j
  minA : ∀ v ∈ A, q ≤ dg G B v
  capA : ∀ v ∈ A, dg G B v ≤ 2 * q - 2
  minB : ∀ v ∈ B, q ≤ dg G A v
  capB : ∀ v ∈ B, dg G A v ≤ 2 * q - 2
  deficient : deficiency (2 * (q : ℤ) - 2) G B A =
    (h : ℤ) * q - a - ((q : ℤ) - 1) * j
  sparse : ∀ X ⊆ A, ∀ Y ⊆ B, h ≤ #X + #Y → #X + #Y < #A + #B →
    2 * ((h : ℤ) * q - a) ≤ potential (2 * (q : ℤ) - 2) G X Y

/-- Nonstrict cost-one escape on actual original residual sets. -/
def PetalEscapeClaim : Prop :=
  ∀ (h q a j : ℕ) (A B K : Finset V), Data h q a j G A B →
    K ⊆ B → q - 1 ≤ #K → 2 ≤ thetaJ q j G A B K →
    (∀ T ⊆ B, K ⊆ T → K ≠ T → thetaJ q j G A B T ≤ thetaJ q j G A B K - 1) →
    ∃ z ∈ B \ K, ∀ P ⊆ B \ K, z ∈ P → 2 ≤ extensionCost q j G A B K P

end Erdos585.AllHLargestNonstrict
