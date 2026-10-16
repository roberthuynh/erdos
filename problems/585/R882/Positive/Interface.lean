import AllHTopTwo.Selection
import AllHTopTwo.PetalEscape

/-! R882: quadratic-cutoff full-C original-floor interface, adapted from R863 and the credited R257 machinery. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.R882.Positive
open QB4 B5 L34 H3Unequal
universe u

def offset (h e : ℕ) : ℕ := 16 * h ^ 2 - e

def constant (h q e : ℕ) : ℕ := h * q - offset h e

structure Parameters (h q j e : ℕ) : Prop where
  height : 6 ≤ h
  error_bound : e ≤ 4 * h ^ 2 - 10 * h + 4
  large : 4096 * (h + 1) ^ 2 ≤ q
  positive : 1 ≤ j
  surplus : j ≤ h - 1

/-- The complete original graph contract, with the proper floor starting at h. -/
structure Host (h q j e : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) : Prop where
  parameters : Parameters h q j e
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  bipartite : G.IsBipartiteWith (A : Set V) (B : Set V)
  card : #B = #A + j
  order : 2 * q ≤ Fintype.card V
  min_degree : ∀ v : V, q ≤ G.degree v
  cap_degree : ∀ v : V, G.degree v ≤ 2 * q - 2
  highA : ∀ v ∈ A, q + 2 * h - 4 ≤ G.degree v
  edges : G.edgeSet.ncard + constant h q e = (q - 1) * Fintype.card V
  proper : ∀ X : Finset V, h ≤ #X → #X < Fintype.card V →
    (constant h q e : ℤ) - e + 1 ≤ ((q : ℤ) - 1) * #X -
      ((G.induce (X : Set V)).edgeSet.ncard : ℤ)

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Paired original incidence fields, derived from Host rather than supplied at the endpoint. -/
structure Data (h q j e : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Prop where
  parameters : Parameters h q j e
  disjoint : Disjoint A B
  card : #B = #A + j
  minA : ∀ a ∈ A, q ≤ dg G B a
  capA : ∀ a ∈ A, dg G B a ≤ 2 * q - 2
  minB : ∀ b ∈ B, q ≤ dg G A b
  capB : ∀ b ∈ B, dg G A b ≤ 2 * q - 2
  highA : ∀ v ∈ A, q + 2 * h - 4 ≤ dg G B v
  deficient : deficiency (2 * (q : ℤ) - 2) G B A =
    (h : ℤ) * q - offset h e - ((q : ℤ) - 1) * j
  sparse : ∀ X ⊆ A, ∀ Y ⊆ B, h ≤ #X + #Y → #X + #Y < #A + #B →
    2 * ((h : ℤ) * q - offset h e - e + 1) ≤ potential (2 * (q : ℤ) - 2) G X Y

/-- Exact local cost-one escape required from original paired incidence.
The full Data premise is discharged internally from Host. Strict maximum height
is a local selection made inside the proof, not an endpoint premise. -/
def PetalEscapeClaim : Prop :=
  ∀ (h q j e : ℕ) (A B K ban : Finset V), Data h q j e G A B →
    K ⊆ B → q - 1 ≤ #K → 2 ≤ thetaJ q j G A B K →
    (∀ T ⊆ B, K ⊆ T → K ≠ T → thetaJ q j G A B T ≤ thetaJ q j G A B K - 1) →
    ban ⊆ B \ K → #ban ≤ 3 * h →
    ∃ z ∈ B \ K, z ∉ ban ∧
      ∀ P ⊆ B \ K, z ∈ P → 2 ≤ extensionCost q j G A B K P

end Erdos585.R882.Positive
