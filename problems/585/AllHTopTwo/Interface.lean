import H3Unequal.Main

/-! R109: literal all-height top-two-surplus interface.
The original host supplies neither a cut selector nor a factor. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHTopTwo
open QB4 B5 L34 H3Unequal
universe u

def offset (h : ℕ) : ℕ := h ^ 2 + 5 * h + 8

def constant (h q : ℕ) : ℕ := h * q - offset h

structure Parameters (h q j : ℕ) : Prop where
  height : 3 ≤ h
  large : 1024 * (h + 1) ^ 2 ≤ q
  branch : j = h - 2 ∨ j = h - 1

/-- The complete original graph contract, with the proper floor starting at h. -/
structure Host (h q j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) : Prop where
  parameters : Parameters h q j
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  bipartite : G.IsBipartiteWith (A : Set V) (B : Set V)
  card : #B = #A + j
  order : 2 * q ≤ Fintype.card V
  min_degree : ∀ v : V, q ≤ G.degree v
  cap_degree : ∀ v : V, G.degree v ≤ 2 * q - 2
  edges : G.edgeSet.ncard + constant h q = (q - 1) * Fintype.card V
  proper : ∀ X : Finset V, h ≤ #X → #X < Fintype.card V →
    (constant h q : ℤ) + 1 ≤ ((q : ℤ) - 1) * #X -
      ((G.induce (X : Set V)).edgeSet.ncard : ℤ)

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Paired original incidence fields, derived from Host rather than supplied at the endpoint. -/
structure Data (h q j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Prop where
  parameters : Parameters h q j
  disjoint : Disjoint A B
  card : #B = #A + j
  minA : ∀ a ∈ A, q ≤ dg G B a
  capA : ∀ a ∈ A, dg G B a ≤ 2 * q - 2
  minB : ∀ b ∈ B, q ≤ dg G A b
  capB : ∀ b ∈ B, dg G A b ≤ 2 * q - 2
  deficient : deficiency (2 * (q : ℤ) - 2) G B A =
    (h : ℤ) * q - offset h - ((q : ℤ) - 1) * j
  sparse : ∀ X ⊆ A, ∀ Y ⊆ B, h ≤ #X + #Y → #X + #Y < #A + #B →
    2 * ((h : ℤ) * q - offset h + 1) ≤ potential (2 * (q : ℤ) - 2) G X Y

/-- Exact local cost-one escape required from original paired incidence.
The full Data premise is discharged internally from Host. Strict maximum height
is a local selection made inside the proof, not an endpoint premise. -/
def PetalEscapeClaim : Prop :=
  ∀ (h q j : ℕ) (A B K ban : Finset V), Data h q j G A B →
    K ⊆ B → q - 1 ≤ #K → 2 ≤ thetaJ q j G A B K →
    (∀ T ⊆ B, K ⊆ T → K ≠ T → thetaJ q j G A B T ≤ thetaJ q j G A B K - 1) →
    ban ⊆ B \ K → #ban ≤ 3 * h →
    ∃ z ∈ B \ K, z ∉ ban ∧
      ∀ P ⊆ B \ K, z ∈ P → 2 ≤ extensionCost q j G A B K P

end Erdos585.AllHTopTwo
