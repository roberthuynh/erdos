import Openmath.Proofs.QB4.Statement

/- 


-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.B5
open QB4
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def potential (D : ℤ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) : ℤ := D * ((#X : ℤ) + #Y) - 2 * (ec G X Y : ℤ)

def deficiency (D : ℤ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (W X : Finset V) : ℤ := ∑ a ∈ X, (D - (dg G W a : ℤ))

def FactorOn (q : ℕ) (G : SimpleGraph V) (U W : Finset V) : Prop :=
  ∃ F : Finset (V × V), F ⊆ U ×ˢ W ∧ (∀ x ∈ F, G.Adj x.1 x.2) ∧
    (∀ u ∈ U, #{x ∈ F | x.1 = u} = q) ∧
    (∀ w ∈ W, #{x ∈ F | x.2 = w} = q)

def RegularPairs (q : ℕ) (G : SimpleGraph V) (U W : Finset V) : Prop :=
  ∃ F : Finset (V × V), F.Nonempty ∧ F ⊆ U ×ˢ W ∧
    (∀ x ∈ F, G.Adj x.1 x.2) ∧
    (∀ u, #{x ∈ F | x.1 = u} = 0 ∨ #{x ∈ F | x.1 = u} = q) ∧
    (∀ w, #{x ∈ F | x.2 = w} = 0 ∨ #{x ∈ F | x.2 = w} = q)

def row (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (W T : Finset V) (a : V) : ℤ := (dg G T a : ℤ) - (dg G W a : ℤ) + q

def theta (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W T : Finset V) : ℤ := (q : ℤ) - q * #T + ∑ a ∈ U, max 0 (row q G W T a)

def canonical (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W T : Finset V) : Finset V := U.filter fun a => 0 < row q G W T a

structure R2Input (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V) : Prop where
  disjoint : Disjoint U W
  card : #W = #U + 1
  minU : ∀ a ∈ U, q ≤ dg G W a
  capU : ∀ a ∈ U, dg G W a ≤ 2 * q - 2
  minW : ∀ w ∈ W, q ≤ dg G U w
  capW : ∀ w ∈ W, dg G U w ≤ 2 * q - 2
  deficient : deficiency (2 * (q : ℤ) - 2) G W U = 1
  sparse : ∀ X ⊆ U, ∀ T ⊆ W, 3 ≤ #X + #T → #X + #T < #U + #W →
    2 * (q : ℤ) + 2 ≤ potential (2 * (q : ℤ) - 2) G X T

/- -/
def R1Claim : Prop :=
  ∀ (q : ℕ), 1 ≤ q → ∀ (U W M N : Finset V),
    (∀ a ∈ U, q ≤ dg G W a) →
    (∑ a ∈ canonical q G U W M ∩ canonical q G U W N,
      max 0 (((dg G W a : ℤ) - q) - dg G (M ∩ N) a)) ≤
    theta q G U W (M ∪ N) + theta q G U W (M ∩ N) -
      theta q G U W M - theta q G U W N

/-- Actual original omission and actual spanning factor, no selector input. -/
def R2Claim : Prop :=
  ∀ (q : ℕ), 5 ≤ q → ∀ (U W : Finset V), R2Input q G U W →
    ∃ w ∈ W, FactorOn q G U (W.erase w)

open scoped Classical in
/-- Bare finite graph endpoint. -/
def Endpoint : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), G.IsBipartite →
    G.maxDegree ≤ 8 → 10 ≤ Fintype.card V →
    4 * Fintype.card V ≤ G.edgeSet.ncard + 5 →
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 5

end Erdos585.B5
