import H3Unequal.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
local instance r804DecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Erdos585.R804
open QB4 B5 L34 H3Unequal
universe u

def offset (h : ℕ) : ℕ := h^2+5*h+8
def constant (h q ξ : ℕ) : ℕ := h*q-ξ

/-- Literal fourth-surplus original host, including every strict proper floor. -/
structure Host (h q j ξ : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) : Prop where
  height : 4 ≤ h
  large : 1024*(h+1)^2 ≤ q
  surplus : j=h-3 ∨ j=h-4
  positive : 1 ≤ j
  lower : h^2+5*h+8-h+2 ≤ ξ
  upper : ξ ≤ h^2+5*h+8-1
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  bipartite : G.IsBipartiteWith (A : Set V) (B : Set V)
  card : #B = #A+j
  order : 2*q ≤ Fintype.card V
  min_degree : ∀ v : V, q ≤ G.degree v
  cap_degree : ∀ v : V, G.degree v ≤ 2*q-2
  edges : G.edgeSet.ncard + constant h q ξ = (q-1)*Fintype.card V
  proper : ∀ X : Finset V, h ≤ #X → #X < Fintype.card V →
    (constant h q ξ : ℤ)+1 ≤ ((q : ℤ)-1)*#X -
      ((G.induce (X : Set V)).edgeSet.ncard : ℤ)

variable {V : Type u} [Fintype V] (G : SimpleGraph V)

def marked (q : ℕ) : Finset V :=
  univ.filter (fun v => q < 4*((2*q-2)-G.degree v))

structure Cleanup (q : ℕ) (A B AH BH : Finset V) : Prop where
  left : AH ⊆ A \ marked G q
  right : BH ⊆ B \ marked G q
  balanced : #AH = #BH
  size : #AH = min #(A \ marked G q) #(B \ marked G q)

/-- Failure of the actual simultaneous deletion quotas, including redundant rows. -/
def Failed (q j : ℕ) (B I : Finset V) : Prop :=
  ¬ ∃ O : Finset V, O ⊆ B ∧ #O=j ∧
    ∀ v∈I, #(O.filter (G.Adj v)) ≤ G.degree v-q

def ThreeFailure (q j : ℕ) (B : Finset V) (x y z : V) : Prop :=
  Failed G q j B {x,y,z}

structure MinimalFailed (q j : ℕ) (B T I : Finset V) : Prop where
  subset : I ⊆ T
  failed : Failed G q j B I
  minimal : ∀ J ⊆ I, #J < #I → ¬ Failed G q j B J

/-- The minimum is taken over actual retained cross-degrees on both shores. -/
def ActualMinimum (d : ℕ) (P Q : Finset V) : Prop :=
  (∀ v∈P, d≤dg G Q v) ∧ (∀ v∈Q, d≤dg G P v) ∧
  ((∃ v∈P, dg G Q v=d) ∨ (∃ v∈Q, dg G P v=d))

/-- Exact original support, omissions, essential constraints, and all active degrees. -/
structure Conclusion (h q j : ℕ) (A B AH BH T : Finset V) : Prop where
  size_lower : q ≤ #AH
  size_upper : 8*#AH ≤ 25*q
  degree_left : ∀ v∈AH, 13*q ≤ 8*dg G BH v
  degree_right : ∀ v∈BH, 13*q ≤ 8*dg G AH v
  omitted_positive : 1 ≤ #(A\AH)
  omitted_bound : #(A\AH) ≤ 8*h-1
  omitted_equal : #(B\BH) = j+#(A\AH)
  omitted_right_bound : #(B\BH) ≤ 8*h+j-1
  omitted_right_small : #(B\BH) < 9*h
  shore_bound : #A ≤ 3*q+3*h
  essential : ∃ I, MinimalFailed G q j B T I ∧ I.Nonempty ∧ #I≤3 ∧
    (∀ v∈I, G.degree v-q<j) ∧ I ⊆ A\AH
  dense_certificate : ∃ δ : ℕ, ActualMinimum G δ AH BH ∧ 13*q≤8*δ ∧ δ<2*q ∧
    (q:ℤ)^2≤16*((#AH:ℤ)*(2*(δ:ℤ)-#AH)-(2*(q:ℤ)-δ)^2)
  strict_left : #AH<#A
  strict_right : #BH<#B
  factor : FactorOn q G AH BH
  subgraph : ∃ H : G.Subgraph, H.verts=(↑(AH∪BH):Set V) ∧
    H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q

end Erdos585.R804
