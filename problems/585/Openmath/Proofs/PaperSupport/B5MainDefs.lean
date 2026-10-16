import Openmath.Proofs.PaperSupport.B5Selector

/- -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.B5
open QB4
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def Sparse8 (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) : Prop :=
  ∀ X ⊆ U, ∀ Y ⊆ W, 3 ≤ #X + #Y → #X + #Y < #U + #W →
    12 ≤ potential 8 G X Y

structure BalancedInput (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q : Finset V) : Prop where
  disjoint : Disjoint P Q
  balanced : #P = #Q
  minP : ∀ p ∈ P, 5 ≤ dg G Q p
  capP : ∀ p ∈ P, dg G Q p ≤ 8
  minQ : ∀ q ∈ Q, 5 ≤ dg G P q
  capQ : ∀ q ∈ Q, dg G P q ≤ 8
  deficientP : deficiency 8 G Q P = 5
  deficientQ : deficiency 8 G P Q = 5
  sparse : Sparse8 G P Q

def DensePairClaim : Prop :=
  ∀ (U W : Finset V), Disjoint U W → 10 ≤ #U + #W →
    (∀ u ∈ U, dg G W u ≤ 8) → (∀ w ∈ W, dg G U w ≤ 8) →
    4 * (#U + #W) ≤ ec G U W + 5 → RegularPairs 5 G U W

open scoped Classical in
/-- Original exact edge thinning on the same ambient vertex type. -/
def ThinContract (U W : Finset V) (m : ℕ) : Prop :=
  ∃ K : SimpleGraph V, K ≤ G ∧ ec K U W = m

end Erdos585.B5
