import AllHThirdFragileFree.Numeric

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.AllHThirdQuotaFailure
open QB4 B5 L34 H3Unequal
open AllHThirdFragileFree (Host offset constant)
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)

/-- The actual original high-scar vertices; the strict threshold is intentional. -/
def marked (q : ℕ) : Finset V :=
  univ.filter (fun v => q < 4 * ((2*q-2)-G.degree v))

/-- Every prescribed balancing choice, with no flow or successful factor input. -/
structure Cleanup (q : ℕ) (A B AH BH : Finset V) : Prop where
  left : AH ⊆ A \ marked G q
  right : BH ⊆ B \ marked G q
  balanced : #AH = #BH
  size : #AH = min #(A \ marked G q) #(B \ marked G q)

/-- Literal failed quota from the two original neighborhoods and degrees. -/
def QuotaFailure (q j : ℕ) (B : Finset V) (x y : V) : Prop :=
  #(B.filter (fun z => ¬ G.Adj x z ∧ ¬ G.Adj y z)) +
    (G.degree x-q) + (G.degree y-q) < j

/-- Exact support and all omission counts, with actual original units. -/
def Conclusion (h q j : ℕ) (A B AH BH : Finset V) (x y : V) : Prop :=
  q ≤ #AH ∧ #AH < 2*q ∧ x ∈ A \ AH ∧ y ∈ A \ AH ∧
  2 ≤ #(A \ AH) ∧ #(A \ AH) ≤ 8*h-1 ∧
  #(B \ BH) = j + #(A \ AH) ∧ #(B \ BH) ≤ 8*h+j-1 ∧ #(B \ BH) < 9*h ∧
  FactorOn q G AH BH ∧
  ∃ H : G.Subgraph, H.verts = (↑(AH ∪ BH) : Set V) ∧
    H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q

end Erdos585.AllHThirdQuotaFailure
