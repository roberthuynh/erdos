import AllHThirdExistence.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHThirdExistence
universe u

/-- Literal raw-field caller, preserving every original Host clause and offset. -/
theorem literal_host_caller (h q j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V)
    (hh : 4≤h) (hq : 1024*(h+1)^2≤q) (hj : j=h-3)
    (hdis : Disjoint A B) (hcover : A∪B=univ)
    (hbip : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcard : #B=#A+j) (horder : 2*q≤Fintype.card V)
    (hmin : ∀v:V,q≤G.degree v) (hcap : ∀v:V,G.degree v≤2*q-2)
    (hedges : G.edgeSet.ncard+(h*q-(h^2+5*h+8))=(q-1)*Fintype.card V)
    (hproper : ∀X:Finset V,h≤#X→#X<Fintype.card V→
      ((h*q-(h^2+5*h+8):ℕ):ℤ)+1≤((q:ℤ)-1)*#X-
        ((G.induce (X:Set V)).edgeSet.ncard:ℤ)) :
    ∃ S O : Finset V, S⊆A ∧ O⊆B ∧ #S≤8*h-1 ∧
      #O=j+#S ∧ #O≤8*h+j-1 ∧ #O<9*h ∧
      q≤#(A\S) ∧ #(A\S)=#(B\O) ∧
      ∃ H : G.Subgraph, H.verts=(↑((A\S)∪(B\O)):Set V) ∧
        H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧ H.verts⊂(Set.univ : Set V) := by
  exact third_surplus h q j G A B
    ⟨⟨hh,hq,hj⟩,hdis,hcover,hbip,hcard,horder,hmin,hcap,hedges,hproper⟩

end Erdos585.AllHThirdExistence
