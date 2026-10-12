import R804.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section

namespace Erdos585.R804
universe u

open Classical in
/-- Literal original inputs alone produce the exact paid proper original subgraph. -/
theorem fourth_surplus_original {V : Type u} [Fintype V] (h q j ξ : ℕ)
    (G : SimpleGraph V) (A B : Finset V)
    (height : 5≤h) (large : 1024*(h+1)^2≤q) (surplus : j=h-4)
    (lower : h^2+5*h+8-h+2≤ξ) (upper : ξ≤h^2+5*h+8-1)
    (disjoint : Disjoint A B) (cover : A∪B=univ)
    (bipartite : G.IsBipartiteWith (A:Set V) (B:Set V))
    (card : #B=#A+j) (order : 2*q≤Fintype.card V)
    (min_degree : ∀ v:V,q≤G.degree v) (cap_degree : ∀ v:V,G.degree v≤2*q-2)
    (edges : G.edgeSet.ncard+(h*q-ξ)=(q-1)*Fintype.card V)
    (proper : ∀ X : Finset V, h≤#X → #X<Fintype.card V →
      ((h*q-ξ:ℕ):ℤ)+1≤((q:ℤ)-1)*#X-
        ((G.induce (X:Set V)).edgeSet.ncard:ℤ)) :
    ∃ S O : Finset V, S⊆A ∧ O⊆B ∧ #S≤8*h-1 ∧
      #O=j+#S ∧ #O≤8*h+j-1 ∧ #O<9*h ∧
      q≤#(A\S) ∧ #(A\S)=#(B\O) ∧
      ((S=∅ ∧ #O=j) ∨ (1≤#S ∧ #(A\S)<#A ∧ #(B\O)<#B)) ∧
      ∃ H : G.Subgraph, H.verts=(↑((A\S)∪(B\O)):Set V) ∧
        H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧ H.verts⊂(Set.univ : Set V) := by
  exact variable_offset_surplus h q j ξ G A B
    ⟨by omega,large,Or.inr surplus,by omega,lower,upper,disjoint,cover,bipartite,card,order,
      min_degree,cap_degree,edges,proper⟩

open Classical in
/-- Literal original inputs alone produce the exact paid proper original subgraph. -/
theorem third_surplus_original {V : Type u} [Fintype V] (h q j ξ : ℕ)
    (G : SimpleGraph V) (A B : Finset V)
    (height : 4≤h) (large : 1024*(h+1)^2≤q) (surplus : j=h-3)
    (lower : h^2+5*h+8-h+2≤ξ) (upper : ξ≤h^2+5*h+8-1)
    (disjoint : Disjoint A B) (cover : A∪B=univ)
    (bipartite : G.IsBipartiteWith (A:Set V) (B:Set V))
    (card : #B=#A+j) (order : 2*q≤Fintype.card V)
    (min_degree : ∀ v:V,q≤G.degree v) (cap_degree : ∀ v:V,G.degree v≤2*q-2)
    (edges : G.edgeSet.ncard+(h*q-ξ)=(q-1)*Fintype.card V)
    (proper : ∀ X : Finset V, h≤#X → #X<Fintype.card V →
      ((h*q-ξ:ℕ):ℤ)+1≤((q:ℤ)-1)*#X-
        ((G.induce (X:Set V)).edgeSet.ncard:ℤ)) :
    ∃ S O : Finset V, S⊆A ∧ O⊆B ∧ #S≤8*h-1 ∧
      #O=j+#S ∧ #O≤8*h+j-1 ∧ #O<9*h ∧
      q≤#(A\S) ∧ #(A\S)=#(B\O) ∧
      ((S=∅ ∧ #O=j) ∨ (1≤#S ∧ #(A\S)<#A ∧ #(B\O)<#B)) ∧
      ∃ H : G.Subgraph, H.verts=(↑((A\S)∪(B\O)):Set V) ∧
        H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧ H.verts⊂(Set.univ : Set V) := by
  exact variable_offset_surplus h q j ξ G A B
    ⟨by omega,large,Or.inl surplus,by omega,lower,upper,disjoint,cover,bipartite,card,order,
      min_degree,cap_degree,edges,proper⟩

end Erdos585.R804

#print axioms Erdos585.R804.third_surplus_original
#print axioms Erdos585.R804.fourth_surplus_original
