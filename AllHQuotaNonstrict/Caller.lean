/-
Copyright 2026 Robert Huynh.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import AllHQuotaNonstrict.Main

/-! R280 fully expanded original host caller. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section
namespace Erdos585.AllHQuotaNonstrict
open QB4 B5 L34 H3Unequal
universe u

open Classical in
/-- The literal integer edge and proper-floor equations produce the SAME omission and factor. -/
theorem original_host_caller (h q j ξ : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V)
    (height : 3 ≤ h) (large : 1024*(h+1)^2 ≤ q)
    (positive : 1 ≤ j) (surplus : j ≤ h-1)
    (lower : h^2+3*h+8 ≤ ξ) (upper : ξ ≤ h^2+5*h+8)
    (disjoint : Disjoint A B) (cover : A∪B=univ)
    (bipartite : G.IsBipartiteWith (A : Set V) (B : Set V))
    (card : #B=#A+j) (order : 2*q ≤ Fintype.card V)
    (min_degree : ∀ v : V, q ≤ G.degree v)
    (cap_degree : ∀ v : V, G.degree v ≤ 2*q-2)
    (edges : (G.edgeSet.ncard : ℤ)=((q : ℤ)-1)*Fintype.card V-((h : ℤ)*q-ξ))
    (proper : ∀ X : Finset V, h ≤ #X → #X < Fintype.card V →
      (h : ℤ)*q-ξ ≤ ((q : ℤ)-1)*#X-
        ((G.induce (X : Set V)).edgeSet.ncard : ℤ))
    (quota : ∃ O0 : Finset V, O0⊆B ∧ #O0=j ∧ ∀ x∈A,
      G.degree x≤q+2*h-5 → dg G O0 x≤G.degree x-q) :
    ∃ O : Finset V, O ⊆ B ∧ #O=j ∧
      (∀ T ⊆ B, O ⊆ T → thetaJ q j G A B T ≤ 0) ∧
      ∃ H : G.Subgraph, H.verts=(↑(A∪(B\O)) : Set V) ∧
        H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  classical
  have p : Parameters h q j ξ := ⟨height,large,positive,surplus,lower,upper⟩
  have hq := p.q_pos
  have hconst := p.constant_cast
  apply uniform_quota_nonstrict h q j ξ G A B ?_ quota
  refine ⟨p,disjoint,cover,bipartite,card,order,min_degree,cap_degree,?_,?_⟩
  · have hqm : q-1+1=q := by omega
    zify at hqm ⊢
    nlinarith
  · intro X hX hproper
    have hf := proper X hX hproper
    omega

end Erdos585.AllHQuotaNonstrict
