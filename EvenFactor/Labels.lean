import EvenFactor.StubPair

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset SimpleGraph
namespace Erdos585.EvenFactorCriterion
open QB4 FactorMatching
universe u
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Labels pay resources on original vertices, original directed edges, and actual original
remainder components. No compatible profile or independent selector is an input. -/
abbrev OddLabel (S T : Finset V) :=
  (({v : V // v ∈ T} × Fin q) ⊕ {d : G.Dart // d ∈ crossDarts G S T}) ⊕
    {C : (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent //
      Odd (ec G (componentVerts G (univ \ (S ∪ T)) C) T)}

lemma oddLabel_card (S T : Finset V) : Nat.card (OddLabel q G S T) =
    q * #T + ec G S T + oddTo G T (univ \ (S ∪ T)) := by
  rw [Nat.card_sum, Nat.card_sum, Nat.card_prod]
  change Nat.card {v : V // v ∈ T} * Nat.card (Fin q) +
    Nat.card {d : G.Dart // d ∈ crossDarts G S T} + oddTo G T (univ \ (S ∪ T)) = _
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_fin,
    crossDarts_card]
  ring

/-- A label maps to the actual component containing its original physical vertex. -/
def labelComponent (hq : 0 < q) (S T : Finset V) (hST : Disjoint S T) :
    OddLabel q G S T → (remainingGraph q G S T).ConnectedComponent
  | Sum.inl (Sum.inl vi) => (remainingGraph q G S T).connectedComponentMk
      (keptSlot q G S T vi.1.val vi.2 (fun hs => Finset.disjoint_left.mp hST hs vi.1.property))
  | Sum.inl (Sum.inr d) => (remainingGraph q G S T).connectedComponentMk
      (keptStub q G S T d.val (fun ht => Finset.disjoint_left.mp hST
        ((mem_crossDarts G S T d.val).mp d.property).1 ht))
  | Sum.inr C => (remainingGraph q G S T).connectedComponentMk (rootR q G hq S T C.val.out)

/-- A complete physical lift identifies its component and pays original odd parity. -/
theorem odd_lift_member (hq : 0 < q) (heven : Even q)
    (hmin : ∀ v : V, q ≤ G.degree v) (S T : Finset V) (hST : Disjoint S T)
    (D : (remainingGraph q G S T).ConnectedComponent) (hD : Odd D.supp.ncard)
    (C : (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent)
    (hx : D.out ∈ liftedRemaining q G S T (componentVerts G (univ \ (S ∪ T)) C)) :
    Odd (ec G (componentVerts G (univ \ (S ∪ T)) C) T) ∧
      (remainingGraph q G S T).connectedComponentMk (rootR q G hq S T C.out) = D := by
  obtain ⟨D',hsupp⟩ := lifted_actual_component G q hq hmin S T hST C
  have hD' : D = D' := ConnectedComponent.eq_of_common_vertex D.out_eq (by
    rw [hsupp]
    exact hx)
  have hcount : D.supp.ncard = #(liftedVertices q G S (componentVerts G (univ \ (S ∪ T)) C)) := by
    rw [hD',hsupp,Set.ncard_coe_finset,liftedRemaining_card q G S T hST C]
  refine ⟨(lifted_component_vertices_parity q G heven S T hST C).mp (hcount ▸ hD),?_⟩
  have hreach := lifted_reaches_root G q hq hmin S T C D.out hx
  exact (ConnectedComponent.sound hreach).symm.trans D.out_eq

end Erdos585.EvenFactorCriterion
