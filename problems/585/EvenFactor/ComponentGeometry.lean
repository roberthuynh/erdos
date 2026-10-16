import EvenFactor.RootWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset SimpleGraph Function
namespace Erdos585.EvenFactorCriterion
open QB4 FactorMatching
universe u
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma closed_mem_of_reachable (W : Finset V)
    (hclosed : ∀ x ∈ W, ∀ y, G.Adj x y → y ∈ W)
    (v w : V) (hv : v ∈ W) (h : G.Reachable v w) : w ∈ W := by
  have aux : ∀ {a b : V}, (p : G.Walk a b) → a ∈ W → b ∈ W := by
    intro a b p
    induction p with
    | nil => exact fun ha => ha
    | cons hadj p ih => exact fun ha => ih (hclosed _ ha _ hadj)
  exact aux h.some hv

/-- Actual paths and edge closure pay the complete component support. -/
theorem component_of_closed_reachable (W : Finset V) (hne : W.Nonempty)
    (hclosed : ∀ x ∈ W, ∀ y, G.Adj x y → y ∈ W)
    (hreach : ∀ x ∈ W, ∀ y ∈ W, G.Reachable x y) :
    ∃ C : G.ConnectedComponent, C.supp.toFinset = W := by
  obtain ⟨v,hv⟩ := hne
  refine ⟨G.connectedComponentMk v, ?_⟩
  ext w
  simp only [Set.mem_toFinset, ConnectedComponent.mem_supp_iff]
  constructor
  · intro hw
    exact closed_mem_of_reachable G W hclosed v w hv (ConnectedComponent.exact hw).symm
  · intro hw
    exact ConnectedComponent.sound (hreach w hw v hv)

variable (q : ℕ)

/-- Each literal lifted vertex has an original gadget path to the same root. -/
theorem lifted_reaches_root (hq : 0 < q) (hmin : ∀ v : V, q ≤ G.degree v)
    (S T : Finset V)
    (C : (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent)
    (x : RemainingVertex q G S T)
    (hx : x ∈ liftedRemaining q G S T (componentVerts G (univ \ (S ∪ T)) C)) :
    (remainingGraph q G S T).Reachable x (rootR q G hq S T C.out) := by
  let A := componentVerts G (univ \ (S ∪ T)) C
  have toRoot (r : ((univ \ (S ∪ T) : Finset V) : Set V)) (hr : r ∈ C.supp) :
      (remainingGraph q G S T).Reachable (rootR q G hq S T r)
        (rootR q G hq S T C.out) :=
    rootR_reachable q G hq S T r C.out (C.reachable_of_mem_supp hr C.out_eq)
  simp only [mem_liftedRemaining] at hx
  rcases x with ⟨x,hxr⟩
  cases x with
  | inl s =>
    obtain ⟨hvr,hvC⟩ := (mem_componentVerts_iff G _ C s.1).mp
      ((mem_lifted_slot q G S A s.1 s.2).mp hx)
    let r : ((univ \ (S ∪ T) : Finset V) : Set V) := ⟨s.1,hvr⟩
    have hn : (G.neighborFinset s.1).Nonempty := card_pos.mp (by
      rw [card_neighborFinset_eq_degree]
      exact lt_of_lt_of_le hq (hmin s.1))
    obtain ⟨w,hw⟩ := hn
    have hadj : G.Adj s.1 w := (G.mem_neighborFinset _ _).mp hw
    have hfirst : (remainingGraph q G S T).Adj ⟨Sum.inl s,hxr⟩
        (stubR q G S T r w hadj) := rfl
    exact hfirst.reachable.trans ((stubR_to_rootR q G hq S T r w hadj).reachable.trans
      (toRoot r hvC))
  | inr d =>
    rcases (mem_lifted_stub q G S A d).mp hx with hdA | ⟨_,hdC⟩
    · obtain ⟨hvr,hvC⟩ := (mem_componentVerts_iff G _ C d.fst).mp hdA
      let r : ((univ \ (S ∪ T) : Finset V) : Set V) := ⟨d.fst,hvr⟩
      have hfirst : (remainingGraph q G S T).Adj ⟨Sum.inr d,hxr⟩
          (rootR q G hq S T r) := rfl
      exact hfirst.reachable.trans (toRoot r hvC)
    · obtain ⟨hvr,hvC⟩ := (mem_componentVerts_iff G _ C d.snd).mp hdC
      let r : ((univ \ (S ∪ T) : Finset V) : Set V) := ⟨d.snd,hvr⟩
      have hfirst : (remainingGraph q G S T).Adj ⟨Sum.inr d,hxr⟩
          (stubR q G S T r d.fst d.adj.symm) := by
        change (⟨(d.snd,d.fst),d.adj.symm⟩ : G.Dart) = d.symm
        apply Dart.ext
        rfl
      exact hfirst.reachable.trans
        ((stubR_to_rootR q G hq S T r d.fst d.adj.symm).reachable.trans (toRoot r hvC))

/-- Each original remainder component lifts to an ACTUAL remaining gadget component. -/
theorem lifted_actual_component (hq : 0 < q) (hmin : ∀ v : V, q ≤ G.degree v)
    (S T : Finset V) (hST : Disjoint S T)
    (C : (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent) :
    ∃ D : (remainingGraph q G S T).ConnectedComponent,
      D.supp = (liftedRemaining q G S T (componentVerts G (univ \ (S ∪ T)) C) : Set _) := by
  let A := componentVerts G (univ \ (S ∪ T)) C
  have hC : (C.out : V) ∈ A :=
    (mem_componentVerts_iff G _ C C.out).mpr ⟨C.out.property,C.out_eq⟩
  have hr : rootR q G hq S T C.out ∈ liftedRemaining q G S T A := by
    simp [rootR, hC]
  obtain ⟨D,hD⟩ := component_of_closed_reachable (remainingGraph q G S T) _ ⟨_,hr⟩
    (fun x hx y hadj => liftedRemaining_closed q G S T hST C x y hx hadj)
    (fun x hx y hy => (lifted_reaches_root G q hq hmin S T C x hx).trans
      (lifted_reaches_root G q hq hmin S T C y hy).symm)
  refine ⟨D,?_⟩
  simpa only [Set.coe_toFinset] using congrArg (fun W : Finset (RemainingVertex q G S T) => (W : Set (RemainingVertex q G S T))) hD

end Erdos585.EvenFactorCriterion
