import EvenFactor.Labels

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

lemma odd_lift_labeled (hq : 0 < q) (heven : Even q)
    (hmin : ∀ v : V, q ≤ G.degree v) (S T : Finset V) (hST : Disjoint S T)
    (D : (remainingGraph q G S T).ConnectedComponent) (hD : Odd D.supp.ncard)
    (C : (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent)
    (hx : D.out ∈ liftedRemaining q G S T (componentVerts G (univ \ (S ∪ T)) C)) :
    ∃ l : OddLabel q G S T, labelComponent q G hq S T hST l = D := by
  obtain ⟨ho,heq⟩ := odd_lift_member q G hq heven hmin S T hST D hD C hx
  exact ⟨Sum.inr ⟨C,ho⟩,heq⟩

/-- Every actual odd remaining component receives one actual original resource label. -/
theorem odd_component_labeled (hq : 0 < q) (heven : Even q)
    (hmin : ∀ v : V, q ≤ G.degree v) (S T : Finset V) (hST : Disjoint S T)
    (D : (remainingGraph q G S T).ConnectedComponent) (hD : Odd D.supp.ncard) :
    ∃ l : OddLabel q G S T, labelComponent q G hq S T hST l = D := by
  cases hval : D.out.val with
  | inl s =>
    have hnS : s.1 ∉ S := by
      intro hs
      apply D.out.property
      rw [hval]
      exact (mem_canonical_slot q G S T s.1 s.2).mpr hs
    by_cases ht : s.1 ∈ T
    · have hout : D.out = keptSlot q G S T s.1 s.2 hnS := Subtype.ext hval
      refine ⟨Sum.inl (Sum.inl (⟨s.1,ht⟩,s.2)),?_⟩
      change (remainingGraph q G S T).connectedComponentMk _ = D
      rw [← hout]
      exact D.out_eq
    · have hr : s.1 ∈ univ \ (S ∪ T) := by simp [hnS,ht]
      let r : ((univ \ (S ∪ T) : Finset V) : Set V) := ⟨s.1,hr⟩
      let C := (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).connectedComponentMk r
      apply odd_lift_labeled q G hq heven hmin S T hST D hD C
      rw [mem_liftedRemaining, hval]
      apply (mem_lifted_slot q G S _ s.1 s.2).mpr
      exact (mem_componentVerts_iff G _ C s.1).mpr ⟨hr,(ConnectedComponent.mem_supp_iff _ _).mpr rfl⟩
  | inr d =>
    have hnT : d.fst ∉ T := by
      intro ht
      apply D.out.property
      rw [hval]
      exact (mem_canonical_stub q G S T d).mpr ht
    by_cases hs : d.fst ∈ S
    · by_cases ht : d.snd ∈ T
      · have hout : D.out = keptStub q G S T d hnT := Subtype.ext hval
        refine ⟨Sum.inl (Sum.inr ⟨d,(mem_crossDarts G S T d).mpr ⟨hs,ht⟩⟩),?_⟩
        change (remainingGraph q G S T).connectedComponentMk _ = D
        rw [← hout]
        exact D.out_eq
      · by_cases heS : d.snd ∈ S
        · have hout : D.out = keptStub q G S T d hnT := Subtype.ext hval
          have hno := stubSS_even_component q G S T hST d hs heS
          have hmk : (remainingGraph q G S T).connectedComponentMk (keptStub q G S T d hnT) = D := by
            rw [← hout]
            exact D.out_eq
          exact False.elim (hno (hmk ▸ hD))
        · have hr : d.snd ∈ univ \ (S ∪ T) := by simp [heS,ht]
          let r : ((univ \ (S ∪ T) : Finset V) : Set V) := ⟨d.snd,hr⟩
          let C := (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).connectedComponentMk r
          apply odd_lift_labeled q G hq heven hmin S T hST D hD C
          rw [mem_liftedRemaining, hval]
          apply (mem_lifted_stub q G S _ d).mpr
          exact Or.inr ⟨hs,(mem_componentVerts_iff G _ C d.snd).mpr
            ⟨hr,(ConnectedComponent.mem_supp_iff _ _).mpr rfl⟩⟩
    · have hr : d.fst ∈ univ \ (S ∪ T) := by simp [hs,hnT]
      let r : ((univ \ (S ∪ T) : Finset V) : Set V) := ⟨d.fst,hr⟩
      let C := (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).connectedComponentMk r
      apply odd_lift_labeled q G hq heven hmin S T hST D hD C
      rw [mem_liftedRemaining, hval]
      apply (mem_lifted_stub q G S _ d).mpr
      exact Or.inl ((mem_componentVerts_iff G _ C d.fst).mpr
        ⟨hr,(ConnectedComponent.mem_supp_iff _ _).mpr rfl⟩)

/-- The simultaneous charge bounds ACTUAL odd components without independently chosen marks. -/
theorem remaining_odd_bound (hq : 0 < q) (heven : Even q)
    (hmin : ∀ v : V, q ≤ G.degree v) (S T : Finset V) (hST : Disjoint S T) :
    (remainingGraph q G S T).oddComponents.ncard ≤
      q * #T + ec G S T + oddTo G T (univ \ (S ∪ T)) := by
  let f : ((remainingGraph q G S T).oddComponents : Set _) → OddLabel q G S T :=
    fun D => Classical.choose (odd_component_labeled q G hq heven hmin S T hST D.val D.property)
  have hf (D : ((remainingGraph q G S T).oddComponents : Set _)) :
      labelComponent q G hq S T hST (f D) = D.val :=
    Classical.choose_spec (odd_component_labeled q G hq heven hmin S T hST D.val D.property)
  have hinj : Function.Injective f := by
    intro D E h
    apply Subtype.ext
    exact (hf D).symm.trans ((congrArg (labelComponent q G hq S T hST) h).trans (hf E))
  rw [← Nat.card_coe_set_eq, ← oddLabel_card q G S T]
  exact Nat.card_le_card_of_injective f hinj

end Erdos585.EvenFactorCriterion
