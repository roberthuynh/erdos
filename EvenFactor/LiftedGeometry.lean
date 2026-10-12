import EvenFactor.LiftedCard

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset SimpleGraph Function
namespace Erdos585.EvenFactorCriterion
open QB4 FactorMatching
universe u
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev RemainingVertex (S T : Finset V) :=
  {x : Vertex q G // x ∉ canonicalDeletion q G S T}

def remainingGraph (S T : Finset V) : SimpleGraph (RemainingVertex q G S T) :=
  (gadget q G).induce {x | x ∉ canonicalDeletion q G S T}

def liftedRemaining (S T A : Finset V) : Finset (RemainingVertex q G S T) :=
  univ.filter (fun x => x.val ∈ liftedVertices q G S A)

@[simp] lemma mem_liftedRemaining (S T A : Finset V) (x : RemainingVertex q G S T) :
    x ∈ liftedRemaining q G S T A ↔ x.val ∈ liftedVertices q G S A := by
  simp [liftedRemaining]

lemma lifted_avoids_deletion (S T : Finset V) (hST : Disjoint S T)
    (C : (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent)
    (x : Vertex q G)
    (hx : x ∈ liftedVertices q G S (componentVerts G (univ \ (S ∪ T)) C)) :
    x ∉ canonicalDeletion q G S T := by
  let A := componentVerts G (univ \ (S ∪ T)) C
  have hAS (v : V) (hv : v ∈ A) : v ∉ S := by
    have hr := componentVerts_subset G (univ \ (S ∪ T)) C hv
    exact fun hs => (mem_sdiff.mp hr).2 (mem_union_left T hs)
  have hAT (v : V) (hv : v ∈ A) : v ∉ T := by
    have hr := componentVerts_subset G (univ \ (S ∪ T)) C hv
    exact fun ht => (mem_sdiff.mp hr).2 (mem_union_right S ht)
  cases x with
  | inl s =>
    exact fun hm => hAS s.1 ((mem_lifted_slot q G S A s.1 s.2).mp hx)
      ((mem_canonical_slot q G S T s.1 s.2).mp hm)
  | inr d =>
    intro hm
    have hdT := (mem_canonical_stub q G S T d).mp hm
    rcases (mem_lifted_stub q G S A d).mp hx with hdA | ⟨hdS,_⟩
    · exact hAT d.fst hdA hdT
    · exact (Finset.disjoint_left.mp hST) hdS hdT

/-- Every member of this literal lifted set is a remaining original gadget vertex. -/
theorem liftedRemaining_card (S T : Finset V) (hST : Disjoint S T)
    (C : (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent) :
    #(liftedRemaining q G S T (componentVerts G (univ \ (S ∪ T)) C)) =
      #(liftedVertices q G S (componentVerts G (univ \ (S ∪ T)) C)) := by
  apply card_bij (fun x _ => x.val)
  · intro x hx
    exact (mem_liftedRemaining q G S T _ x).mp hx
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    let y : RemainingVertex q G S T := ⟨x,lifted_avoids_deletion q G S T hST C x hx⟩
    exact ⟨y,(mem_liftedRemaining q G S T _ y).mpr hx,rfl⟩

/-- Original component closure is transported through every actual gadget edge. -/
theorem liftedRemaining_closed (S T : Finset V) (hST : Disjoint S T)
    (C : (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent)
    (x y : RemainingVertex q G S T)
    (hx : x ∈ liftedRemaining q G S T (componentVerts G (univ \ (S ∪ T)) C))
    (hadj : (remainingGraph q G S T).Adj x y) :
    y ∈ liftedRemaining q G S T (componentVerts G (univ \ (S ∪ T)) C) := by
  let A := componentVerts G (univ \ (S ∪ T)) C
  simp only [mem_liftedRemaining] at hx ⊢
  rcases x with ⟨x,hxr⟩
  rcases y with ⟨y,hyr⟩
  change x ∈ liftedVertices q G S A at hx
  change (gadget q G).Adj x y at hadj
  change y ∈ liftedVertices q G S A
  cases x with
  | inl s =>
    cases y with
    | inl t => exact False.elim hadj
    | inr d =>
      have hA := (mem_lifted_slot q G S A s.1 s.2).mp hx
      apply (mem_lifted_stub q G S A d).mpr
      exact Or.inl (hadj ▸ hA)
  | inr d =>
    rcases (mem_lifted_stub q G S A d).mp hx with hdA | ⟨hdS,hdC⟩
    · cases y with
      | inl t =>
        apply (mem_lifted_slot q G S A t.1 t.2).mpr
        exact hadj ▸ hdA
      | inr e =>
        change e = d.symm at hadj
        subst e
        apply (mem_lifted_stub q G S A d.symm).mpr
        by_cases hs : d.snd ∈ S
        · exact Or.inr ⟨hs,hdA⟩
        · have ht : d.snd ∉ T := by simpa using hyr
          have hr : d.snd ∈ univ \ (S ∪ T) := by simp [hs,ht]
          exact Or.inl (component_no_external_edge G _ C d.fst d.snd hdA hr d.adj)
    · cases y with
      | inl t =>
        exact False.elim (hyr ((mem_canonical_slot q G S T t.1 t.2).mpr (hadj ▸ hdS)))
      | inr e =>
        change e = d.symm at hadj
        subst e
        exact (mem_lifted_stub q G S A d.symm).mpr (Or.inl hdC)

end Erdos585.EvenFactorCriterion
