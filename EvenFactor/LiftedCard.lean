import EvenFactor.ComponentParity

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

def crossDarts (S A : Finset V) : Finset G.Dart :=
  univ.filter (fun d => d.fst ∈ S ∧ d.snd ∈ A)

@[simp] lemma mem_crossDarts (S A : Finset V) (d : G.Dart) :
    d ∈ crossDarts G S A ↔ d.fst ∈ S ∧ d.snd ∈ A := by simp [crossDarts]

lemma crossDarts_card (S A : Finset V) : #(crossDarts G S A) = ec G S A := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun d : G.Dart => d.fst) (t := S)
    (fun d hd => ((mem_crossDarts G S A d).mp hd).1)]
  unfold ec dg
  apply sum_congr rfl
  intro v hv
  apply card_bij (fun d _ => d.snd)
  · intro d hd
    obtain ⟨hd,he⟩ := mem_filter.mp hd
    obtain ⟨_,hA⟩ := (mem_crossDarts G S A d).mp hd
    exact mem_filter.mpr ⟨hA,he ▸ d.adj⟩
  · intro d hd e he hsame
    apply Dart.ext
    apply Prod.ext
    · exact ((mem_filter.mp hd).2).trans ((mem_filter.mp he).2).symm
    · exact hsame
  · intro w hw
    obtain ⟨hA,hadj⟩ := mem_filter.mp hw
    let d : G.Dart := ⟨(v,w),hadj⟩
    refine ⟨d,?_,rfl⟩
    simp [d, hv,hA]

def liftedVertices (S A : Finset V) : Finset (Vertex q G) :=
  (A ×ˢ (univ : Finset (Fin q))).disjSum
    ((dartsAt G A) ∪ crossDarts G S A)

@[simp] lemma mem_lifted_slot (S A : Finset V) (v : V) (i : Fin q) :
    Sum.inl (v,i) ∈ liftedVertices q G S A ↔ v ∈ A := by
  simp [liftedVertices]

@[simp] lemma mem_lifted_stub (S A : Finset V) (d : G.Dart) :
    Sum.inr d ∈ liftedVertices q G S A ↔ d.fst ∈ A ∨ (d.fst ∈ S ∧ d.snd ∈ A) := by
  simp [liftedVertices]

lemma dartsAt_cross_disjoint (S A : Finset V) (hAS : Disjoint A S) :
    Disjoint (dartsAt G A) (crossDarts G S A) := by
  rw [Finset.disjoint_left]
  intro d hd he
  exact (Finset.disjoint_left.mp hAS) ((mem_dartsAt G A d).mp hd)
    ((mem_crossDarts G S A d).mp he).1

/-- Every displayed vertex is an actual local slot or original incident dart. -/
theorem liftedVertices_card (S A : Finset V) (hAS : Disjoint A S) :
    #(liftedVertices q G S A) = q * #A + (∑ v ∈ A, G.degree v) + ec G S A := by
  rw [liftedVertices,card_disjSum,card_product,card_univ,Fintype.card_fin,
    card_union_of_disjoint (dartsAt_cross_disjoint G S A hAS),
    dartsAt_card,crossDarts_card]
  ring

/-- Cardinal parity of the literal lifted vertex set of an actual original
component. Connectivity and complete gadget-component classification are separate. -/
theorem lifted_component_vertices_parity (heven : Even q) (S T : Finset V)
    (hST : Disjoint S T)
    (C : (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent) :
    Odd #(liftedVertices q G S (componentVerts G (univ \ (S ∪ T)) C)) ↔
      Odd (ec G (componentVerts G (univ \ (S ∪ T)) C) T) := by
  have hAS : Disjoint (componentVerts G (univ \ (S ∪ T)) C) S := by
    apply Finset.disjoint_left.mpr
    intro v hv hs
    have hr := componentVerts_subset G (univ \ (S ∪ T)) C hv
    exact (mem_sdiff.mp hr).2 (mem_union_left T hs)
  rw [liftedVertices_card q G S _ hAS]
  exact component_lifted_parity G q heven S T hST C

end Erdos585.EvenFactorCriterion
