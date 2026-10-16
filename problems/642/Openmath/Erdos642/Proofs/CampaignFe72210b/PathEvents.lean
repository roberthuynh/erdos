import Openmath.Erdos642.Proofs.CampaignFe72210b.FiniteMarkov

namespace Erdos642.FiniteMarkov.Chain
variable {V : Type*} [Fintype V] (C : Erdos642.FiniteMarkov.Chain V)
variable {n : ℕ}

theorem eventMass_mono (E F : V → Path V n → Prop)
    (h : ∀ x p, E x p → F x p) (x : V) :
    C.eventMass n E x ≤ C.eventMass n F x := by
  classical
  unfold eventMass
  apply Finset.sum_le_sum
  intro p _
  split_ifs with he hf hf
  · exact le_rfl
  · exact False.elim (hf (h x p he))
  · exact C.weight_nonneg x p
  · exact le_rfl

theorem eventMass_compl_add (E : V → Path V n → Prop) (x : V) :
    C.eventMass n (fun y p => ¬ E y p) x + C.eventMass n E x = 1 := by
  classical
  unfold eventMass
  rw [← Finset.sum_add_distrib, ← C.total_weight n x]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : E x p <;> simp [h]

theorem eventMass_compl (E : V → Path V n → Prop) (x : V) :
    C.eventMass n (fun y p => ¬ E y p) x = 1 - C.eventMass n E x := by
  have h := C.eventMass_compl_add E x
  linarith

theorem eventMass_union_le (E F : V → Path V n → Prop) (x : V) :
    C.eventMass n (fun y p => E y p ∨ F y p) x ≤
      C.eventMass n E x + C.eventMass n F x := by
  classical
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  have hw := C.weight_nonneg x p
  by_cases he : E x p <;> by_cases hf : F x p <;> simp [he, hf]
  linarith

theorem eventMass_biUnion_le {I : Type*} (s : Finset I)
    (E : I → V → Path V n → Prop) (x : V) :
    C.eventMass n (fun y p => ∃ i ∈ s, E i y p) x ≤
      ∑ i ∈ s, C.eventMass n (E i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eventMass]
  | @insert i s hi ih =>
    have h := C.eventMass_union_le (E i) (fun y p => ∃ j ∈ s, E j y p) x
    simp only [Finset.mem_insert, exists_eq_or_imp] at h ⊢
    rw [Finset.sum_insert hi]
    exact h.trans (add_le_add le_rfl ih)

theorem eventMass_iUnion_le {I : Type*} [Fintype I]
    (E : I → V → Path V n → Prop) (x : V) :
    C.eventMass n (fun y p => ∃ i, E i y p) x ≤
      ∑ i, C.eventMass n (E i) x := by
  classical
  simpa using C.eventMass_biUnion_le Finset.univ E x
end Erdos642.FiniteMarkov.Chain
