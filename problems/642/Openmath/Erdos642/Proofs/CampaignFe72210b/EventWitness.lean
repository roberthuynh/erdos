import Openmath.Erdos642.Proofs.CampaignFe72210b.PathEvents

/-! Positive-weight witnesses for simultaneous events in the actual finite path law. -/
namespace Erdos642.FiniteMarkov.Chain
variable {V : Type*} [Fintype V] (C : Erdos642.FiniteMarkov.Chain V)
variable {n : ℕ}

theorem exists_positive_weight_of_eventMass_pos (E : V → Path V n → Prop)
    (x : V) (h : 0 < C.eventMass n E x) :
    ∃ p : Path V n, E x p ∧ 0 < C.weight x p := by
  classical
  by_contra hn
  push_neg at hn
  have hz : C.eventMass n E x ≤ 0 := by
    unfold eventMass
    apply Finset.sum_nonpos
    intro p _
    split_ifs with he
    · exact hn p he
    · exact le_rfl
  linarith

theorem exists_positive_weight_avoiding (E B : V → Path V n → Prop)
    (x : V) (h : C.eventMass n B x < C.eventMass n E x) :
    ∃ p : Path V n, E x p ∧ ¬ B x p ∧ 0 < C.weight x p := by
  have hm := C.eventMass_mono E (fun y p => (E y p ∧ ¬ B y p) ∨ B y p)
    (by intro y p he; by_cases hb : B y p <;> tauto) x
  have hu := C.eventMass_union_le (fun y p => E y p ∧ ¬ B y p) B x
  have hp : 0 < C.eventMass n (fun y p => E y p ∧ ¬ B y p) x := by linarith
  obtain ⟨p, ⟨he, hb⟩, hw⟩ := C.exists_positive_weight_of_eventMass_pos _ x hp
  exact ⟨p, he, hb, hw⟩

theorem exists_positive_weight_avoiding_family {I : Type*} [Fintype I]
    (E : V → Path V n → Prop) (B : I → V → Path V n → Prop)
    (x : V) (h : (∑ i, C.eventMass n (B i) x) < C.eventMass n E x) :
    ∃ p : Path V n, E x p ∧ (∀ i, ¬ B i x p) ∧ 0 < C.weight x p := by
  have hu := C.eventMass_iUnion_le B x
  obtain ⟨p, he, hb, hw⟩ := C.exists_positive_weight_avoiding E
    (fun y p => ∃ i, B i y p) x (lt_of_le_of_lt hu h)
  exact ⟨p, he, by simpa only [not_exists] using hb, hw⟩

end Erdos642.FiniteMarkov.Chain
