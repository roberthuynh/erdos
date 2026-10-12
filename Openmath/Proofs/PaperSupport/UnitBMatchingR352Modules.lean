import Openmath.Proofs.PaperSupport.ReservationInterfaceR348
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset Sum
open scoped Classical
noncomputable section
namespace Erdos585.UnitBMatchingR352
open QB4
universe u
variable {V : Type u} [DecidableEq V]

def degreeB (E : Finset (V × V)) (b : V) : ℕ := #{e ∈ E | e.2 = b}
def indices (A B : Finset V) (E : Finset (V × V)) (d c : V → ℕ) :=
  (slots A d).disjSum (slots B fun b => degreeB E b - c b)
def neighbors (E : Finset (V × V)) : (V × ℕ) ⊕ (V × ℕ) → Finset (V × V) :=
  Sum.elim (fun s => E.filter fun e => e.1 = s.1)
    (fun s => E.filter fun e => e.2 = s.1)

lemma hall (A B : Finset V) (E : Finset (V × V)) (d c : V → ℕ)
    (hcut : ∀ P ⊆ A, ∀ T ⊆ B,
      (∑ a ∈ P, d a) ≤ #{e ∈ E | e.1 ∈ P ∧ e.2 ∉ T} + ∑ b ∈ T, c b)
    (S : Finset ((V × ℕ) ⊕ (V × ℕ))) (hS : S ⊆ indices A B E d c) :
    #S ≤ #(S.biUnion (neighbors E)) := by
  let P := S.toLeft.image Prod.fst
  let T := S.toRight.image Prod.fst
  have hL : ∀ s ∈ S.toLeft, s.1 ∈ A ∧ s.2 < d s.1 := by
    intro s hs
    exact mem_slots.1 (inl_mem_disjSum.1 (hS (mem_toLeft.1 hs)))
  have hR : ∀ s ∈ S.toRight, s.1 ∈ B ∧ s.2 < degreeB E s.1 - c s.1 := by
    intro s hs
    exact mem_slots.1 (inr_mem_disjSum.1 (hS (mem_toRight.1 hs)))
  have hPA : P ⊆ A := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := mem_image.1 ha
    exact (hL s hs).1
  have hTB : T ⊆ B := by
    intro b hb
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hb
    exact (hR s hs).1
  have hc : ∀ b ∈ T, c b ≤ degreeB E b := by
    intro b hb
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hb
    have := (hR s hs).2
    omega
  have hLc : #S.toLeft ≤ ∑ a ∈ P, d a := by
    rw [← card_slots]
    exact card_le_card fun s hs => mem_slots.2 ⟨mem_image_of_mem _ hs, (hL s hs).2⟩
  have hRc : #S.toRight ≤ ∑ b ∈ T, (degreeB E b - c b) := by
    rw [← card_slots]
    exact card_le_card fun s hs => mem_slots.2 ⟨mem_image_of_mem _ hs, (hR s hs).2⟩
  let N := E.filter fun e => e.1 ∈ P ∨ e.2 ∈ T
  have hN : N ⊆ S.biUnion (neighbors E) := by
    intro e he
    obtain ⟨heE, hePT⟩ := mem_filter.1 he
    rcases hePT with heP | heT
    · obtain ⟨s, hs, hse⟩ := mem_image.1 heP
      exact mem_biUnion.2 ⟨inl s, mem_toLeft.1 hs, mem_filter.2 ⟨heE, hse.symm⟩⟩
    · obtain ⟨s, hs, hse⟩ := mem_image.1 heT
      exact mem_biUnion.2 ⟨inr s, mem_toRight.1 hs, mem_filter.2 ⟨heE, hse.symm⟩⟩
  have hsplit : #N = #{e ∈ E | e.1 ∈ P ∧ e.2 ∉ T} + #{e ∈ E | e.2 ∈ T} := by
    have heq : N = (E.filter fun e => e.1 ∈ P ∧ e.2 ∉ T) ∪
        (E.filter fun e => e.2 ∈ T) := by
      ext e
      simp only [N, mem_filter, mem_union]
      tauto
    rw [heq, card_union_of_disjoint]
    exact disjoint_left.2 fun e he hf => (mem_filter.1 he).2.2 (mem_filter.1 hf).2
  have hdeg : #{e ∈ E | e.2 ∈ T} = ∑ b ∈ T, degreeB E b := by
    have hfiber : #{e ∈ E | e.2 ∈ T} = ∑ b ∈ T,
        #{e ∈ E.filter (fun e => e.2 ∈ T) | e.2 = b} :=
      card_eq_sum_card_fiberwise (f := Prod.snd) (fun e he => (mem_filter.1 he).2)
    rw [hfiber]
    apply sum_congr rfl
    intro b hb
    congr 1
    ext e
    simp only [mem_filter]
    constructor
    · tauto
    · rintro ⟨he, rfl⟩
      exact ⟨⟨he, hb⟩, rfl⟩
  have hcancel : (∑ b ∈ T, (degreeB E b - c b)) + ∑ b ∈ T, c b =
      ∑ b ∈ T, degreeB E b := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun b hb => Nat.sub_add_cancel (hc b hb)
  have hcut' := hcut P hPA T hTB
  have hsum := card_toLeft_add_card_toRight (u := S)
  have hbound := card_le_card hN
  omega

theorem exists_unit_bmatching (A B : Finset V) (E : Finset (V × V)) (d c : V → ℕ)
    (_hE : E ⊆ A ×ˢ B)
    (hcut : ∀ P ⊆ A, ∀ T ⊆ B,
      (∑ a ∈ P, d a) ≤ #{e ∈ E | e.1 ∈ P ∧ e.2 ∉ T} + ∑ b ∈ T, c b) :
    ∃ J : Finset (V × V), J ⊆ E ∧
      (∀ a ∈ A, #{e ∈ J | e.1 = a} = d a) ∧
      (∀ b ∈ B, #{e ∈ J | e.2 = b} ≤ c b) := by
  rcases A.eq_empty_or_nonempty with hA | ⟨a0, _⟩
  · exact ⟨∅, empty_subset _, by simp [hA], by simp⟩
  have : Nonempty (V × V) := ⟨(a0, a0)⟩
  obtain ⟨g, hginj, hgt⟩ := exists_injOn_of_hall (indices A B E d c) (neighbors E)
    (hall A B E d c hcut)
  let J := (slots A d).image (fun s => g (inl s))
  have hLmem : ∀ s ∈ slots A d, inl s ∈ indices A B E d c := by
    intro s hs
    exact inl_mem_disjSum.2 hs
  have hRmem : ∀ b ∈ B, ∀ i < degreeB E b - c b,
      inr (b, i) ∈ indices A B E d c := by
    intro b hb i hi
    exact inr_mem_disjSum.2 (mem_slots.2 ⟨hb, hi⟩)
  have hLedge : ∀ s ∈ slots A d, g (inl s) ∈ E ∧ (g (inl s)).1 = s.1 := by
    intro s hs
    exact mem_filter.1 (hgt _ (hLmem s hs))
  have hRedge : ∀ b ∈ B, ∀ i < degreeB E b - c b,
      g (inr (b, i)) ∈ E ∧ (g (inr (b, i))).2 = b := by
    intro b hb i hi
    exact mem_filter.1 (hgt _ (hRmem b hb i hi))
  have hJ : J ⊆ E := by
    intro e he
    obtain ⟨s, hs, rfl⟩ := mem_image.1 he
    exact (hLedge s hs).1
  refine ⟨J, hJ, ?_, ?_⟩
  · intro a ha
    have hsub : slots {a} d ⊆ slots A d := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := mem_slots.1 hs
      exact mem_slots.2 ⟨(mem_singleton.1 hs1) ▸ ha, hs2⟩
    have heq : J.filter (fun e => e.1 = a) =
        (slots {a} d).image (fun s => g (inl s)) := by
      ext e
      constructor
      · intro he
        obtain ⟨heJ, hea⟩ := mem_filter.1 he
        obtain ⟨s, hs, rfl⟩ := mem_image.1 heJ
        exact mem_image.2 ⟨s, mem_slots.2
          ⟨mem_singleton.2 ((hLedge s hs).2.symm.trans hea), (mem_slots.1 hs).2⟩, rfl⟩
      · intro he
        obtain ⟨s, hs, rfl⟩ := mem_image.1 he
        exact mem_filter.2 ⟨mem_image_of_mem _ (hsub hs),
          (hLedge s (hsub hs)).2.trans (mem_singleton.1 (mem_slots.1 hs).1)⟩
    rw [heq, card_image_of_injOn, card_slots, sum_singleton]
    intro s hs t ht heq
    exact inl_injective (hginj _ (hLmem s (hsub hs)) _ (hLmem t (hsub ht)) heq)
  · intro b hb
    let D := (range (degreeB E b - c b)).image (fun i => g (inr (b, i)))
    have hDc : #D = degreeB E b - c b := by
      rw [card_image_of_injOn, card_range]
      intro i hi j hj heq
      have hi' := mem_range.1 hi
      have hj' := mem_range.1 hj
      have he := hginj _ (hRmem b hb i hi') _ (hRmem b hb j hj') heq
      simpa using he
    have hD : D ⊆ E.filter (fun e => e.2 = b) := by
      intro e he
      obtain ⟨i, hi, rfl⟩ := mem_image.1 he
      exact mem_filter.2 (hRedge b hb i (mem_range.1 hi))
    have hdis : Disjoint (J.filter fun e => e.2 = b) D := by
      apply disjoint_left.2
      intro e heJ heD
      obtain ⟨s, hs, hse⟩ := mem_image.1 (mem_filter.1 heJ).1
      obtain ⟨i, hi, hie⟩ := mem_image.1 heD
      have he := hginj _ (hLmem s hs) _ (hRmem b hb i (mem_range.1 hi))
        (hse.trans hie.symm)
      exact inl_ne_inr he
    have hboth : (J.filter fun e => e.2 = b) ∪ D ⊆ E.filter (fun e => e.2 = b) := by
      intro e he
      rcases mem_union.1 he with he | he
      · exact mem_filter.2 ⟨hJ (mem_filter.1 he).1, (mem_filter.1 he).2⟩
      · exact hD he
    have hbound := card_le_card hboth
    rw [card_union_of_disjoint hdis, hDc] at hbound
    change #{e ∈ J | e.2 = b} + (degreeB E b - c b) ≤ degreeB E b at hbound
    omega

#print axioms exists_unit_bmatching
end Erdos585.UnitBMatchingR352

namespace Erdos585.UnitBMatchingR352
universe u
/-- Proof of the exact R348 interface, with no additional hypothesis. -/
theorem unitBMatchingCutCriterion :
    Erdos585.MixedMatchingReservationR348.UnitBMatchingCutCriterion.{u} := by
  classical
  intro V A B E d c hE hcut
  exact exists_unit_bmatching A B E d c hE hcut
#print axioms unitBMatchingCutCriterion
end Erdos585.UnitBMatchingR352
