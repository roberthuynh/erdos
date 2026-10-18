import Openmath.IncidenceRepair.FrameSelection
import Mathlib.GroupTheory.GroupAction.Basic

/-!
Unconditioned averaging of equivariant slots. The acting group need not be finite:
it acts by permutations on the finite source and transitively on the target.
Actual projective action and transitivity are separate geometric obligations.
-/

open scoped BigOperators

namespace Erdos85.IncidenceRepair

/-- Equivariance transports each slot fiber bijectively to every other fiber. -/
theorem equivariant_slot_fiber_card_eq
    {G F I : Type*} [Group G] [Fintype F] [DecidableEq I]
    [MulAction G F] [MulAction G I] [MulAction.IsPretransitive G I]
    (slot : F → I) (hequiv : ∀ (g : G) (f : F), slot (g • f) = g • slot f)
    (i j : I) :
    (Finset.univ.filter (fun f => slot f = i)).card =
      (Finset.univ.filter (fun f => slot f = j)).card := by
  classical
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G i j
  apply Finset.card_bij (fun f _ => g • f)
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    rw [hequiv, hf, hg]
  · intro f hf f' hf' h
    exact (MulAction.toPerm g).injective h
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    refine ⟨g⁻¹ • f, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hequiv, hf, ← hg, inv_smul_smul]
    · exact smul_inv_smul g f

/-- Every original flag is sampled equally often by any equivariant slot.
The equality concerns all source frames, not frames conditioned on survival. -/
theorem average_equivariant_slot
    {G F I : Type*} [Group G] [Fintype F] [Fintype I] [DecidableEq I]
    [Nonempty F] [Nonempty I]
    [MulAction G F] [MulAction G I] [MulAction.IsPretransitive G I]
    (slot : F → I) (hequiv : ∀ (g : G) (f : F), slot (g • f) = g • slot f)
    (error : I → ℝ) :
    (∑ f, error (slot f)) / (Fintype.card F : ℝ) =
      (∑ i, error i) / (Fintype.card I : ℝ) := by
  classical
  let i₀ : I := Classical.choice inferInstance
  apply average_slot_of_equal_multiplicity slot error
    ((Finset.univ.filter (fun f => slot f = i₀)).card)
  intro i
  exact equivariant_slot_fiber_card_eq slot hequiv i i₀

/-- Any finite weighted family of equivariant flag slots has exactly the
predicted unconditioned total cost. Repetitions of slots are retained. -/
theorem average_weighted_equivariant_slots
    {G F I S : Type*} [Group G] [Fintype F] [Fintype I] [Fintype S]
    [DecidableEq I] [Nonempty F] [Nonempty I]
    [MulAction G F] [MulAction G I] [MulAction.IsPretransitive G I]
    (slot : S → F → I)
    (hequiv : ∀ (s : S) (g : G) (f : F), slot s (g • f) = g • slot s f)
    (weight : S → ℝ) (error : I → ℝ) :
    (∑ f, ∑ s, weight s * error (slot s f)) / (Fintype.card F : ℝ) =
      (∑ s, weight s) * ((∑ i, error i) / (Fintype.card I : ℝ)) := by
  calc
    (∑ f, ∑ s, weight s * error (slot s f)) / (Fintype.card F : ℝ) =
        ∑ s, weight s * ((∑ f, error (slot s f)) / (Fintype.card F : ℝ)) := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.mul_sum]
      ring
    _ = ∑ s, weight s * ((∑ i, error i) / (Fintype.card I : ℝ)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [average_equivariant_slot (slot s) (hequiv s) error]
    _ = (∑ s, weight s) * ((∑ i, error i) / (Fintype.card I : ℝ)) := by
      rw [Finset.sum_mul]

/-- A bound on the normalized mass of a slot family bounds its average cost. -/
theorem average_weighted_equivariant_slots_le
    {G F I S : Type*} [Group G] [Fintype F] [Fintype I] [Fintype S]
    [DecidableEq I] [Nonempty F] [Nonempty I]
    [MulAction G F] [MulAction G I] [MulAction.IsPretransitive G I]
    (slot : S → F → I)
    (hequiv : ∀ (s : S) (g : G) (f : F), slot s (g • f) = g • slot s f)
    (weight : S → ℝ) (error : I → ℝ) (mass : ℝ)
    (herror : ∀ i, 0 ≤ error i) (hmass : ∑ s, weight s ≤ mass) :
    (∑ f, ∑ s, weight s * error (slot s f)) / (Fintype.card F : ℝ) ≤
      mass * ((∑ i, error i) / (Fintype.card I : ℝ)) := by
  rw [average_weighted_equivariant_slots slot hequiv weight error]
  apply mul_le_mul_of_nonneg_right hmass
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => herror i)
  · positivity

/-- Union bound for an actual certificate made of finitely many equivariant
original-flag slots, including repeated slots. -/
theorem certificate_failure_fraction_le
    {G F I S : Type*} [Group G] [Fintype F] [Fintype I] [Fintype S]
    [DecidableEq I] [Nonempty F] [Nonempty I]
    [MulAction G F] [MulAction G I] [MulAction.IsPretransitive G I]
    (slot : S → F → I)
    (hequiv : ∀ (s : S) (g : G) (f : F), slot s (g • f) = g • slot s f)
    (bad : I → Prop) [DecidablePred bad] :
    ((Finset.univ.filter (fun f => ∃ s, bad (slot s f))).card : ℝ) /
        (Fintype.card F : ℝ) ≤
      (Fintype.card S : ℝ) *
        (((Finset.univ.filter bad).card : ℝ) / (Fintype.card I : ℝ)) := by
  classical
  have hpoint (f : F) :
      (if ∃ s, bad (slot s f) then (1 : ℝ) else 0) ≤
        ∑ s, if bad (slot s f) then (1 : ℝ) else 0 := by
    split_ifs with h
    · obtain ⟨s, hs⟩ := h
      calc
        (1 : ℝ) = (if bad (slot s f) then 1 else 0) := by simp [hs]
        _ ≤ ∑ s, if bad (slot s f) then (1 : ℝ) else 0 := by
          apply Finset.single_le_sum (s := Finset.univ)
            (f := fun s : S => if bad (slot s f) then (1 : ℝ) else 0) (a := s)
          · intro s _
            split_ifs <;> norm_num
          · exact Finset.mem_univ s
    · apply Finset.sum_nonneg
      intro s _
      split_ifs <;> norm_num
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun f _ => hpoint f)
  have havg := average_weighted_equivariant_slots slot hequiv
    (fun _ => (1 : ℝ)) (fun i => if bad i then (1 : ℝ) else 0)
  simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at havg
  have hsurv : (∑ f : F, if ∃ s, bad (slot s f) then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun f => ∃ s, bad (slot s f))).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  have hbad : (∑ i : I, if bad i then (1 : ℝ) else 0) =
      ((Finset.univ.filter bad).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [hsurv] at hsum
  rw [hbad] at havg
  rw [← havg]
  exact div_le_div_of_nonneg_right hsum (by positivity)

end Erdos85.IncidenceRepair
