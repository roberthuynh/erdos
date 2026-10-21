import Openmath.Proofs.PathContraction
import Mathlib.GroupTheory.Perm.Option
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Arbitrary arc constraints on a uniform cyclic permutation

The count is bounded by deleting a constrained vertex, without assuming a
displayed path partition or consistency of the prescribed ordered pairs.
This is a supporting finite counting input to the completion argument.
-/

namespace Erdos585.CyclicConstraintCount

open Equiv

universe u

variable {V : Type u}

abbrev TailEvent (s : Finset V) (f : V → V) :=
  {σ : Perm V // (∀ x ∈ s, σ x = f x) ∧ σ.IsCycleOn Set.univ}

abbrev ArcEvent (r : Finset (V × V)) :=
  {σ : Perm V // (∀ a ∈ r, σ a.1 = a.2) ∧ σ.IsCycleOn Set.univ}

theorem removeNone_apply (σ : Perm (Option V)) (y : V)
    (hy : σ none = some y) (x : V) :
    removeNone σ x = (σ (some x)).getD y := by
  cases h : σ (some x) with
  | none =>
    have hh := removeNone_none σ h
    rw [hy] at hh
    simpa using Option.some.inj hh
  | some z =>
    have hh := removeNone_some σ ⟨z, h⟩
    rw [h] at hh
    simpa using Option.some.inj hh

theorem removeNone_isCycleOn [Finite V] (σ : Perm (Option V)) (y : V)
    (hy : σ none = some y) (hσ : σ.IsCycleOn Set.univ) :
    Equiv.Perm.IsCycleOn (removeNone σ) Set.univ := by
  let p : Option V → V := fun v => v.getD y
  have step (v : Option V) :
      Equiv.Perm.SameCycle (removeNone σ) (p v) (p (σ v)) := by
    cases v with
    | none => simpa [p, hy] using (Equiv.Perm.SameCycle.rfl (f := removeNone σ) (x := y))
    | some x =>
      change Equiv.Perm.SameCycle (removeNone σ) x ((σ (some x)).getD y)
      rw [← removeNone_apply σ y hy x]
      exact Equiv.Perm.SameCycle.rfl.apply_right
  refine ⟨(removeNone σ).bijective.bijOn_univ, ?_⟩
  intro x _ z _
  obtain ⟨n, hn⟩ := hσ.exists_pow_eq' Set.finite_univ
    (Set.mem_univ (some x)) (Set.mem_univ (some z))
  have hp : ∀ n : ℕ, Equiv.Perm.SameCycle (removeNone σ) x (p ((σ ^ n) (some x))) := by
    intro n
    induction n with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ n ih =>
      simpa only [pow_succ', Equiv.Perm.mul_apply] using
        ih.trans (step ((σ ^ n) (some x)))
  simpa [hn, p] using hp n

theorem removeNone_injective_on [DecidableEq V]
    (σ τ : Perm (Option V)) (hhead : σ none = τ none)
    (hremove : removeNone σ = removeNone τ) : σ = τ := by
  apply Equiv.Perm.decomposeOption.injective
  exact Prod.ext hhead hremove

/-- Relabel and remove one prescribed tail from an actual cycle. -/
noncomputable def deleteTail [Fintype V] [DecidableEq V]
    (s : Finset V) (f : V → V) (x : V) (hx : x ∈ s) (hfx : f x ≠ x)
    (σ : TailEvent s f) :
    TailEvent (s.subtype (fun v => v ≠ x))
      (fun v => ((optionSubtypeNe x).symm (f v)).getD ⟨f x, hfx⟩) := by
  let e := optionSubtypeNe x
  let σo := e.symm.permCongr σ.1
  have hnone : σo none = some ⟨f x, hfx⟩ := by
    simp [σo, e, Equiv.permCongr_apply, σ.2.1 x hx,
      Equiv.optionSubtypeNe_symm_of_ne hfx]
  refine ⟨removeNone σo, ?_, ?_⟩
  · intro v hv
    rw [removeNone_apply σo ⟨f x, hfx⟩ hnone]
    have hh := σ.2.1 v (Finset.mem_subtype.mp hv)
    simp only [σo, Equiv.permCongr_apply, Equiv.symm_symm,
      e, Equiv.optionSubtypeNe_some, hh]
  · apply removeNone_isCycleOn σo _ hnone
    exact Erdos585.PathContraction.isCycleOn_relabel e.symm σ.1 σ.2.2

theorem deleteTail_injective [Fintype V] [DecidableEq V]
    (s : Finset V) (f : V → V) (x : V) (hx : x ∈ s) (hfx : f x ≠ x) :
    Function.Injective (deleteTail s f x hx hfx) := by
  intro σ τ h
  apply Subtype.ext
  apply (optionSubtypeNe x).symm.permCongr.injective
  apply removeNone_injective_on
  · simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.optionSubtypeNe_none,
      σ.2.1 x hx, τ.2.1 x hx]
  · exact congrArg Subtype.val h

/-- No consistency or path-partition assumption is imposed on the tail data. -/
theorem card_tailEvent_le_aux (k : ℕ) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (s : Finset V) (f : V → V),
      s.card = k → k + 2 ≤ Fintype.card V →
      Nat.card (TailEvent s f) ≤ (Fintype.card V - k - 1).factorial := by
  induction k with
  | zero =>
    intro V _ _ s f hs hn
    have he : s = ∅ := Finset.card_eq_zero.mp hs
    subst s
    have e : TailEvent (∅ : Finset V) f ≃
        {σ : Perm V // σ.IsCycleOn Set.univ} :=
      Equiv.subtypeEquivRight (fun _ => by simp)
    rw [Nat.card_congr e, Erdos585.PathContraction.card_fullCycles (by omega)]
    simp
  | succ k ih =>
    intro V _ _ s f hs hn
    classical
    by_cases hne : Nonempty (TailEvent s f)
    · obtain ⟨σ⟩ := hne
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
      have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      let : Nontrivial V := hnt
      have hfx : f x ≠ x := by
        rw [← σ.2.1 x hx]
        exact σ.2.2.apply_ne Set.nontrivial_univ (Set.mem_univ x)
      let s' := s.subtype (fun v => v ≠ x)
      have hs' : s'.card = k := by
        have he : s.filter (fun v => v ≠ x) = s.erase x := by
          ext v
          simp [and_comm]
        simp only [s', Finset.card_subtype, he, Finset.card_erase_of_mem hx, hs]
        omega
      have hn' : Fintype.card {v : V // v ≠ x} + 1 = Fintype.card V := by
        simpa using Fintype.card_congr (optionSubtypeNe x)
      let f' : {v : V // v ≠ x} → {v : V // v ≠ x} :=
        fun v => ((optionSubtypeNe x).symm (f v)).getD ⟨f x, hfx⟩
      have hcount := ih s' f' hs' (by omega)
      have hbound := Nat.card_le_card_of_injective
        (deleteTail s f x hx hfx) (deleteTail_injective s f x hx hfx)
      have hsub : Fintype.card {v : V // v ≠ x} - k - 1 =
          Fintype.card V - (k + 1) - 1 := by omega
      exact hbound.trans (by simpa only [hsub] using hcount)
    · let : IsEmpty (TailEvent s f) := not_nonempty_iff.mp hne
      simp

/-- Bound the event for an arbitrary finite set of actual ordered-pair constraints. -/
theorem card_arcEvent_le [Fintype V] [DecidableEq V] (r : Finset (V × V))
    (hn : r.card + 2 ≤ Fintype.card V) :
    Nat.card (ArcEvent r) ≤ (Fintype.card V - r.card - 1).factorial := by
  classical
  by_cases hne : Nonempty (ArcEvent r)
  · obtain ⟨ρ⟩ := hne
    let s := r.image Prod.fst
    have hs : s.card = r.card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      apply Prod.ext hab
      exact (ρ.2.1 a ha).symm.trans ((congrArg ρ.1 hab).trans (ρ.2.1 b hb))
    have hp (σ : Perm V) : (∀ a ∈ r, σ a.1 = a.2) ↔ ∀ x ∈ s, σ x = ρ.1 x := by
      constructor
      · intro h x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact (h a ha).trans (ρ.2.1 a ha).symm
      · intro h a ha
        exact (h a.1 (Finset.mem_image.mpr ⟨a, ha, rfl⟩)).trans (ρ.2.1 a ha)
    let e : ArcEvent r ≃ TailEvent s ρ.1 :=
      Equiv.subtypeEquivRight (fun σ => and_congr (hp σ) Iff.rfl)
    rw [Nat.card_congr e]
    exact card_tailEvent_le_aux r.card s ρ.1 hs hn
  · let : IsEmpty (ArcEvent r) := not_nonempty_iff.mp hne
    simp

/-- Scalar probability estimate, with every factorial and denominator positive. -/
theorem factorial_ratio_le (n k : ℕ) (hn : k + 2 ≤ n) (hk : 2 * k ≤ n) :
    ((n - k - 1).factorial : ℚ) / ((n - 1).factorial : ℚ) ≤
      (2 / (n : ℚ)) ^ k := by
  have hstep : n - k - 1 + 1 = n - k := by omega
  have hsum : n - k - 1 + k = n - 1 := by omega
  have hnat : (n - k - 1).factorial * (n - k) ^ k ≤ (n - 1).factorial := by
    simpa only [hstep, hsum] using
      (Nat.factorial_mul_pow_le_factorial (m := n - k - 1) (n := k))
  have hcast : ((n - k - 1).factorial : ℚ) * ((n - k : ℕ) : ℚ) ^ k ≤
      ((n - 1).factorial : ℚ) := by exact_mod_cast hnat
  have hnk : k ≤ n := by omega
  have hhalf : (n : ℚ) / 2 ≤ ((n - k : ℕ) : ℚ) := by
    rw [Nat.cast_sub hnk]
    have hh : 2 * (k : ℚ) ≤ (n : ℚ) := by exact_mod_cast hk
    linarith
  have hp : 0 < (n : ℚ) / 2 := by
    have hh : 0 < n := by omega
    positivity
  have hprod : ((n - k - 1).factorial : ℚ) * ((n : ℚ) / 2) ^ k ≤
      ((n - 1).factorial : ℚ) := by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le hhalf k)
      (by positivity)).trans hcast
  have hf : 0 < ((n - 1).factorial : ℚ) := by positivity
  calc
    ((n - k - 1).factorial : ℚ) / ((n - 1).factorial : ℚ)
      ≤ 1 / ((n : ℚ) / 2) ^ k := by
        apply (div_le_div_iff₀ hf (pow_pos hp k)).mpr
        simpa using hprod
    _ = (2 / (n : ℚ)) ^ k := by rw [← one_div_pow, one_div_div]

/-- The finite uniform cycle probability is its event count divided by the full sample count. -/
noncomputable def uniformCycleProbability [Finite V] (r : Finset (V × V)) : ℚ :=
  (Nat.card (ArcEvent r) : ℚ) /
    (Nat.card {σ : Perm V // σ.IsCycleOn Set.univ} : ℚ)

/-- Arbitrary actual arcs satisfy the joint bound used by the Hamilton completion sampler. -/
theorem uniformCycleProbability_le [Fintype V] [DecidableEq V]
    (r : Finset (V × V)) (hn : r.card + 2 ≤ Fintype.card V)
    (hk : 2 * r.card ≤ Fintype.card V) :
    uniformCycleProbability r ≤ (2 / (Fintype.card V : ℚ)) ^ r.card := by
  have hc : (Nat.card (ArcEvent r) : ℚ) ≤
      ((Fintype.card V - r.card - 1).factorial : ℚ) := by
    exact_mod_cast card_arcEvent_le r hn
  unfold uniformCycleProbability
  rw [Erdos585.PathContraction.card_fullCycles (by omega)]
  exact (div_le_div_of_nonneg_right hc (by positivity)).trans
    (factorial_ratio_le (Fintype.card V) r.card hn hk)

end Erdos585.CyclicConstraintCount
