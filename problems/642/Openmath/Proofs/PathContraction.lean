import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Logic.Equiv.Fin.Rotate

   
                                                               

                                                                      
                                                                         
                                                                       
                                                                          
  

namespace Erdos585.PathContraction

open Equiv

variable {I : Type*}

abbrev Vertex (len : I → ℕ) := Σ i, Fin (len i + 1)

def head (len : I → ℕ) (i : I) : Vertex len := ⟨i, 0⟩

def tail (len : I → ℕ) (i : I) : Vertex len := ⟨i, Fin.last (len i)⟩

def moveHeadFn (len : I → ℕ) (τ : Perm I) (v : Vertex len) : Vertex len :=
  if v.2 = 0 then head len (τ v.1) else v

theorem moveHeadFn_head (len : I → ℕ) (τ : Perm I) (i : I) :
    moveHeadFn len τ (head len i) = head len (τ i) := rfl

theorem moveHeadFn_nonzero (len : I → ℕ) (τ : Perm I) (v : Vertex len)
    (hv : v.2 ≠ 0) : moveHeadFn len τ v = v := if_neg hv

def moveHeads (len : I → ℕ) (τ : Perm I) : Perm (Vertex len) where
  toFun := moveHeadFn len τ
  invFun := moveHeadFn len τ.symm
  left_inv := by
    rintro ⟨i, k⟩
    by_cases hk : k = 0
    · subst k
      change moveHeadFn len τ.symm (moveHeadFn len τ (head len i)) = _
      rw [moveHeadFn_head, moveHeadFn_head, Equiv.symm_apply_apply]
      rfl
    · rw [moveHeadFn_nonzero len τ _ hk, moveHeadFn_nonzero len τ.symm _ hk]
  right_inv := by
    rintro ⟨i, k⟩
    by_cases hk : k = 0
    · subst k
      change moveHeadFn len τ (moveHeadFn len τ.symm (head len i)) = _
      rw [moveHeadFn_head, moveHeadFn_head, Equiv.apply_symm_apply]
      rfl
    · rw [moveHeadFn_nonzero len τ.symm _ hk, moveHeadFn_nonzero len τ _ hk]

def successor (len : I → ℕ) (τ : Perm I) : Perm (Vertex len) :=
  moveHeads len τ * Equiv.sigmaCongrRight (fun i => finRotate (len i + 1))

theorem successor_internal (len : I → ℕ) (τ : Perm I) (i : I)
    (k : ℕ) (hk : k < len i) :
    successor len τ ⟨i, ⟨k, by omega⟩⟩ = ⟨i, ⟨k + 1, by omega⟩⟩ := by
  change moveHeads len τ ⟨i, finRotate (len i + 1) ⟨k, by omega⟩⟩ = _
  rw [finRotate_of_lt hk]
  change moveHeadFn len τ ⟨i, ⟨k + 1, by omega⟩⟩ = ⟨i, ⟨k + 1, by omega⟩⟩
  apply moveHeadFn_nonzero len τ
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_zero] at hh
  omega

theorem successor_tail (len : I → ℕ) (τ : Perm I) (i : I) :
    successor len τ (tail len i) = head len (τ i) := by
  change moveHeads len τ ⟨i, finRotate (len i + 1) (Fin.last (len i))⟩ = _
  rw [finRotate_last]
  exact moveHeadFn_head len τ i

                                                                                     
def Preserves (len : I → ℕ) (σ : Perm (Vertex len)) : Prop :=
  ∀ i k (hk : k < len i), σ ⟨i, ⟨k, by omega⟩⟩ = ⟨i, ⟨k + 1, by omega⟩⟩

theorem successor_preserves (len : I → ℕ) (τ : Perm I) :
    Preserves len (successor len τ) := successor_internal len τ

theorem sameCycle_within (len : I → ℕ) (τ : Perm I) (i : I)
    (k : Fin (len i + 1)) :
    (successor len τ).SameCycle (head len i) ⟨i, k⟩ := by
  obtain ⟨k, hk⟩ := k
  induction k with
  | zero => exact Equiv.Perm.SameCycle.rfl
  | succ k ih =>
    have hh := (ih (by omega)).apply_right
    simpa only [successor_internal len τ i k (by omega)] using hh

theorem sameCycle_next_head (len : I → ℕ) (τ : Perm I) (i : I) :
    (successor len τ).SameCycle (head len i) (head len (τ i)) := by
  have hh := (sameCycle_within len τ i (Fin.last (len i))).apply_right
  change (successor len τ).SameCycle (head len i) (successor len τ (tail len i)) at hh
  rwa [successor_tail] at hh

theorem successor_isCycleOn [Finite I] (len : I → ℕ) (τ : Perm I)
    (hτ : τ.IsCycleOn Set.univ) :
    (successor len τ).IsCycleOn Set.univ := by
  refine ⟨(successor len τ).bijective.bijOn_univ, ?_⟩
  rintro ⟨i, k⟩ _ ⟨j, l⟩ _
  obtain ⟨n, hn⟩ := hτ.exists_pow_eq' Set.finite_univ (Set.mem_univ i) (Set.mem_univ j)
  have hpow : ∀ n : ℕ, (successor len τ).SameCycle
      (head len i) (head len ((τ ^ n) i)) := by
    intro n
    induction n with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ n ih =>
      simpa only [pow_succ', Equiv.Perm.mul_apply] using
        ih.trans (sameCycle_next_head len τ ((τ ^ n) i))
  have hj : (successor len τ).SameCycle (head len i) (head len j) := by
    simpa only [hn] using hpow n
  exact (sameCycle_within len τ i k).symm.trans
    (hj.trans (sameCycle_within len τ j l))

theorem sameCycle_index_step (len : I → ℕ) (τ : Perm I) (v : Vertex len) :
    τ.SameCycle v.1 ((successor len τ) v).1 := by
  obtain ⟨i, k, hk⟩ := v
  by_cases h : k < len i
  · rw [successor_internal len τ i k h]
  · have heq : k = len i := by omega
    subst k
    change τ.SameCycle i ((successor len τ) (tail len i)).1
    rw [successor_tail]
    exact Equiv.Perm.SameCycle.rfl.apply_right

theorem isCycleOn_of_successor [Finite I] (len : I → ℕ) (τ : Perm I)
    (hσ : (successor len τ).IsCycleOn Set.univ) : τ.IsCycleOn Set.univ := by
  refine ⟨τ.bijective.bijOn_univ, ?_⟩
  intro i _ j _
  obtain ⟨n, hn⟩ := hσ.exists_pow_eq' Set.finite_univ
    (Set.mem_univ (head len i)) (Set.mem_univ (head len j))
  have hpow : ∀ n : ℕ, τ.SameCycle i (((successor len τ) ^ n) (head len i)).1 := by
    intro n
    induction n with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ n ih =>
      simpa only [pow_succ', Equiv.Perm.mul_apply] using
        ih.trans (sameCycle_index_step len τ (((successor len τ) ^ n) (head len i)))
  have hh := hpow n
  rw [hn] at hh
  exact hh

theorem successor_isCycleOn_iff [Finite I] (len : I → ℕ) (τ : Perm I) :
    (successor len τ).IsCycleOn Set.univ ↔ τ.IsCycleOn Set.univ :=
  ⟨isCycleOn_of_successor len τ, successor_isCycleOn len τ⟩

/-- Any extension sends a tail to a head, since all other vertices already have predecessors. -/
theorem tail_image_is_head (len : I → ℕ) (σ : Perm (Vertex len))
    (hσ : Preserves len σ) (i : I) :
    σ (tail len i) = head len (σ (tail len i)).1 := by
  generalize hval : σ (tail len i) = v
  obtain ⟨j, k, hk⟩ := v
  have hz : k = 0 := by
    by_contra hn
    have hp : k - 1 < len j := by omega
    have hpv := hσ j (k - 1) hp
    have hpv' : σ ⟨j, ⟨k - 1, by omega⟩⟩ = ⟨j, ⟨k, hk⟩⟩ := by
      have hk1 : k - 1 + 1 = k := by omega
      simpa only [hk1] using hpv
    have heq := σ.injective (hval.trans hpv'.symm)
    have hij : i = j := congrArg Sigma.fst heq
    subst j
    have hv : len i = k - 1 := by
      simpa [tail] using congrArg (fun v : Vertex len => v.2.val) heq
    omega
  subst k
  rfl

theorem contracted_injective (len : I → ℕ) (σ : Perm (Vertex len))
    (hσ : Preserves len σ) : Function.Injective (fun i => (σ (tail len i)).1) := by
  intro i j hij
  change (σ (tail len i)).1 = (σ (tail len j)).1 at hij
  have heq : σ (tail len i) = σ (tail len j) := by
    rw [tail_image_is_head len σ hσ i, tail_image_is_head len σ hσ j, hij]
  exact congrArg Sigma.fst (σ.injective heq)

noncomputable def contract [Finite I] (len : I → ℕ) (σ : Perm (Vertex len))
    (hσ : Preserves len σ) : Perm I :=
  Equiv.ofBijective (fun i => (σ (tail len i)).1)
    ((Finite.injective_iff_bijective).mp (contracted_injective len σ hσ))

theorem contract_apply [Finite I] (len : I → ℕ) (σ : Perm (Vertex len))
    (hσ : Preserves len σ) (i : I) : contract len σ hσ i = (σ (tail len i)).1 := rfl

theorem successor_contract [Finite I] (len : I → ℕ) (σ : Perm (Vertex len))
    (hσ : Preserves len σ) : successor len (contract len σ hσ) = σ := by
  apply Equiv.ext
  rintro ⟨i, k, hk⟩
  by_cases h : k < len i
  · exact (successor_internal len _ i k h).trans (hσ i k h).symm
  · have heq : k = len i := by omega
    subst k
    change successor len (contract len σ hσ) (tail len i) = σ (tail len i)
    rw [successor_tail, contract_apply]
    exact (tail_image_is_head len σ hσ i).symm

theorem contract_successor [Finite I] (len : I → ℕ) (τ : Perm I) :
    contract len (successor len τ) (successor_preserves len τ) = τ := by
  apply Equiv.ext
  intro i
  rw [contract_apply, successor_tail]
  rfl

/-- Explicit contraction/expansion correspondence on all cyclic path extensions. -/
noncomputable def cyclicExtensionEquiv [Finite I] (len : I → ℕ) :
    {σ : Perm (Vertex len) // Preserves len σ ∧ σ.IsCycleOn Set.univ} ≃
      {τ : Perm I // τ.IsCycleOn Set.univ} where
  toFun σ := ⟨contract len σ.1 σ.2.1, by
    apply isCycleOn_of_successor len
    rw [successor_contract]
    exact σ.2.2⟩
  invFun τ := ⟨successor len τ.1, successor_preserves len τ.1, successor_isCycleOn len τ.1 τ.2⟩
  left_inv σ := by
    apply Subtype.ext
    exact successor_contract len σ.1 σ.2.1
  right_inv τ := by
    apply Subtype.ext
    exact contract_successor len τ.1

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem isCycleOn_univ_iff_cycleType (σ : Perm V) (hc : 2 ≤ Fintype.card V) :
    σ.IsCycleOn Set.univ ↔ σ.cycleType = {Fintype.card V} := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hc
  constructor
  · intro h
    have hcycle : σ.IsCycle :=
      Equiv.Perm.isCycle_iff_exists_isCycleOn.mpr
        ⟨Set.univ, Set.nontrivial_univ, h, fun _ _ => Set.mem_univ _⟩
    have hs : σ.support = Finset.univ := by
      ext v
      simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
      exact h.apply_ne Set.nontrivial_univ (Set.mem_univ v)
    rw [hcycle.cycleType, hs, Finset.card_univ]
  · intro h
    have hcycle : σ.IsCycle := Equiv.Perm.card_cycleType_eq_one.mp (by simp [h])
    have hs : σ.support = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [← Equiv.Perm.sum_cycleType, h, Multiset.sum_singleton]
    have hset : {v | σ v ≠ v} = Set.univ := by
      ext v
      simpa only [Equiv.Perm.mem_support, Finset.mem_univ, Set.mem_ofPred_eq,
        Set.mem_univ, iff_true] using Finset.ext_iff.mp hs v
    simpa only [hset] using hcycle.isCycleOn

/-- The unrestricted cycle count is supplied by Mathlib's cycle-type enumeration. -/
theorem card_fullCycles (hc : 2 ≤ Fintype.card V) :
    Nat.card {σ : Perm V // σ.IsCycleOn Set.univ} = (Fintype.card V - 1).factorial := by
  classical
  have heq : {σ : Perm V // σ.IsCycleOn Set.univ} ≃
      {σ : Perm V // σ.cycleType = {Fintype.card V}} :=
    Equiv.subtypeEquivRight (fun σ => isCycleOn_univ_iff_cycleType σ hc)
  rw [Nat.card_congr heq, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [Nat.choose_self, mul_one] using
    (Equiv.Perm.card_of_cycleType_singleton (α := V) hc (le_refl _))

end Counting

/-- All cyclic extensions of a displayed path partition are counted, with no formula assumed. -/
theorem card_cyclicExtensions [Fintype I] (len : I → ℕ) (hc : 2 ≤ Fintype.card I) :
    Nat.card {σ : Perm (Vertex len) // Preserves len σ ∧ σ.IsCycleOn Set.univ} =
      (Fintype.card I - 1).factorial := by
  classical
  rw [Nat.card_congr (cyclicExtensionEquiv len)]
  exact card_fullCycles hc

section Relabel

variable {V W : Type*}

theorem permCongr_pow_apply (e : V ≃ W) (σ : Perm V) (n : ℕ) (v : V) :
    ((e.permCongr σ) ^ n) (e v) = e ((σ ^ n) v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply, ih, Equiv.permCongr_apply,
      Equiv.symm_apply_apply]

theorem isCycleOn_relabel [Finite V] (e : V ≃ W) (σ : Perm V)
    (hσ : σ.IsCycleOn Set.univ) : (e.permCongr σ).IsCycleOn Set.univ := by
  refine ⟨(e.permCongr σ).bijective.bijOn_univ, ?_⟩
  intro x _ y _
  obtain ⟨n, hn⟩ := hσ.exists_pow_eq' Set.finite_univ
    (Set.mem_univ (e.symm x)) (Set.mem_univ (e.symm y))
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  have hh := permCongr_pow_apply e σ n (e.symm x)
  simpa only [Equiv.apply_symm_apply, hn] using hh

theorem isCycleOn_relabel_iff [Finite V] [Finite W] (e : V ≃ W) (σ : Perm V) :
    (e.permCongr σ).IsCycleOn Set.univ ↔ σ.IsCycleOn Set.univ := by
  constructor
  · intro h
    have hh := isCycleOn_relabel e.symm (e.permCongr σ) h
    simpa only [← Equiv.permCongr_symm, Equiv.symm_apply_apply] using hh
  · exact isCycleOn_relabel e σ

/-- Prescribed arcs on the original labels, not merely on component indices. -/
def PreservesAlong (len : I → ℕ) (e : Vertex len ≃ V) (σ : Perm V) : Prop :=
  ∀ i k (hk : k < len i),
    σ (e ⟨i, ⟨k, by omega⟩⟩) = e ⟨i, ⟨k + 1, by omega⟩⟩

theorem preservesAlong_iff (len : I → ℕ) (e : Vertex len ≃ V) (σ : Perm V) :
    PreservesAlong len e σ ↔ Preserves len (e.symm.permCongr σ) := by
  constructor
  · intro h i k hk
    simpa only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
      using congrArg e.symm (h i k hk)
  · intro h i k hk
    simpa only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
      using congrArg e (h i k hk)

noncomputable def labeledExtensionEquiv [Finite I] [Finite V]
    (len : I → ℕ) (e : Vertex len ≃ V) :
    {σ : Perm V // PreservesAlong len e σ ∧ σ.IsCycleOn Set.univ} ≃
      {σ : Perm (Vertex len) // Preserves len σ ∧ σ.IsCycleOn Set.univ} :=
  e.symm.permCongr.subtypeEquiv (by
    intro σ
    exact and_congr (preservesAlong_iff len e σ) (isCycleOn_relabel_iff e.symm σ).symm)

/-- Exact count for arbitrary original labels and arbitrary nonempty path components. -/
theorem card_labeled_cyclicExtensions [Fintype I] [Finite V]
    (len : I → ℕ) (e : Vertex len ≃ V) (hc : 2 ≤ Fintype.card I) :
    Nat.card {σ : Perm V // PreservesAlong len e σ ∧ σ.IsCycleOn Set.univ} =
      (Fintype.card I - 1).factorial := by
  rw [Nat.card_congr (labeledExtensionEquiv len e)]
  exact card_cyclicExtensions len hc

/-- A displayed path partition has one more vertex than arc per component. -/
theorem card_labels [Fintype I] [Finite V] (len : I → ℕ) (e : Vertex len ≃ V) :
    Nat.card V = (∑ i, len i) + Fintype.card I := by
  classical
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  simp [Vertex, Fintype.card_sigma, Finset.sum_add_distrib]

/-- The usual `(m-k-1)!` formula, with `k` counting actual prescribed arcs. -/
theorem card_labeled_cyclicExtensions_sub [Fintype I] [Finite V]
    (len : I → ℕ) (e : Vertex len ≃ V) (hc : 2 ≤ Fintype.card I) :
    Nat.card {σ : Perm V // PreservesAlong len e σ ∧ σ.IsCycleOn Set.univ} =
      (Nat.card V - (∑ i, len i) - 1).factorial := by
  rw [card_labeled_cyclicExtensions len e hc, card_labels len e, Nat.add_sub_cancel_left]

/-- A full cyclic permutation cannot leave a nonempty proper set invariant. -/
theorem not_isCycleOn_of_closed_proper [Finite V] (σ : Perm V) (s : Set V)
    (hne : s.Nonempty) (hproper : s ≠ Set.univ) (hclosed : Set.MapsTo σ s s) :
    ¬ σ.IsCycleOn Set.univ := by
  intro hσ
  obtain ⟨x, hx⟩ := hne
  apply hproper
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨n, hn⟩ := hσ.exists_pow_eq' Set.finite_univ (Set.mem_univ x) (Set.mem_univ y)
  have hp : ∀ n : ℕ, (σ ^ n) x ∈ s := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => simpa only [pow_succ', Equiv.Perm.mul_apply] using hclosed ih
  simpa only [hn] using hp n

/-- Constraints forcing a closed nonempty proper set admit zero full cyclic extensions. -/
theorem card_closed_cyclicExtensions_eq_zero [Finite V] (P : Perm V → Prop)
    (s : Set V) (hne : s.Nonempty) (hproper : s ≠ Set.univ)
    (hclosed : ∀ σ, P σ → Set.MapsTo σ s s) :
    Nat.card {σ : Perm V // P σ ∧ σ.IsCycleOn Set.univ} = 0 := by
  let : IsEmpty {σ : Perm V // P σ ∧ σ.IsCycleOn Set.univ} :=
    ⟨fun σ => not_isCycleOn_of_closed_proper σ.1 s hne hproper
      (hclosed σ.1 σ.2.1) σ.2.2⟩
  exact Nat.card_of_isEmpty

end Relabel

end Erdos585.PathContraction
