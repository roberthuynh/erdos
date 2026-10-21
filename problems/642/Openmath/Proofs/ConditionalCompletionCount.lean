import Openmath.Proofs.CyclicConstraintCount
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite conditional completion counts

Ordinary pairing constraints and pairing-dependent endpoint cycle constraints
are bounded by summing fibers. Independent colors are combined only afterwards.
The probability is a normalized finite rational count, not a sampler law.
-/

namespace Erdos585.ConditionalCompletionCount

open Equiv
open scoped BigOperators

variable {S C E F : Type*}

abbrev PairEvent (r : Finset (S × S)) :=
  {σ : Perm S // ∀ a ∈ r, σ a.1 = a.2}

/-- A witnessed tail event is a coset of the pointwise stabilizer. -/
noncomputable def tailEquivFixed (s : Finset S) (ρ : Perm S) :
    {σ : Perm S // ∀ x ∈ s, σ x = ρ x} ≃
      {σ : Perm S // ∀ x ∈ s, σ x = x} where
  toFun σ := ⟨ρ.symm * σ.1, fun x hx => by simp [Perm.mul_apply, σ.2 x hx]⟩
  invFun σ := ⟨ρ * σ.1, fun x hx => by simp [Perm.mul_apply, σ.2 x hx]⟩
  left_inv σ := by apply Subtype.ext; ext x; simp [Perm.mul_apply]
  right_inv σ := by apply Subtype.ext; ext x; simp [Perm.mul_apply]

/-- Arbitrary ordinary permutation constraints, including inconsistent data. -/
theorem card_pairEvent_le [Fintype S] [DecidableEq S] (r : Finset (S × S)) :
    Nat.card (PairEvent r) ≤ (Fintype.card S - r.card).factorial := by
  classical
  by_cases hne : Nonempty (PairEvent r)
  · obtain ⟨ρ⟩ := hne
    let s := r.image Prod.fst
    have hs : s.card = r.card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      exact Prod.ext hab ((ρ.2 a ha).symm.trans ((congrArg ρ.1 hab).trans (ρ.2 b hb)))
    have hp (σ : Perm S) : (∀ a ∈ r, σ a.1 = a.2) ↔ ∀ x ∈ s, σ x = ρ.1 x := by
      constructor
      · intro h x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact (h a ha).trans (ρ.2 a ha).symm
      · intro h a ha
        exact (h a.1 (Finset.mem_image.mpr ⟨a, ha, rfl⟩)).trans (ρ.2 a ha)
    let e := (Equiv.subtypeEquivRight hp).trans (tailEquivFixed s ρ.1)
    let e' : {σ : Perm S // ∀ x ∈ s, σ x = x} ≃ Perm {x : S // x ∉ s} :=
      (Equiv.subtypeEquivRight (fun σ => by simp)).trans
        (Perm.subtypeEquivSubtypePerm (fun x : S => x ∉ s)).symm
    rw [Nat.card_congr (e.trans e'), Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl, Fintype.card_coe, hs]
  · let : IsEmpty (PairEvent r) := not_nonempty_iff.mp hne
    simp

/-- The empty shore is covered: its only constraint set is empty. -/
theorem matching_factorial_ratio_le (n k : ℕ) (hk : 2 * k ≤ n) :
    ((n - k).factorial : ℚ) / (n.factorial : ℚ) ≤ (2 / (n : ℚ)) ^ k := by
  by_cases hn : n = 0
  · have hzero : k = 0 := by omega
    simp [hn, hzero]
  have hkn : k ≤ n := by omega
  have hnat : (n - k).factorial * (n - k + 1) ^ k ≤ n.factorial := by
    simpa only [Nat.sub_add_cancel hkn] using
      (Nat.factorial_mul_pow_le_factorial (m := n - k) (n := k))
  have hcast : ((n - k).factorial : ℚ) * ((n - k + 1 : ℕ) : ℚ) ^ k ≤
      (n.factorial : ℚ) := by exact_mod_cast hnat
  have hhalf : (n : ℚ) / 2 ≤ ((n - k + 1 : ℕ) : ℚ) := by
    rw [Nat.cast_add, Nat.cast_sub hkn]
    have hh : 2 * (k : ℚ) ≤ (n : ℚ) := by exact_mod_cast hk
    norm_num only [Nat.cast_one]
    linarith
  have hp : 0 < (n : ℚ) / 2 := by
    have hh : 0 < n := Nat.pos_of_ne_zero hn
    positivity
  have hprod : ((n - k).factorial : ℚ) * ((n : ℚ) / 2) ^ k ≤
      (n.factorial : ℚ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le hhalf k) (by positivity)).trans hcast
  calc
    ((n - k).factorial : ℚ) / (n.factorial : ℚ) ≤ 1 / ((n : ℚ) / 2) ^ k := by
      apply (div_le_div_iff₀ (by positivity) (pow_pos hp k)).mpr
      simpa using hprod
    _ = (2 / (n : ℚ)) ^ k := by rw [← one_div_pow, one_div_div]

noncomputable def uniformPairProbability [Finite S] (r : Finset (S × S)) : ℚ :=
  (Nat.card (PairEvent r) : ℚ) / (Nat.card (Perm S) : ℚ)

theorem uniformPairProbability_le [Fintype S] [DecidableEq S]
    (r : Finset (S × S)) (hk : 2 * r.card ≤ Fintype.card S) :
    uniformPairProbability r ≤ (2 / (Fintype.card S : ℚ)) ^ r.card := by
  have hc : (Nat.card (PairEvent r) : ℚ) ≤
      ((Fintype.card S - r.card).factorial : ℚ) := by exact_mod_cast card_pairEvent_le r
  unfold uniformPairProbability
  rw [Nat.card_perm, show Nat.card S = Fintype.card S from Nat.card_eq_fintype_card]
  exact (div_le_div_of_nonneg_right hc (by positivity)).trans
    (matching_factorial_ratio_le _ _ hk)

/-- Convert actual endpoint units to arcs through the conditioning-dependent bijections. -/
noncomputable def endpointArcs [DecidableEq C] (t : Finset (E × F))
    (e : E ≃ C) (d : F ≃ C) : Finset (C × C) := t.map (e.prodCongr d).toEmbedding

@[simp] theorem card_endpointArcs [DecidableEq C] (t : Finset (E × F))
    (e : E ≃ C) (d : F ≃ C) : (endpointArcs t e d).card = t.card := by
  simp [endpointArcs]

abbrev Cycles (C : Type*) := {τ : Perm C // τ.IsCycleOn Set.univ}
abbrev ColorSample (S C : Type*) := Perm S × Cycles C

/-- The event uses the actual endpoint units, with maps allowed to depend on the pairing. -/
def ColorPredicate (r : Finset (S × S)) (t : Finset (E × F))
    (e : Perm S → E ≃ C) (d : Perm S → F ≃ C) (z : ColorSample S C) : Prop :=
  (∀ a ∈ r, z.1 a.1 = a.2) ∧ ∀ a ∈ t, z.2.1 (e z.1 a.1) = d z.1 a.2

abbrev ColorEvent (r : Finset (S × S)) (t : Finset (E × F))
    (e : Perm S → E ≃ C) (d : Perm S → F ≃ C) :=
  {z : ColorSample S C // ColorPredicate r t e d z}

noncomputable def colorFiberEquiv [DecidableEq C]
    (r : Finset (S × S)) (t : Finset (E × F))
    (e : Perm S → E ≃ C) (d : Perm S → F ≃ C) :
    ColorEvent r t e d ≃ Σ σ : PairEvent r,
      Erdos585.CyclicConstraintCount.ArcEvent (endpointArcs t (e σ.1) (d σ.1)) where
  toFun z := ⟨⟨z.1.1, z.2.1⟩, z.1.2.1, by
    constructor
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
      exact z.2.2 b hb
    · exact z.1.2.2⟩
  invFun z := ⟨⟨z.1.1, z.2.1, z.2.2.2⟩, z.1.2, by
    intro a ha
    exact z.2.2.1 _ (Finset.mem_map.mpr ⟨a, ha, rfl⟩)⟩
  left_inv z := by rfl
  right_inv z := by rfl

/-- Sum over pairing fibers; no independence of the two edge predicates is assumed. -/
theorem card_colorEvent_le [Fintype S] [Fintype C] [DecidableEq C]
    (r : Finset (S × S)) (t : Finset (E × F))
    (e : Perm S → E ≃ C) (d : Perm S → F ≃ C)
    (hn : t.card + 2 ≤ Fintype.card C) :
    Nat.card (ColorEvent r t e d) ≤
      Nat.card (PairEvent r) * (Fintype.card C - t.card - 1).factorial := by
  classical
  let : Fintype (PairEvent r) := Fintype.ofFinite _
  rw [Nat.card_congr (colorFiberEquiv r t e d), Nat.card_sigma]
  calc
    _ ≤ ∑ _σ : PairEvent r, (Fintype.card C - t.card - 1).factorial := by
      apply Finset.sum_le_sum
      intro σ _
      simpa using Erdos585.CyclicConstraintCount.card_arcEvent_le
        (endpointArcs t (e σ.1) (d σ.1)) (by simpa using hn)
    _ = _ := by simp [Nat.card_eq_fintype_card]

noncomputable def uniformColorProbability [Finite S] [Finite C]
    (r : Finset (S × S)) (t : Finset (E × F))
    (e : Perm S → E ≃ C) (d : Perm S → F ≃ C) : ℚ :=
  (Nat.card (ColorEvent r t e d) : ℚ) / (Nat.card (ColorSample S C) : ℚ)

/-- The two free-unit weights for a single color, retaining pairing dependence. -/
theorem uniformColorProbability_le [Fintype S] [Fintype C] [DecidableEq S] [DecidableEq C]
    (r : Finset (S × S)) (t : Finset (E × F))
    (e : Perm S → E ≃ C) (d : Perm S → F ≃ C)
    (hs : 2 * r.card ≤ Fintype.card S)
    (hc : t.card + 2 ≤ Fintype.card C) (ht : 2 * t.card ≤ Fintype.card C) :
    uniformColorProbability r t e d ≤
      (2 / (Fintype.card S : ℚ)) ^ r.card * (2 / (Fintype.card C : ℚ)) ^ t.card := by
  have hb : (Nat.card (ColorEvent r t e d) : ℚ) ≤
      (Nat.card (PairEvent r) : ℚ) * ((Fintype.card C - t.card - 1).factorial : ℚ) := by
    exact_mod_cast card_colorEvent_le r t e d hc
  have hden : Nat.card (ColorSample S C) =
      Nat.card (Perm S) * (Fintype.card C - 1).factorial := by
    rw [Nat.card_prod, Erdos585.PathContraction.card_fullCycles (by omega)]
  unfold uniformColorProbability
  rw [hden, Nat.cast_mul]
  calc
    _ ≤ ((Nat.card (PairEvent r) : ℚ) * ((Fintype.card C - t.card - 1).factorial : ℚ)) /
        ((Nat.card (Perm S) : ℚ) * ((Fintype.card C - 1).factorial : ℚ)) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = uniformPairProbability r *
        (((Fintype.card C - t.card - 1).factorial : ℚ) /
          ((Fintype.card C - 1).factorial : ℚ)) := by
      exact mul_div_mul_comm _ _ _ _
    _ ≤ _ := mul_le_mul (uniformPairProbability_le r hs)
      (Erdos585.CyclicConstraintCount.factorial_ratio_le _ _ hc ht)
      (by positivity) (by positivity)

/-- Coordinate-local event counts factor on the full product sample space. -/
theorem normalized_product {I : Type*} [Fintype I] {A : I → Type*} [∀ i, Finite (A i)]
    (p : ∀ i, A i → Prop) :
    (Nat.card {z : ∀ i, A i // ∀ i, p i (z i)} : ℚ) / (Nat.card (∀ i, A i) : ℚ) =
      ∏ i, (Nat.card {z : A i // p i z} : ℚ) / (Nat.card (A i) : ℚ) := by
  rw [Nat.card_congr Equiv.subtypePiEquivPi, Nat.card_pi, Nat.card_pi]
  simp only [Nat.cast_prod, Finset.prod_div_distrib]

/-- Independent colors retain the actual endpoint predicate in each coordinate. -/
theorem uniformColorsProbability_le {I : Type*} [Fintype I]
    {S C E F : I → Type*} [∀ i, Fintype (S i)] [∀ i, Fintype (C i)]
    [∀ i, DecidableEq (S i)] [∀ i, DecidableEq (C i)]
    (r : ∀ i, Finset (S i × S i)) (t : ∀ i, Finset (E i × F i))
    (e : ∀ i, Perm (S i) → E i ≃ C i) (d : ∀ i, Perm (S i) → F i ≃ C i)
    (hs : ∀ i, 2 * (r i).card ≤ Fintype.card (S i))
    (hc : ∀ i, (t i).card + 2 ≤ Fintype.card (C i))
    (ht : ∀ i, 2 * (t i).card ≤ Fintype.card (C i)) :
    (Nat.card {z : ∀ i, ColorSample (S i) (C i) //
        ∀ i, ColorPredicate (r i) (t i) (e i) (d i) (z i)} : ℚ) /
      (Nat.card (∀ i, ColorSample (S i) (C i)) : ℚ) ≤
    ∏ i, (2 / (Fintype.card (S i) : ℚ)) ^ (r i).card *
      (2 / (Fintype.card (C i) : ℚ)) ^ (t i).card := by
  rw [normalized_product]
  apply Finset.prod_le_prod
  · intro i _
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro i _
    exact uniformColorProbability_le (r i) (t i) (e i) (d i) (hs i) (hc i) (ht i)

/-- The full color sample is nonempty under the exposed cycle domain. -/
theorem colorSample_card_pos [Fintype S] [Fintype C]
    (hc : 2 ≤ Fintype.card C) : 0 < Nat.card (ColorSample S C) := by
  classical
  rw [Nat.card_prod, Nat.card_perm,
    Erdos585.PathContraction.card_fullCycles (by omega)]
  exact Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)

/-- In the completion, the added edge is u--M(τ(u)).  This event is expressed
on those actual endpoint pairs rather than on a supplied arc set. -/
theorem uniformEndpointColorsProbability_le {I : Type*} [Fintype I]
    {S U V : I → Type*} [∀ i, Fintype (S i)] [∀ i, Fintype (U i)]
    [∀ i, DecidableEq (S i)] [∀ i, DecidableEq (U i)]
    (r : ∀ i, Finset (S i × S i)) (t : ∀ i, Finset (U i × V i))
    (M : ∀ i, Perm (S i) → U i ≃ V i)
    (hs : ∀ i, 2 * (r i).card ≤ Fintype.card (S i))
    (hc : ∀ i, (t i).card + 2 ≤ Fintype.card (U i))
    (ht : ∀ i, 2 * (t i).card ≤ Fintype.card (U i)) :
    (Nat.card {z : ∀ i, ColorSample (S i) (U i) // ∀ i,
      (∀ a ∈ r i, (z i).1 a.1 = a.2) ∧
      ∀ a ∈ t i, M i (z i).1 ((z i).2.1 a.1) = a.2} : ℚ) /
      (Nat.card (∀ i, ColorSample (S i) (U i)) : ℚ) ≤
    ∏ i, (2 / (Fintype.card (S i) : ℚ)) ^ (r i).card *
      (2 / (Fintype.card (U i) : ℚ)) ^ (t i).card := by
  have heq : ∀ z : ∀ i, ColorSample (S i) (U i),
      (∀ i, (∀ a ∈ r i, (z i).1 a.1 = a.2) ∧
        ∀ a ∈ t i, M i (z i).1 ((z i).2.1 a.1) = a.2) ↔
      ∀ i, ColorPredicate (r i) (t i) (fun _ => Equiv.refl (U i))
        (fun σ => (M i σ).symm) (z i) := by
    intro z
    apply forall_congr'
    intro i
    apply and_congr Iff.rfl
    apply forall_congr'
    intro a
    apply forall_congr'
    intro _
    exact (M i (z i).1).eq_symm_apply.symm
  rw [Nat.card_congr (Equiv.subtypeEquivRight heq)]
  exact uniformColorsProbability_le r t (fun i _ => Equiv.refl (U i))
    (fun i σ => (M i σ).symm) hs hc ht

/-- The block-weight form used by the completion, including zero isolated shores.
Only the total number of prescribed labeled free units is bounded. -/
theorem uniformEndpointColorsProbability_le_blockWeights {I : Type*} [Fintype I]
    {S U V : I → Type*} [∀ i, Fintype (S i)] [∀ i, Fintype (U i)]
    [∀ i, DecidableEq (S i)] [∀ i, DecidableEq (U i)]
    (r : ∀ i, Finset (S i × S i)) (t : ∀ i, Finset (U i × V i))
    (M : ∀ i, Perm (S i) → U i ≃ V i)
    (b : ℕ) (s c : I → ℕ) (hb : 4 ≤ b) (hc : ∀ i, 1 ≤ c i)
    (hS : ∀ i, Fintype.card (S i) = s i * b)
    (hU : ∀ i, Fintype.card (U i) = c i * b)
    (hunits : 2 * (∑ i, ((r i).card + (t i).card)) ≤ b) :
    (Nat.card {z : ∀ i, ColorSample (S i) (U i) // ∀ i,
      (∀ a ∈ r i, (z i).1 a.1 = a.2) ∧
      ∀ a ∈ t i, M i (z i).1 ((z i).2.1 a.1) = a.2} : ℚ) /
      (Nat.card (∀ i, ColorSample (S i) (U i)) : ℚ) ≤
    ∏ i, ((2 / (s i : ℚ)) / (b : ℚ)) ^ (r i).card *
      ((2 / (c i : ℚ)) / (b : ℚ)) ^ (t i).card := by
  have hi (i : I) : 2 * ((r i).card + (t i).card) ≤ b := by
    have hh := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
        Nat.zero_le ((r j).card + (t j).card)) (Finset.mem_univ i)
    omega
  have hm (i : I) : b ≤ Fintype.card (U i) := by
    rw [hU]
    have hh := hc i
    nlinarith
  have hs (i : I) : 2 * (r i).card ≤ Fintype.card (S i) := by
    by_cases hz : s i = 0
    · have hn : Fintype.card (S i) = 0 := by simp [hS i, hz]
      have hr := (r i).card_le_univ
      simp only [Fintype.card_prod, hn, zero_mul] at hr
      omega
    · have hh := hi i
      rw [hS]
      have hpos : 1 ≤ s i := by omega
      nlinarith
  have hout := uniformEndpointColorsProbability_le r t M hs
    (fun i => by have := hi i; have := hm i; omega)
    (fun i => by have := hi i; have := hm i; omega)
  simpa only [hS, hU, Nat.cast_mul, div_mul_eq_div_div] using hout

end Erdos585.ConditionalCompletionCount
