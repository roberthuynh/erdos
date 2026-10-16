import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic

/- 





-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

universe u
namespace Erdos585.QB6C02TwoScar
open Finset

def resourcePotential (B s : ℤ) : ℤ :=
  if s < 2 then
    if 9 ≤ B then 6 else if 6 ≤ B then 4 else if 3 ≤ B then 2 else 0
  else
    if 8 ≤ B then 7 else if 5 ≤ B then 5 else if 4 ≤ B then 3 else if 3 ≤ B then 2 else 0

lemma resourcePotential_nonneg (B s : ℤ)
    (_hB0 : 0 ≤ B) (_hB : B ≤ 10) (_hs0 : 0 ≤ s) (_hs : s ≤ 2) :
    0 ≤ resourcePotential B s := by
  unfold resourcePotential
  split_ifs <;> omega

lemma resourcePotential_step (B s b a delta d : ℤ)
    (hB0 : 0 ≤ B) (hB : B ≤ 10) (hs0 : 0 ≤ s) (hs : s ≤ 2)
    (hb0 : 0 ≤ b) (hb : b ≤ B) (ha0 : 0 ≤ a) (ha : a ≤ s) (hdpos : 0 < delta)
    (hc : (b = 3 ∧ a = 0 ∧ delta ≤ 2) ∨
      (-2 ≤ d ∧ d ≤ 1 ∧ 6 + d - a ≤ b ∧ delta ≤ 1 + 2 * d + a)) :
    delta + resourcePotential (B - b) (s - a) ≤ resourcePotential B s := by
  rcases hc with hsmall | hlarge
  · obtain ⟨hb3, ha0', hdel⟩ := hsmall
    unfold resourcePotential
    split_ifs <;> omega
  · obtain ⟨hdlo, hdhi, hcost, hdel⟩ := hlarge
    unfold resourcePotential
    split_ifs <;> omega

lemma resource_family_bound {I : Type u} [DecidableEq I] (F : Finset I)
    (b a delta d : I → ℤ) (B s : ℤ)
    (hB0 : 0 ≤ B) (hB : B ≤ 10) (hs0 : 0 ≤ s) (hs : s ≤ 2)
    (hb0 : ∀ i ∈ F, 0 ≤ b i) (ha0 : ∀ i ∈ F, 0 ≤ a i) (hd0 : ∀ i ∈ F, 0 ≤ delta i)
    (hcost : ∑ i ∈ F, b i ≤ B) (hscar : ∑ i ∈ F, a i ≤ s)
    (hc : ∀ i ∈ F, (b i = 3 ∧ a i = 0 ∧ delta i ≤ 2) ∨
      (-2 ≤ d i ∧ d i ≤ 1 ∧ 6 + d i - a i ≤ b i ∧ delta i ≤ 1 + 2 * d i + a i)) :
    (∑ i ∈ F, delta i) ≤ resourcePotential B s := by
  induction F using Finset.induction_on generalizing B s with
  | empty => simpa only [sum_empty] using resourcePotential_nonneg B s hB0 hB hs0 hs
  | @insert i F hi ih =>
    have hbFi : 0 ≤ b i := hb0 i (mem_insert_self i F)
    have haFi : 0 ≤ a i := ha0 i (mem_insert_self i F)
    have hdFi : 0 ≤ delta i := hd0 i (mem_insert_self i F)
    have hbF : ∀ j ∈ F, 0 ≤ b j := fun j hj => hb0 j (mem_insert_of_mem hj)
    have haF : ∀ j ∈ F, 0 ≤ a j := fun j hj => ha0 j (mem_insert_of_mem hj)
    have hdF : ∀ j ∈ F, 0 ≤ delta j := fun j hj => hd0 j (mem_insert_of_mem hj)
    have hcF : ∀ j ∈ F, (b j = 3 ∧ a j = 0 ∧ delta j ≤ 2) ∨
      (-2 ≤ d j ∧ d j ≤ 1 ∧ 6 + d j - a j ≤ b j ∧ delta j ≤ 1 + 2 * d j + a j) :=
      fun j hj => hc j (mem_insert_of_mem hj)
    rw [sum_insert hi] at hcost hscar ⊢
    have hbSum : (0 : ℤ) ≤ ∑ j ∈ F, b j := sum_nonneg hbF
    have haSum : (0 : ℤ) ≤ ∑ j ∈ F, a j := sum_nonneg haF
    by_cases hdz : delta i = 0
    · have hh := ih B s hB0 hB hs0 hs hbF haF hdF (by omega) (by omega) hcF
      omega
    · have hh := ih (B - b i) (s - a i) (by omega) (by omega) (by omega) (by omega)
        hbF haF hdF (by omega) (by omega) hcF
      have hstep := resourcePotential_step B s (b i) (a i) (delta i) (d i)
        hB0 hB hs0 hs hbFi (by omega) haFi (by omega) (by omega) (hc i (mem_insert_self i F))
      omega

lemma resource_budget_seven {I : Type u} [DecidableEq I] (F : Finset I)
    (b a delta d : I → ℤ)
    (hb0 : ∀ i ∈ F, 0 ≤ b i) (ha0 : ∀ i ∈ F, 0 ≤ a i) (hd0 : ∀ i ∈ F, 0 ≤ delta i)
    (hcost : ∑ i ∈ F, b i ≤ 10) (hscar : ∑ i ∈ F, a i ≤ 2)
    (hc : ∀ i ∈ F, (b i = 3 ∧ a i = 0 ∧ delta i ≤ 2) ∨
      (-2 ≤ d i ∧ d i ≤ 1 ∧ 6 + d i - a i ≤ b i ∧ delta i ≤ 1 + 2 * d i + a i)) :
    (∑ i ∈ F, delta i) ≤ 7 := by
  have hh := resource_family_bound F b a delta d 10 2 (by omega) (by omega) (by omega) (by omega)
    hb0 ha0 hd0 hcost hscar hc
  norm_num [resourcePotential] at hh
  exact hh

/-- The requested literal Nat-resource ledger, including empty and arbitrary finite families. -/
theorem two_scar_int {I : Type u} [DecidableEq I] (F : Finset I)
    (d delta : I → ℤ) (B scar : I → ℕ)
    (hdelta : ∀ i ∈ F, 0 ≤ delta i)
    (hitem : ∀ i ∈ F,
      (d i = 1 ∧ B i = 3 ∧ scar i = 0 ∧ delta i ≤ 2) ∨
      (-2 ≤ d i ∧ d i ≤ 1 ∧ 6 + d i - (scar i : ℤ) ≤ (B i : ℤ) ∧
        delta i ≤ 1 + 2 * d i + (scar i : ℤ)))
    (hB : ∑ i ∈ F, B i ≤ 10) (hscar : ∑ i ∈ F, scar i ≤ 2) :
    (∑ i ∈ F, delta i) ≤ 7 := by
  have hBI : (∑ i ∈ F, (B i : ℤ)) ≤ 10 := by exact_mod_cast hB
  have hscarI : (∑ i ∈ F, (scar i : ℤ)) ≤ 2 := by exact_mod_cast hscar
  apply resource_budget_seven F (fun i => (B i : ℤ)) (fun i => (scar i : ℤ)) delta d
    (fun _ _ => Int.natCast_nonneg _) (fun _ _ => Int.natCast_nonneg _) hdelta hBI hscarI
  intro i hi
  rcases hitem i hi with hsmall | hlarge
  · obtain ⟨_, hb, ha, hd⟩ := hsmall
    exact Or.inl ⟨by exact_mod_cast hb, by exact_mod_cast ha, hd⟩
  · exact Or.inr hlarge

end Erdos585.QB6C02TwoScar
