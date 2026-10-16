/-
Copyright 2026 Robert Huynh.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Openmath.Proofs.PaperSupport.QB6E6Lean
import Openmath.Proofs.QB5.KL1Merge

/- 




-/

open Finset
namespace Erdos585.QB6CoveredFive
open QB4 QB5 QB6E6 QB6E6Lean

universe u
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A C T J T' : Finset V} {m : V → ℕ}

set_option maxHeartbeats 2000000

structure FiveData (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (m : V → ℕ) : Prop where
  block : ScarBlock G A C
  msum_eq : msum m A = 5
  le_delta : ∀ a ∈ A, m a + dg G C a ≤ 6

namespace FiveData

omit [DecidableEq V] in
lemma msum_le (h : FiveData G A C m) (hT : T ⊆ A) : msum m T ≤ 5 :=
  h.msum_eq ▸ msum_mono m hT

omit [DecidableEq V] in
lemma m_le_three (h : FiveData G A C m) {a : V} (ha : a ∈ A) : m a ≤ 3 := by
  have := h.le_delta a ha
  have := h.block.minA a ha
  omega

omit [DecidableEq V] in
lemma wsum_eq_eight (h : FiveData G A C m) : wsum G m C A = 8 := by
  rw [wsum_eq, h.block.edges, h.msum_eq, h.block.card]
  push_cast
  ring

omit [DecidableEq V] in
lemma sum_f_eq_two (h : FiveData G A C m) :
    ∑ a ∈ A, (3 * (m a : ℤ) - 6 + dg G C a) = 2 := by
  change (∑ a ∈ A, rowWeight G m C a) = 2
  rw [← row_weight_sum]
  rw [h.msum_eq, h.wsum_eq_eight]
  norm_num

omit [DecidableEq V] in
lemma wsum_nonneg' (h : FiveData G A C m) (hT : T ⊆ A) : 0 ≤ wsum G m C T :=
  wsum_nonneg h.le_delta hT

end FiveData

omit [DecidableEq V] in
lemma theta_le_large (h : ScarBlock G A C) (m : V → ℕ)
    (hT : T ⊆ A) (hJ : J ⊆ C) (h3 : 3 ≤ #T + #J) :
    theta G m T J ≤ msum m T - 3 - ((#T : ℤ) - #J) := by
  have hg := h.sparse T hT J hJ h3
  have ht := two_mul_theta (G := G) m T J
  linarith

lemma thetaStar_le_two (h : FiveData G A C m) (hT : T ⊆ A) (h3 : 3 ≤ #T) :
    thetaStar G m C T ≤ 2 := by
  have hb := shifted_theta_bound (m := m) h.block.sparse hT (cpr_subset (G := G) C T) (by omega)
  rw [theta_cpr] at hb
  have hm := h.msum_le hT
  have hw := h.wsum_nonneg' hT
  have he : (0 : ℤ) ≤ ec G T (C \ cpr G C T) := Nat.cast_nonneg _
  omega

lemma kappa_bounds (h : FiveData G A C m) (hT : T ⊆ A) (hJ : J ⊆ C)
    (h3 : 3 ≤ #T + #J) (h1 : 1 ≤ theta G m T J) :
    -1 ≤ (#T : ℤ) - #J ∧ (#T : ℤ) - #J ≤ msum m T - 4 := by
  have hb := theta_le_large h.block m hT hJ h3
  have ht := theta_eq_four_add (G := G) m hJ T
  have hw := h.wsum_nonneg' hT
  have he : (0 : ℤ) ≤ ec G T (C \ J) := Nat.cast_nonneg _
  omega

lemma big_supply (h : FiveData G A C m) (hT : T ⊆ A) (h3 : 3 ≤ #T)
    (h1 : 1 ≤ thetaStar G m C T) :
    3 ≤ msum m T ∧ -1 ≤ (#T : ℤ) - #(cpr G C T) ∧
      (#T : ℤ) - #(cpr G C T) ≤ msum m T - 4 := by
  rw [← theta_cpr] at h1
  have hk := kappa_bounds h hT (cpr_subset C T) (by omega) h1
  exact ⟨by omega, hk⟩

omit [DecidableEq V] in
lemma cpr_nonempty (hm : msum m T ≤ 5) (h3 : 3 ≤ #T)
    (h1 : 1 ≤ thetaStar G m C T) : (cpr G C T).Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro he
  rw [← theta_cpr, he] at h1
  have hz : ec G T ∅ = 0 := by simp [ec, dg]
  simp only [theta, card_empty, hz, CharP.cast_eq_zero, add_zero] at h1
  omega

lemma merge_card_ne_two (h : FiveData G A C m) (hT : T ⊆ A)
    (h1 : 1 ≤ thetaStar G m C T) (h1' : 1 ≤ thetaStar G m C T')
    (hU : thetaStar G m C (T ∪ T') ≤ 0) : #(T ∩ T') ≠ 2 := by
  intro hi
  have hb := merge_thetaStar_inter hU
  rw [thetaStar_of_card_eq_two m C hi] at hb
  have hm := h.msum_le ((inter_subset_left (s₂ := T')).trans hT)
  linarith

lemma merge_N3 (h : FiveData G A C m) (hT : T ⊆ A)
    (h1 : 1 ≤ thetaStar G m C T) (h1' : 1 ≤ thetaStar G m C T')
    (hU : thetaStar G m C (T ∪ T') ≤ 0) (h3 : 3 ≤ #(T ∩ T')) :
    thetaStar G m C (T ∩ T') = 2 ∧ thetaStar G m C T = 1 ∧ thetaStar G m C T' = 1 := by
  have hb := merge_thetaStar_inter hU
  have ht := thetaStar_le_two h (inter_subset_left.trans hT) h3
  omega

def CoveredByOverloads (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (m : V → ℕ) : Prop :=
  ∀ p ∈ A, ∃ T ⊆ A, p ∈ T ∧ 1 ≤ thetaStar G m C T

lemma no_max_pair (h : FiveData G A C m) (hall : CoveredByOverloads G A C m)
    (hT : IsMaxOver G m A C T) : #T ≠ 2 := by
  classical
  intro hT2
  have hmT : msum m T = 5 := by
    have ht := hT.2.1
    rw [thetaStar_of_card_eq_two m C hT2] at ht
    have hb := h.msum_le hT.1
    omega
  obtain ⟨a, b, hab, hTab, hma, hmb⟩ :
      ∃ a b, a ≠ b ∧ T = {a, b} ∧ m a = 3 ∧ m b = 2 := by
    obtain ⟨a, b, hab, hTab⟩ := card_eq_two.1 hT2
    have haA := hT.1 (hTab ▸ mem_insert_self a {b})
    have hbA := hT.1 (hTab ▸ mem_insert_of_mem (mem_singleton_self b))
    have hma := h.m_le_three haA
    have hmb := h.m_le_three hbA
    rw [hTab, msum, sum_pair hab] at hmT
    rcases (by omega : m a = 3 ∧ m b = 2 ∨ m b = 3 ∧ m a = 2) with hm | hm
    · exact ⟨a, b, hab, hTab, hm⟩
    · exact ⟨b, a, hab.symm, hTab.trans (pair_comm a b), hm⟩
  have haT : a ∈ T := hTab ▸ mem_insert_self a {b}
  have hbT : b ∈ T := hTab ▸ mem_insert_of_mem (mem_singleton_self b)
  have haA := hT.1 haT
  have hbA := hT.1 hbT
  have hda : dg G C a = 3 := by
    have := h.le_delta a haA
    have := h.block.minA a haA
    omega
  have herase : msum m (A.erase a) = 2 := by
    have he := sum_erase_add A (fun x => (m x : ℤ)) haA
    change msum m (A.erase a) + (m a : ℤ) = msum m A at he
    rw [hma, h.msum_eq] at he
    omega
  have bigfacts : ∀ S, IsMaxOver G m A C S → 3 ≤ #S →
      a ∈ S ∧ b ∉ S ∧ msum m S = 3 ∧ thetaStar G m C S = 1 ∧
      (#S : ℤ) - #(cpr G C S) = -1 ∧ gv G S (cpr G C S) = 14 ∧
      dg G (cpr G C S) a = 3 := by
    intro S hS hS3
    have hmS := (big_supply h hS.1 hS3 hS.2.1).1
    have haS : a ∈ S := by
      by_contra hn
      have hs : S ⊆ A.erase a := fun x hx => mem_erase.2 ⟨fun he => hn (he ▸ hx), hS.1 hx⟩
      have hb := msum_mono m hs
      omega
    have hbS : b ∉ S := by
      intro hb
      have htS : T ⊆ S := by rw [hTab]; exact insert_subset haS (singleton_subset_iff.2 hb)
      have he := hT.2.2 S hS.1 htS hS.2.1
      rw [he] at hS3
      omega
    have hms3 : msum m S = 3 := by
      have hbe : msum m (A.erase b) = 3 := by
        have he := sum_erase_add A (fun x => (m x : ℤ)) hbA
        change msum m (A.erase b) + (m b : ℤ) = msum m A at he
        rw [hmb, h.msum_eq] at he
        omega
      have hs : S ⊆ A.erase b := fun x hx => mem_erase.2 ⟨fun he => hbS (he ▸ hx), hS.1 hx⟩
      have hl := msum_mono m hs
      omega
    have hk := big_supply h hS.1 hS3 hS.2.1
    have hpos := hS.2.1
    have ht := theta_le_large h.block m hS.1 (cpr_subset (G := G) C S) (by omega)
    rw [theta_cpr] at ht
    have htheta : thetaStar G m C S = 1 := by omega
    have hkap : (#S : ℤ) - #(cpr G C S) = -1 := by omega
    have hg : gv G S (cpr G C S) = 14 := by
      have he := two_mul_theta (G := G) m S (cpr G C S)
      rw [theta_cpr, htheta, hms3] at he
      linarith
    have hcn := cpr_nonempty (h.msum_le hS.1) hS3 hS.2.1
    have hc : 3 ≤ #(S.erase a) + #(cpr G C S) := by
      rw [card_erase_of_mem haS]
      have := hcn.card_pos
      omega
    have hsp := h.block.sparse (S.erase a) ((erase_subset a S).trans hS.1)
      (cpr G C S) (cpr_subset C S) hc
    rw [gv_erase_left haS, hg] at hsp
    have hd := dg_mono (G := G) (cpr_subset (G := G) C S) a
    have hdeg : dg G (cpr G C S) a = 3 := by omega
    exact ⟨haS, hbS, hms3, htheta, hkap, hg, hdeg⟩
  have unique_big : ∀ S S', IsMaxOver G m A C S → 3 ≤ #S →
      IsMaxOver G m A C S' → 3 ≤ #S' → S = S' := by
    intro S S' hS hS3 hS' hS3'
    by_contra hne
    obtain ⟨haS, _, hmS, htS, _, _, hdS⟩ := bigfacts S hS hS3
    obtain ⟨haS', _, hmS', htS', _, _, hdS'⟩ := bigfacts S' hS' hS3'
    have hu := hS.union_le hS' hne
    have hi : thetaStar G m C (S ∩ S') ≥ 2 := by
      have := merge_thetaStar_inter hu
      omega
    have him : msum m (S ∩ S') ≤ 3 := (msum_mono m inter_subset_left).trans hmS.le
    have hin2 := merge_card_ne_two h hS.1 hS.2.1 hS'.2.1 hu
    have haI : a ∈ S ∩ S' := mem_inter.2 ⟨haS, haS'⟩
    have hipos : 1 ≤ #(S ∩ S') := card_pos.2 ⟨a, haI⟩
    by_cases hi3 : 3 ≤ #(S ∩ S')
    · have hb := theta_le_large (T := S ∩ S') h.block m (inter_subset_left.trans hS.1)
        (cpr_subset (G := G) C (S ∩ S')) (by omega)
      rw [theta_cpr] at hb
      have hk := kappa_bounds (T := S ∩ S') h (inter_subset_left.trans hS.1)
        (cpr_subset (G := G) C (S ∩ S')) (by omega) (by rw [theta_cpr]; omega)
      omega
    · have hc1 : #(S ∩ S') = 1 := by omega
      have hIa : S ∩ S' = {a} := (eq_of_subset_of_card_le
        (singleton_subset_iff.2 haI) (by simp [hc1])).symm
      have hb := merge_N1 hu hIa
      have he := dg_union_add_dg_inter (G := G) (cpr G C S) (cpr G C S') a
      have hd := dg_mono (G := G) (union_subset (cpr_subset (G := G) C S)
        (cpr_subset (G := G) C S')) a
      have hcard := dg_le_card (G := G) (cpr G C S ∩ cpr G C S') a
      rw [hma] at hb
      omega
  have outside_zero : ∀ x ∈ A, x ∉ T → m x = 0 := by
    intro x hx hn
    have hs : insert x T ⊆ A := insert_subset hx hT.1
    have hm := h.msum_le hs
    rw [msum, sum_insert hn] at hm
    change (m x : ℤ) + msum m T ≤ 5 at hm
    omega
  have haway : ∀ x ∈ A, x ∉ T → ∃ S, IsMaxOver G m A C S ∧ 3 ≤ #S ∧ x ∈ S := by
    intro x hx hn
    obtain ⟨S, hs, hxS, ht⟩ := hall x hx
    obtain ⟨S', hSS', hS'⟩ := exists_isMaxOver hs ht
    have hxS' := hSS' hxS
    have hS'3 : 3 ≤ #S' := by
      by_contra hc
      have hm0 := outside_zero x hx hn
      interval_cases he : #S'
      · have hz := card_eq_zero.1 he
        rw [hz] at hxS'
        simp at hxS'
      · have hex : S' = {x} := (eq_of_subset_of_card_le
          (singleton_subset_iff.2 hxS') (by simp [he])).symm
        have ht := hS'.2.1
        rw [hex, thetaStar_singleton, hm0] at ht
        norm_num at ht
      · have ht := hS'.2.1
        rw [thetaStar_of_card_eq_two m C he] at ht
        have hm5 : msum m S' = 5 := by have := h.msum_le hS'.1; omega
        have her : msum m (S'.erase x) = 5 := by
          have he := sum_erase_add S' (fun y => (m y : ℤ)) hxS'
          change msum m (S'.erase x) + (m x : ℤ) = msum m S' at he
          rw [hm0, hm5] at he
          omega
        have hcer : #(S'.erase x) = 1 := by rw [card_erase_of_mem hxS', he]
        obtain ⟨y, hy⟩ := card_eq_one.1 hcer
        rw [hy, msum_singleton] at her
        have hyA : y ∈ A := hS'.1 (erase_subset x S' (hy ▸ mem_singleton_self y))
        have := h.m_le_three hyA
        omega
    exact ⟨S', hS', hS'3, hxS'⟩
  have hex : ∃ x ∈ A, x ∉ T := by
    by_contra! hn
    have hb := card_le_card (fun x hx => hn x hx)
    have := h.block.six
    omega
  obtain ⟨x, hxA, hxT⟩ := hex
  obtain ⟨S, hS, hS3, hxS⟩ := haway x hxA hxT
  have hcover : A.erase b ⊆ S := by
    intro y hy
    obtain ⟨hyb, hyA⟩ := mem_erase.1 hy
    by_cases hya : y = a
    · subst y
      exact (bigfacts S hS hS3).1
    · have hyT : y ∉ T := by rw [hTab]; simp [hya, hyb]
      obtain ⟨S', hS', hS3', hyS'⟩ := haway y hyA hyT
      rw [unique_big S' S hS' hS3' hS hS3] at hyS'
      exact hyS'
  have hsc : #(A.erase b) ≤ #S := card_le_card hcover
  rw [card_erase_of_mem hbA] at hsc
  have hc := card_le_card (cpr_subset (G := G) C S)
  have hk := (bigfacts S hS hS3).2.2.2.2.1
  have hAC := h.block.card
  omega


lemma max_cases (h : FiveData G A C m) (hall : CoveredByOverloads G A C m)
    (hT : IsMaxOver G m A C T) :
    T = ∅ ∨ (∃ u, T = {u} ∧ 1 ≤ m u) ∨ 3 ≤ #T := by
  rcases lt_or_ge #T 3 with hc | hc
  · have hn2 := no_max_pair h hall hT
    have h1 := hT.2.1
    interval_cases he : #T
    · exact Or.inl (card_eq_zero.1 he)
    · obtain ⟨u, rfl⟩ := card_eq_one.1 he
      rw [thetaStar_singleton] at h1
      exact Or.inr (Or.inl ⟨u, rfl, by exact_mod_cast h1⟩)
    · exact absurd rfl hn2
  · exact Or.inr (Or.inr hc)

lemma inter_of_lt (h : FiveData G A C m) (hT : IsMaxOver G m A C T)
    (hT' : IsMaxOver G m A C T') (hne : T ≠ T') (h3 : #(T ∩ T') < 3) :
    T ∩ T' = ∅ ∨ ∃ v, T ∩ T' = {v} ∧
      thetaStar G m C T + thetaStar G m C T' + #(cpr G C T ∩ cpr G C T') ≤ m v := by
  have hU := hT.union_le hT' hne
  have h2 := merge_card_ne_two h hT.1 hT.2.1 hT'.2.1 hU
  interval_cases hc : #(T ∩ T')
  · exact Or.inl (card_eq_zero.1 hc)
  · obtain ⟨v, hv⟩ := card_eq_one.1 hc
    exact Or.inr ⟨v, hv, merge_N1 hU hv⟩
  · exact absurd rfl h2

lemma three_cpr_false (hX : ScarBlock G A C) {T₁ T₂ T₃ : Finset V} (h₁ : T₁ ⊆ A)
    (h₂ : T₂ ⊆ A) (h₃ : T₃ ⊆ A) {v c : V} (h12 : T₁ ∩ T₂ = {v}) (h13 : T₁ ∩ T₃ = {v})
    (h23 : T₂ ∩ T₃ = {v}) (hc : c ∈ C) (hc₁ : 3 ≤ dg G T₁ c) (hc₂ : 3 ≤ dg G T₂ c)
    (hc₃ : 3 ≤ dg G T₃ c) : False := by
  have e1 := dg_union_add_dg_inter (G := G) T₁ T₂ c
  have e2 := dg_union_add_dg_inter (G := G) (T₁ ∪ T₂) T₃ c
  have hi : (T₁ ∪ T₂) ∩ T₃ = {v} := by rw [union_inter_distrib_right, h13, h23, union_self]
  rw [h12] at e1
  rw [hi] at e2
  have hv := dg_le_card (G := G) ({v} : Finset V) c
  rw [card_singleton] at hv
  have hA := dg_mono (G := G) (union_subset (union_subset h₁ h₂) h₃) c
  have hcap := (hX.scar c hc).2
  omega

/-- Double counting over a family of subsets of `A`. -/
lemma sum_sum_eq_sum_filter {ℱ : Finset (Finset V)} (hℱ : ∀ T ∈ ℱ, T ⊆ A)
    (F : V → Finset V → ℤ) :
    ∑ T ∈ ℱ, ∑ v ∈ T, F v T = ∑ v ∈ A, ∑ T ∈ ℱ.filter (fun T => v ∈ T), F v T := by
  have h : ∀ T ∈ ℱ, ∑ v ∈ T, F v T = ∑ v ∈ A, if v ∈ T then F v T else 0 := by
    intro T hT
    rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.2 (hℱ T hT)]
  rw [sum_congr rfl h, sum_comm]
  exact sum_congr rfl fun v _ => (sum_filter _ _).symm

/-- If every `c ∈ C` lies in at most `b` of the sets `t T ⊆ C`, then `Σ_T e(v, t T) ≤ b d_v`. -/
lemma sum_dg_le_mul {ℱ : Finset (Finset V)} (t : Finset V → Finset V)
    (ht : ∀ T ∈ ℱ, t T ⊆ C) (b : ℕ) (hb : ∀ c ∈ C, #(ℱ.filter (fun T => c ∈ t T)) ≤ b)
    (v : V) : ∑ T ∈ ℱ, dg G (t T) v ≤ b * dg G C v := by
  have e1 : ∀ T ∈ ℱ, dg G (t T) v = ∑ c ∈ C.filter (G.Adj v), if c ∈ t T then 1 else 0 := by
    intro T hT
    unfold dg
    rw [← card_filter]
    congr 1
    ext c
    simp only [mem_filter]
    constructor
    · rintro ⟨hc, hadj⟩
      exact ⟨⟨ht T hT hc, hadj⟩, hc⟩
    · rintro ⟨⟨_, hadj⟩, hc⟩
      exact ⟨hc, hadj⟩
  calc ∑ T ∈ ℱ, dg G (t T) v
      = ∑ T ∈ ℱ, ∑ c ∈ C.filter (G.Adj v), if c ∈ t T then 1 else 0 := sum_congr rfl e1
    _ = ∑ c ∈ C.filter (G.Adj v), ∑ T ∈ ℱ, if c ∈ t T then 1 else 0 := sum_comm
    _ = ∑ c ∈ C.filter (G.Adj v), #(ℱ.filter (fun T => c ∈ t T)) :=
        sum_congr rfl fun c _ => (card_filter _ _).symm
    _ ≤ ∑ _c ∈ C.filter (G.Adj v), b := sum_le_sum fun c hc => hb c (mem_filter.1 hc).1
    _ = b * dg G C v := by
        rw [sum_const, smul_eq_mul, mul_comm]
        rfl

omit [DecidableEq V] in
/-- `Σ_{v ∈ T} (3m(v) - 6 + e(v, C'(T))) = 3θ*(T) + g(X'(T)) - 12`: the per-member term of
PAPER4 (3.1), `2m(T) - w(T) - ∂_A(X'(T))`. -/
lemma sum_F_eq (m : V → ℕ) (C T : Finset V) :
    ∑ v ∈ T, (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) =
      3 * thetaStar G m C T + gv G T (cpr G C T) - 12 := by
  have e1 : (ec G T (cpr G C T) : ℤ) = ∑ v ∈ T, (dg G (cpr G C T) v : ℤ) := by
    unfold ec
    push_cast
    rfl
  have e2 : ∑ v ∈ T, (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) =
      3 * msum m T - 6 * #T + ∑ v ∈ T, (dg G (cpr G C T) v : ℤ) := by
    unfold msum
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    ring
  rw [e2, ← theta_cpr]
  unfold theta gv
  rw [e1]
  ring

/-- Under "no two maximal overloaded sets share three vertices", two of them containing `v` meet
exactly in `{v}`, and Lemma 3.2 (N1) applies at `v`. -/
lemma inter_eq_singleton (hK : FiveData G A C m)
    (hno : ∀ T₁ T₂, IsMaxOver G m A C T₁ → IsMaxOver G m A C T₂ → T₁ ≠ T₂ → #(T₁ ∩ T₂) < 3)
    {T T' : Finset V} (hT : IsMaxOver G m A C T) (hT' : IsMaxOver G m A C T') (hne : T ≠ T')
    {v : V} (hv : v ∈ T) (hv' : v ∈ T') :
    T ∩ T' = {v} ∧
      thetaStar G m C T + thetaStar G m C T' + #(cpr G C T ∩ cpr G C T') ≤ m v := by
  have hvi : v ∈ T ∩ T' := mem_inter.2 ⟨hv, hv'⟩
  rcases inter_of_lt hK hT hT' hne (hno T T' hT hT' hne) with h | ⟨w, hw, hle⟩
  · rw [h] at hvi
    simp at hvi
  · rw [hw, mem_singleton] at hvi
    subst hvi
    exact ⟨hw, hle⟩

/-- If every vertex of `A` lies in an overloaded set, a vertex in no maximal overloaded set with at
least three elements lies in a singleton member, so `m(v) ≥ 1`. -/
lemma one_le_m_of_not_big (hK : FiveData G A C m)
    (hall : CoveredByOverloads G A C m) {v : V} (hv : v ∈ A)
    (hnb : ∀ T, IsMaxOver G m A C T → 3 ≤ #T → v ∉ T) : 1 ≤ m v := by
  obtain ⟨T, hTA, hvT, h1⟩ := hall v hv
  obtain ⟨T', hsub, hT'⟩ := exists_isMaxOver hTA h1
  have hvT' := hsub hvT
  rcases max_cases hK hall hT' with h | ⟨u, hu, hmu⟩ | h
  · rw [h] at hvT'
    simp at hvT'
  · rw [hu, mem_singleton] at hvT'
    subst hvT'
    exact hmu
  · exact absurd hvT' (hnb T' hT' h)

theorem exists_hub_pair (hK : FiveData G A C m)
    (hall : CoveredByOverloads G A C m) :
    ∃ T₁ T₂, IsMaxOver G m A C T₁ ∧ IsMaxOver G m A C T₂ ∧ T₁ ≠ T₂ ∧ 3 ≤ #(T₁ ∩ T₂) := by
  classical
  by_contra! hno
  -- the big members of the family
  set ℬ : Finset (Finset V) := A.powerset.filter (fun T => IsMaxOver G m A C T ∧ 3 ≤ #T)
    with hℬ
  have memℬ : ∀ T, T ∈ ℬ ↔ IsMaxOver G m A C T ∧ 3 ≤ #T := fun T => by
    rw [hℬ, mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.1.1, h⟩⟩
  have hℬA : ∀ T ∈ ℬ, T ⊆ A := fun T hT => ((memℬ T).1 hT).1.1
  -- the weight identity (3.1)
  have hid := sum_sum_eq_sum_filter hℬA
    (fun v T => 3 * (m v : ℤ) - 6 + dg G (cpr G C T) v)
  have hf0 := hK.sum_f_eq_two
  -- lower bound for each big member: 2m(T) - w(T) - ∂_A(X'(T)) ≥ 3 + (g(X'(T)) - 12)
  have hlow : ∀ T ∈ ℬ, 3 + (gv G T (cpr G C T) - 12) ≤
      ∑ v ∈ T, (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) := by
    intro T hT
    obtain ⟨hTm, hT3⟩ := (memℬ T).1 hT
    have e := sum_F_eq (G := G) m C T
    have h1 := hTm.2.1
    linarith
  have hgnn : ∀ T ∈ ℬ, 2 ≤ gv G T (cpr G C T) - 12 := fun T hT => by
    obtain ⟨hTm, hT3⟩ := (memℬ T).1 hT
    have := hK.block.sparse T hTm.1 (cpr G C T) (cpr_subset C T) (by omega)
    linarith
  -- the bound at a vertex that is not shared by two big members with `m = 3`
  have hvert : ∀ v ∈ A, ¬ (2 ≤ #(ℬ.filter (fun T => v ∈ T)) ∧ m v = 3) →
      ∑ T ∈ ℬ.filter (fun T => v ∈ T), (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) ≤
        3 * (m v : ℤ) - 6 + dg G C v := by
    intro v hv hnb
    have hd3 := hK.block.minA v hv
    have hm3 := hK.m_le_three hv
    have hsplit : ∑ T ∈ ℬ.filter (fun T => v ∈ T), (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) =
        (#(ℬ.filter (fun T => v ∈ T)) : ℤ) * (3 * (m v : ℤ) - 6) +
          ∑ T ∈ ℬ.filter (fun T => v ∈ T), (dg G (cpr G C T) v : ℤ) := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    rw [hsplit]
    rcases Nat.lt_or_ge #(ℬ.filter (fun T => v ∈ T)) 1 with hk | hk
    · -- `v` lies in no big member: it is a singleton member, `m(v) ≥ 1`
      have hk0 : ℬ.filter (fun T => v ∈ T) = ∅ := card_eq_zero.1 (by omega)
      rw [hk0, sum_empty, card_empty]
      have h1 : 1 ≤ m v := one_le_m_of_not_big hK hall hv fun T hT hT3 hvT => by
        have : T ∈ ℬ.filter (fun T => v ∈ T) := mem_filter.2 ⟨(memℬ T).2 ⟨hT, hT3⟩, hvT⟩
        rw [hk0] at this
        simp at this
      push_cast
      omega
    · -- the sets `C'(T)`, `v ∈ T`, are pairwise disjoint (or there is only one)
      have hdisj : ∑ T ∈ ℬ.filter (fun T => v ∈ T), dg G (cpr G C T) v ≤ 1 * dg G C v := by
        refine sum_dg_le_mul (fun T => cpr G C T) (fun T _ => cpr_subset C T) 1
          (fun c _ => ?_) v
        rw [card_le_one]
        intro T₁ h₁ T₂ h₂
        by_contra hne
        rw [mem_filter, mem_filter] at h₁ h₂
        obtain ⟨⟨hT₁ℬ, hvT₁⟩, hc₁⟩ := h₁
        obtain ⟨⟨hT₂ℬ, hvT₂⟩, hc₂⟩ := h₂
        have hT₁m := ((memℬ _).1 hT₁ℬ).1
        have hT₂m := ((memℬ _).1 hT₂ℬ).1
        obtain ⟨-, hle⟩ := inter_eq_singleton hK hno hT₁m hT₂m hne hvT₁ hvT₂
        have hcc : 0 < #(cpr G C T₁ ∩ cpr G C T₂) := card_pos.2 ⟨c, mem_inter.2 ⟨hc₁, hc₂⟩⟩
        have h2 : 1 < #(ℬ.filter (fun T => v ∈ T)) :=
          one_lt_card.2 ⟨T₁, mem_filter.2 ⟨hT₁ℬ, hvT₁⟩, T₂, mem_filter.2 ⟨hT₂ℬ, hvT₂⟩, hne⟩
        have hm2 : m v ≠ 3 := fun h => hnb ⟨h2, h⟩
        have h1 := hT₁m.2.1
        have h1' := hT₂m.2.1
        omega
      have hdisj' : ∑ T ∈ ℬ.filter (fun T => v ∈ T), (dg G (cpr G C T) v : ℤ) ≤ dg G C v := by
        rw [one_mul] at hdisj
        exact_mod_cast hdisj
      have hkm : (#(ℬ.filter (fun T => v ∈ T)) : ℤ) * (3 * (m v : ℤ) - 6) ≤ 3 * (m v : ℤ) - 6 := by
        by_cases hmv : m v = 3
        · have : #(ℬ.filter (fun T => v ∈ T)) = 1 := by
            by_contra h
            exact hnb ⟨by omega, hmv⟩
          rw [this]
          simp
        · have hx : 3 * (m v : ℤ) - 6 ≤ 0 := by omega
          have hk1 : (1 : ℤ) ≤ #(ℬ.filter (fun T => v ∈ T)) := by exact_mod_cast hk
          have := mul_le_mul_of_nonpos_right hk1 hx
          linarith
      linarith
  by_cases hbad : ∃ v₀ ∈ A, 2 ≤ #(ℬ.filter (fun T => v₀ ∈ T)) ∧ m v₀ = 3
  · -- a vertex `v₀` with `m(v₀) = 3` shared by two big members
    obtain ⟨v₀, hv₀, hk₀, hm₀⟩ := hbad
    have hd₀ : dg G C v₀ = 3 := by
      have := hK.le_delta v₀ hv₀
      have := hK.block.minA v₀ hv₀
      omega
    -- every other vertex has `m ≤ 2`, so the bound applies there
    have hother : ∀ v ∈ A.erase v₀,
        ∑ T ∈ ℬ.filter (fun T => v ∈ T), (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) ≤
          3 * (m v : ℤ) - 6 + dg G C v := by
      intro v hv
      obtain ⟨hne, hvA⟩ := mem_erase.1 hv
      refine hvert v hvA fun ⟨_, hm⟩ => ?_
      have hsub : ({v, v₀} : Finset V) ⊆ A := by
        intro x hx
        rw [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hvA
        · exact hv₀
      have h4 := hK.msum_le hsub
      rw [msum, sum_pair hne] at h4
      omega
    -- every big member contains `v₀`, since it has `m(T) ≥ 3`
    have hall₀ : ∀ T ∈ ℬ, v₀ ∈ T := by
      intro T hT
      obtain ⟨hTm, hT3⟩ := (memℬ T).1 hT
      by_contra hv₀T
      have h2 := (big_supply hK hTm.1 hT3 hTm.2.1).1
      have h3 : msum m T ≤ msum m (A.erase v₀) :=
        msum_mono m fun x hx => mem_erase.2 ⟨fun h => hv₀T (h ▸ hx), hTm.1 hx⟩
      have h4 : msum m (A.erase v₀) + m v₀ = msum m A := by
        unfold msum
        exact sum_erase_add A _ hv₀
      have h5 := hK.msum_eq
      rw [hm₀] at h4
      push_cast at h4
      omega
    have hℬv₀ : ℬ.filter (fun T => v₀ ∈ T) = ℬ := filter_true_of_mem hall₀
    rw [hℬv₀] at hk₀
    -- the identity and the bounds at the vertices
    have hsum : ∑ v ∈ A, ∑ T ∈ ℬ.filter (fun T => v ∈ T),
        (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) ≤
          ∑ T ∈ ℬ, (3 * (m v₀ : ℤ) - 6 + dg G (cpr G C T) v₀) -
            (3 * (m v₀ : ℤ) - 6 + dg G C v₀) + 2 := by
      rw [← add_sum_erase A _ hv₀, hℬv₀]
      have h1 := sum_le_sum hother
      have h2 : ∑ v ∈ A.erase v₀, (3 * (m v : ℤ) - 6 + dg G C v) +
          (3 * (m v₀ : ℤ) - 6 + dg G C v₀) = 2 := by
        rw [sum_erase_add A _ hv₀]
        exact hf0
      linarith
    have hF₀ : ∑ T ∈ ℬ, (3 * (m v₀ : ℤ) - 6 + dg G (cpr G C T) v₀) =
        3 * #ℬ + ∑ T ∈ ℬ, (dg G (cpr G C T) v₀ : ℤ) := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul, hm₀]
      push_cast
      ring
    have hlowsum : ∑ T ∈ ℬ, (3 + (gv G T (cpr G C T) - 12)) =
        3 * #ℬ + ∑ T ∈ ℬ, (gv G T (cpr G C T) - 12) := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      ring
    -- a neighbor of `v₀` lies in at most two of the sets `C'(T)`
    have hdg2 : ∑ T ∈ ℬ, dg G (cpr G C T) v₀ ≤ 2 * dg G C v₀ := by
      refine sum_dg_le_mul (fun T => cpr G C T) (fun T _ => cpr_subset C T) 2
        (fun c hc => ?_) v₀
      by_contra! h3
      obtain ⟨T₁, h₁, T₂, h₂, T₃, h₃, h12, h13, h23⟩ := two_lt_card.1 h3
      rw [mem_filter] at h₁ h₂ h₃
      have hT₁m := ((memℬ _).1 h₁.1).1
      have hT₂m := ((memℬ _).1 h₂.1).1
      have hT₃m := ((memℬ _).1 h₃.1).1
      exact three_cpr_false hK.block hT₁m.1 hT₂m.1 hT₃m.1
        (inter_eq_singleton hK hno hT₁m hT₂m h12 (hall₀ _ h₁.1) (hall₀ _ h₂.1)).1
        (inter_eq_singleton hK hno hT₁m hT₃m h13 (hall₀ _ h₁.1) (hall₀ _ h₃.1)).1
        (inter_eq_singleton hK hno hT₂m hT₃m h23 (hall₀ _ h₂.1) (hall₀ _ h₃.1)).1
        hc (mem_cpr.1 h₁.2).2 (mem_cpr.1 h₂.2).2 (mem_cpr.1 h₃.2).2
    have hdg2' : ∑ T ∈ ℬ, (dg G (cpr G C T) v₀ : ℤ) ≤ 6 := by
      rw [hd₀] at hdg2
      exact_mod_cast hdg2
    have hlow' := sum_le_sum hlow
    have hglow : 2 * (#ℬ : ℤ) ≤ ∑ T ∈ ℬ, (gv G T (cpr G C T) - 12) := by
      have hs := sum_le_sum hgnn
      simpa only [sum_const, nsmul_eq_mul, mul_comm] using hs
    rw [hd₀] at hsum
    push_cast at hsum
    linarith
  · have hall' : ∀ v ∈ A,
        ∑ T ∈ ℬ.filter (fun T => v ∈ T), (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) ≤
          3 * (m v : ℤ) - 6 + dg G C v :=
      fun v hv => hvert v hv fun h => hbad ⟨v, hv, h⟩
    have h1 := sum_le_sum hall'
    have h2 := sum_le_sum hlow
    have h3 : ∑ T ∈ ℬ, (3 + (gv G T (cpr G C T) - 12)) =
        3 * #ℬ + ∑ T ∈ ℬ, (gv G T (cpr G C T) - 12) := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      ring
    have h4 : 2 * (#ℬ : ℤ) ≤ ∑ T ∈ ℬ, (gv G T (cpr G C T) - 12) := by
      have hs := sum_le_sum hgnn
      simpa only [sum_const, nsmul_eq_mul, mul_comm] using hs
    have hℬ0 : ℬ = ∅ := by
      apply card_eq_zero.1
      have : (#ℬ : ℤ) ≤ 0 := by linarith
      omega
    have hm1 : ∀ v ∈ A, (1 : ℤ) ≤ m v := fun v hv => by
      have := one_le_m_of_not_big hK hall hv fun T hT hT3 hvT => by
        have : T ∈ ℬ := (memℬ T).2 ⟨hT, hT3⟩
        rw [hℬ0] at this
        simp at this
      exact_mod_cast this
    have h5 : ∑ _v ∈ A, (1 : ℤ) ≤ msum m A := sum_le_sum hm1
    rw [sum_const, nsmul_eq_mul, mul_one, hK.msum_eq] at h5
    have := hK.block.six
    omega


variable {K : Finset V}

def columnLoss (G : SimpleGraph V) [DecidableRel G.Adj] (A J : Finset V) : ℤ :=
  6 * #J - ec G A J

omit [DecidableEq V] in
lemma loss_nonneg (h : ScarBlock G A C) (hJ : J ⊆ C) : 0 ≤ columnLoss G A J := by
  have hb : ec G J A ≤ 6 * #J := by
    calc
      ec G J A ≤ ∑ _c ∈ J, 6 := sum_le_sum fun c hc => (h.scar c (hJ hc)).2
      _ = 6 * #J := by simp [mul_comm]
  rw [ec_comm] at hb
  unfold columnLoss
  omega

lemma loss_le_one (h : ScarBlock G A C) (hJ : J ⊆ C) : columnLoss G A J ≤ 1 := by
  have hn := loss_nonneg h (sdiff_subset (s := C) (t := J))
  have he := ec_sdiff_add_right (G := G) hJ A
  have hc := card_sdiff_add_card_eq_card hJ
  have hfull := h.edges
  unfold columnLoss at *
  omega

lemma theta_boundary (h : ScarBlock G A C) (m : V → ℕ)
    (hT : T ⊆ A) (hJ : J ⊆ C) :
    theta G m T J = msum m T + 4 - 4 * ((#T : ℤ) - #J) -
      columnLoss G A J - ec G J (A \ T) := by
  have he := ec_sdiff_add_right (G := G) hT J
  have ht := ec_comm (G := G) T J
  have ha := ec_comm (G := G) A J
  have hn := loss_nonneg h hJ
  unfold theta columnLoss at *
  omega

def kpC (G : SimpleGraph V) [DecidableRel G.Adj] (C K : Finset V) : Finset V :=
  {c ∈ C | 2 ≤ dg G K c}

omit [DecidableEq V] in
lemma kpC_subset (C K : Finset V) : kpC G C K ⊆ C := filter_subset _ _

omit [DecidableEq V] in
lemma theta_kpC (m : V → ℕ) (C K : Finset V) :
    theta G m K (kpC G C K) = thetaStar G m C K :=
  theta_eq_thetaStar m (kpC_subset C K) (fun c hc h3 => mem_filter.2 ⟨hc, by omega⟩)
    (fun c hc => (mem_filter.1 hc).2)

structure IsHub (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (m : V → ℕ) (K : Finset V) : Prop where
  subset : K ⊆ A
  three_le : 3 ≤ #K
  thetaStar_eq : thetaStar G m C K = 2
  maximal : ∀ K' ⊆ A, K ⊆ K' → 2 ≤ thetaStar G m C K' → K' = K
  msum_ge : 4 ≤ msum m K
  big : ∀ T, IsMaxOver G m A C T → 3 ≤ #T →
    K ⊆ T ∧ thetaStar G m C T = 1 ∧ T ≠ K
  inter : ∀ T T', IsMaxOver G m A C T → 3 ≤ #T → IsMaxOver G m A C T' →
    3 ≤ #T' → T ≠ T' → T ∩ T' = K
  exists_big : ∃ T, IsMaxOver G m A C T ∧ 3 ≤ #T
  exists_pair : ∃ T₁ T₂, IsMaxOver G m A C T₁ ∧ 3 ≤ #T₁ ∧
    IsMaxOver G m A C T₂ ∧ 3 ≤ #T₂ ∧ T₁ ≠ T₂

lemma kplus_facts (hK : FiveData G A C m) (hKA : K ⊆ A) (hK3 : 3 ≤ #K)
    (hKθ : thetaStar G m C K = 2) :
    wsum G m C K + ec G K (C \ kpC G C K) = 2 + 2 * ((#K : ℤ) - #(kpC G C K)) ∧
      (#K : ℤ) - #(kpC G C K) ≤ msum m K - 5 ∧
      (ec G (kpC G C K) (A \ K) : ℤ) + columnLoss G A (kpC G C K) =
        msum m K + 2 - 4 * ((#K : ℤ) - #(kpC G C K)) ∧
      gv G K (kpC G C K) = 2 * msum m K + 4 - 2 * ((#K : ℤ) - #(kpC G C K)) := by
  have hθ : theta G m K (kpC G C K) = 2 := (theta_kpC m C K).trans hKθ
  have h1 := theta_eq_four_add (G := G) m (kpC_subset (G := G) C K) K
  have h2 := theta_le_large hK.block m hKA (kpC_subset (G := G) C K) (by omega)
  have h3 := theta_boundary hK.block m hKA (kpC_subset (G := G) C K)
  have h4 := two_mul_theta (G := G) m K (kpC G C K)
  rw [hθ] at h1 h2 h3 h4
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma hub_meet_one_false (hK : FiveData G A C m) {K T : Finset V} (hKA : K ⊆ A)
    (hK3 : 3 ≤ #K) (hKθ : thetaStar G m C K = 2) (hT : IsMaxOver G m A C T) (hT3 : 3 ≤ #T)
    {a : V} (ha : T ∩ K = {a}) : False := by
  have haT : a ∈ T := (mem_inter.1 (ha ▸ mem_singleton_self a)).1
  have haK : a ∈ K := (mem_inter.1 (ha ▸ mem_singleton_self a)).2
  have haA := hKA haK
  -- `T ∪ K` strictly contains `T`, so it is not overloaded
  have hKT : ¬ K ⊆ T := fun h => by
    rw [inter_eq_right.2 h] at ha
    rw [ha, card_singleton] at hK3
    omega
  have hU : thetaStar G m C (T ∪ K) ≤ 0 := by
    by_contra h
    have := hT.2.2 (T ∪ K) (union_subset hT.1 hKA) subset_union_left (by omega)
    exact hKT (this ▸ subset_union_right)
  -- (2.1) gives `m(a) ≥ 3`, so `m(a) = 3` and `d_a = 3`
  have h21 := thetaStar_add_le (G := G) m C T K
  rw [ha, thetaStar_singleton] at h21
  have hT1 := hT.2.1
  have hma3 := hK.m_le_three haA
  have hma : m a = 3 := by omega
  have hda : dg G C a = 3 := by
    have := hK.le_delta a haA
    have := hK.block.minA a haA
    omega
  -- every neighbor of `a` lies in `K⁺_C`
  obtain ⟨hk1, hk2, -, hk4⟩ := kplus_facts hK hKA hK3 hKθ
  have hwK := hK.wsum_nonneg' hKA
  have hmK := hK.msum_le hKA
  have hdL : dg G (kpC G C K) a = 3 := by
    have hle := dg_mono (G := G) (kpC_subset (G := G) C K) a
    have hsplit := dg_sdiff_add (G := G) (kpC_subset (G := G) C K) a
    have hec : (0 : ℤ) ≤ ec G K (C \ kpC G C K) := Nat.cast_nonneg _
    rcases (by omega : (#K : ℤ) - #(kpC G C K) = -1 ∨ (#K : ℤ) - #(kpC G C K) = 0)
      with hκ | hκ
    · -- case (β): `∂_A(K⁺) = 0`
      have h0 : ec G K (C \ kpC G C K) = 0 := by
        have : (ec G K (C \ kpC G C K) : ℤ) = 0 := by linarith
        exact_mod_cast this
      have hle' : dg G (C \ kpC G C K) a ≤ ec G K (C \ kpC G C K) :=
        single_le_sum (f := fun x => dg G (C \ kpC G C K) x) (fun _ _ => Nat.zero_le _) haK
      omega
    · -- case (δ): `K⁺` is tight and `|K⁺ - a| ≥ 3`
      have hg : gv G K (kpC G C K) = 14 := by
        rw [hk4, hκ]
        have : msum m K = 5 := by linarith
        rw [this]
        norm_num
      have hcard : 3 ≤ #(K.erase a) + #(kpC G C K) := by
        rw [card_erase_of_mem haK]
        omega
      have hsp := hK.block.sparse (K.erase a) ((erase_subset a K).trans hKA) (kpC G C K)
        (kpC_subset C K) hcard
      rw [gv_erase_left haK, hg] at hsp
      omega
  -- Lemma 2.1(c) for `X'(T)` and `K⁺` gives `θ({a} ∪ (C'(T) ∩ K⁺_C)) ≥ 3`, so `C'(T) ∩ K⁺_C = ∅`
  have hun := theta_union_add_theta_inter (G := G) m T K (cpr G C T) (kpC G C K)
  rw [theta_cpr, theta_kpC, ha, hKθ] at hun
  have hle := theta_le_thetaStar (G := G) m
    (union_subset (cpr_subset (G := G) C T) (kpC_subset (G := G) C K)) (T ∪ K)
  have hsing := (theta_singleton (G := G) m a (cpr G C T ∩ kpC G C K)).2
  have hcross : (0 : ℤ) ≤ (ec G (T \ K) (kpC G C K \ cpr G C T) : ℤ) +
      (ec G (K \ T) (cpr G C T \ kpC G C K) : ℤ) := by positivity
  have hJ0 : #(cpr G C T ∩ kpC G C K) = 0 := by
    rw [hma] at hsing
    push_cast at hsing
    have : (#(cpr G C T ∩ kpC G C K) : ℤ) ≤ 0 := by linarith
    omega
  -- so `a` has no neighbor in `C'(T)`
  have hsub : cpr G C T ⊆ C \ kpC G C K := fun c hc => by
    refine mem_sdiff.2 ⟨cpr_subset C T hc, fun hcL => ?_⟩
    have : c ∈ cpr G C T ∩ kpC G C K := mem_inter.2 ⟨hc, hcL⟩
    rw [card_eq_zero.1 hJ0] at this
    simp at this
  have hda0 : dg G (cpr G C T) a = 0 := by
    have h1 := dg_mono (G := G) hsub a
    have h2 := dg_sdiff_add (G := G) (kpC_subset (G := G) C K) a
    omega
  -- `g(X'(T) - a) ≥ 14` gives `g(X'(T)) ≥ 20`, against `g(X'(T)) ≤ 18`
  have hne := cpr_nonempty (hK.msum_le hT.1) hT3 hT.2.1
  have hcard : 3 ≤ #(T.erase a) + #(cpr G C T) := by
    rw [card_erase_of_mem haT]
    have := hne.card_pos
    omega
  have hsp := hK.block.sparse (T.erase a) ((erase_subset a T).trans hT.1) (cpr G C T)
    (cpr_subset C T) hcard
  rw [gv_erase_left haT, hda0] at hsp
  have h2θ := two_mul_theta (G := G) m T (cpr G C T)
  rw [theta_cpr] at h2θ
  have hκT := (big_supply hK hT.1 hT3 hT.2.1).2.1
  have hmT := hK.msum_le hT.1
  push_cast at hsp
  linarith

/-- **PAPER4 Lemma 3.4 (a), (c)**: two distinct maximal overloaded sets sharing at least three
vertices meet in a hub. -/
theorem isHub_of_pair (hK : FiveData G A C m) {T₁ T₂ : Finset V} (h₁ : IsMaxOver G m A C T₁)
    (h₂ : IsMaxOver G m A C T₂) (hne : T₁ ≠ T₂) (h3 : 3 ≤ #(T₁ ∩ T₂)) :
    IsHub G A C m (T₁ ∩ T₂) := by
  have hU := h₁.union_le h₂ hne
  obtain ⟨hKθ, hθ₁, hθ₂⟩ := merge_N3 hK h₁.1 h₁.2.1 h₂.2.1 hU h3
  have hKA : T₁ ∩ T₂ ⊆ A := inter_subset_left.trans h₁.1
  -- (a): no set strictly containing `K` has `θ* ≥ 2`
  have hmax : ∀ K' ⊆ A, T₁ ∩ T₂ ⊆ K' → 2 ≤ thetaStar G m C K' → K' = T₁ ∩ T₂ := by
    intro K' hK'A hsub h2
    have key : ∀ T, IsMaxOver G m A C T → T₁ ∩ T₂ ⊆ T → thetaStar G m C T = 1 → K' ⊆ T := by
      intro T hT hKT hθT
      have hle := thetaStar_add_le (G := G) m C T K'
      have hi3 : 3 ≤ #(T ∩ K') := h3.trans (card_le_card (subset_inter hKT hsub))
      have hi2 := thetaStar_le_two hK
        ((inter_subset_left (s₂ := K')).trans hT.1) hi3
      have hu1 : 1 ≤ thetaStar G m C (T ∪ K') := by linarith
      have := hT.2.2 (T ∪ K') (union_subset hT.1 hK'A) subset_union_left hu1
      rw [← this]
      exact subset_union_right
    exact Subset.antisymm
      (subset_inter (key T₁ h₁ inter_subset_left hθ₁) (key T₂ h₂ inter_subset_right hθ₂)) hsub
  -- (a): `m(K) ≥ 4`
  have hmK : 4 ≤ msum m (T₁ ∩ T₂) := by
    have hθ : theta G m (T₁ ∩ T₂) (cpr G C (T₁ ∩ T₂)) = 2 := (theta_cpr m C _).trans hKθ
    have hk := kappa_bounds hK hKA (cpr_subset (G := G) C (T₁ ∩ T₂))
      (by omega) (by rw [hθ]; norm_num)
    have hsp := theta_le_large hK.block m hKA (cpr_subset (G := G) C (T₁ ∩ T₂))
      (by omega)
    rw [hθ] at hsp
    linarith [hk.1]
  -- (c): every big maximal overloaded set contains `K` and has `θ* = 1`
  have hbig : ∀ T, IsMaxOver G m A C T → 3 ≤ #T →
      T₁ ∩ T₂ ⊆ T ∧ thetaStar G m C T = 1 ∧ T ≠ T₁ ∩ T₂ := by
    intro T hT hT3
    have hsub : T₁ ∩ T₂ ⊆ T := by
      have h2m := (big_supply hK hT.1 hT3 hT.2.1).1
      rcases lt_or_ge #(T ∩ (T₁ ∩ T₂)) 2 with hlt | hge
      · exfalso
        interval_cases hc : #(T ∩ (T₁ ∩ T₂))
        · -- `T` misses `K`: then `m(T) ≤ 5 - m(K) ≤ 1`
          have hdisj : Disjoint T (T₁ ∩ T₂) := disjoint_iff_inter_eq_empty.2 (card_eq_zero.1 hc)
          have e := msum_union_of_disjoint m hdisj
          have := hK.msum_le (union_subset hT.1 hKA)
          omega
        · obtain ⟨a, ha⟩ := card_eq_one.1 hc
          exact hub_meet_one_false hK hKA h3 hKθ hT hT3 ha
      · -- `T` shares at least two vertices with `K`: `T ∪ K` is overloaded
        have hle := thetaStar_add_le (G := G) m C T (T₁ ∩ T₂)
        have hi2 : thetaStar G m C (T ∩ (T₁ ∩ T₂)) ≤ 2 := by
          rcases eq_or_lt_of_le hge with h2 | h3'
          · rw [thetaStar_of_card_eq_two m C h2.symm]
            have := hK.msum_le ((inter_subset_left (s₂ := T₁ ∩ T₂)).trans hT.1)
            linarith
          · exact thetaStar_le_two hK
              ((inter_subset_left (s₂ := T₁ ∩ T₂)).trans hT.1) h3'
        have hu1 : 1 ≤ thetaStar G m C (T ∪ (T₁ ∩ T₂)) := by linarith [hT.2.1]
        have := hT.2.2 _ (union_subset hT.1 hKA) subset_union_left hu1
        rw [← this]
        exact subset_union_right
    refine ⟨hsub, ?_, ?_⟩
    · by_cases hT1 : T = T₁
      · rw [hT1]
        exact hθ₁
      · have hU' := hT.union_le h₁ hT1
        have h3' : 3 ≤ #(T ∩ T₁) := h3.trans (card_le_card (subset_inter hsub inter_subset_left))
        exact (merge_N3 hK hT.1 hT.2.1 h₁.2.1 hU' h3').2.1
    · intro hTK
      have e1 := hT.2.2 T₁ h₁.1 (hTK ▸ inter_subset_left) h₁.2.1
      have e2 := hT.2.2 T₂ h₂.1 (hTK ▸ inter_subset_right) h₂.2.1
      exact hne (e1.trans e2.symm)
  -- (c): two big members meet exactly in `K`
  have hinter : ∀ T T', IsMaxOver G m A C T → 3 ≤ #T → IsMaxOver G m A C T' → 3 ≤ #T' →
      T ≠ T' → T ∩ T' = T₁ ∩ T₂ := by
    intro T T' hT hT3 hT' hT3' hTT'
    obtain ⟨hs, -, -⟩ := hbig T hT hT3
    obtain ⟨hs', -, -⟩ := hbig T' hT' hT3'
    have h3' : 3 ≤ #(T ∩ T') := h3.trans (card_le_card (subset_inter hs hs'))
    have hU' := hT.union_le hT' hTT'
    have hθ := (merge_N3 hK hT.1 hT.2.1 hT'.2.1 hU' h3').1
    exact hmax (T ∩ T') ((inter_subset_left (s₂ := T')).trans hT.1) (subset_inter hs hs')
      hθ.ge
  have hT₁3 : 3 ≤ #T₁ := h3.trans (card_le_card inter_subset_left)
  have hT₂3 : 3 ≤ #T₂ := h3.trans (card_le_card inter_subset_right)
  exact ⟨hKA, h3, hKθ, hmax, hmK, hbig, hinter, ⟨T₁, h₁, hT₁3⟩,
    ⟨T₁, T₂, h₁, hT₁3, h₂, hT₂3, hne⟩⟩

/-! ### The petals (PAPER4 Lemma 3.5) -/

lemma theta_S (hub : IsHub G A C m K) {T : Finset V} (hT : IsMaxOver G m A C T)
    (hT3 : 3 ≤ #T) : theta G m T (cpr G C T ∪ kpC G C K) = 1 := by
  obtain ⟨hKT, hθT, -⟩ := hub.big T hT hT3
  rw [← hθT]
  refine theta_eq_thetaStar m (union_subset (cpr_subset C T) (kpC_subset C K))
    (fun c hc h3 => mem_union_left _ (mem_cpr.2 ⟨hc, h3⟩)) fun c hc => ?_
  rcases mem_union.1 hc with h | h
  · have := (mem_cpr.1 h).2
    omega
  · exact (mem_filter.1 h).2.trans (dg_mono hKT c)

/-- **PAPER4 Lemma 3.5 (a) to (c)** for one big member `T` and its petal
`P_T = (T - K, C'(T) - K⁺_C)`: `θ(P_T) = 3 - E_T` with `E_T = e(K, C'(T) - K⁺_C) + e(T - K, K⁺_C)`,
`w(K) + w(T - K) ≤ 3 + 2κ(S_T)` and `κ(S_T) ≤ m(T) - 4`, where
`κ(S_T) = κ(K⁺) + κ(P_T)`, and `T - K ≠ ∅`. -/
lemma petal_facts (hK : FiveData G A C m) (hub : IsHub G A C m K) {T : Finset V}
    (hT : IsMaxOver G m A C T) (hT3 : 3 ≤ #T) :
    theta G m (T \ K) (cpr G C T \ kpC G C K) =
        3 - ((ec G K (cpr G C T \ kpC G C K) : ℤ) + ec G (T \ K) (kpC G C K)) ∧
      wsum G m C K + wsum G m C (T \ K) ≤
        3 + 2 * (((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K))) ∧
      ((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K)) ≤
        msum m K + msum m (T \ K) - 4 ∧
      1 ≤ #(T \ K) ∧
      -1 ≤ ((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K)) := by
  obtain ⟨hKT, hθT, hTK⟩ := hub.big T hT hT3
  have hS := theta_S hub hT hT3
  have hJ'C : cpr G C T ∪ kpC G C K ⊆ C := union_subset (cpr_subset C T) (kpC_subset C K)
  -- θ(P_T) = 3 - E_T, from Lemma 2.1(c) for the disjoint `K⁺` and `P_T`
  have hun := theta_union_add_theta_inter (G := G) m K (T \ K) (kpC G C K)
    (cpr G C T \ kpC G C K)
  have e1 : K ∪ (T \ K) = T := union_sdiff_of_subset hKT
  have e2 : kpC G C K ∪ (cpr G C T \ kpC G C K) = cpr G C T ∪ kpC G C K := by
    rw [union_sdiff_self_eq_union, union_comm]
  have e3 : K ∩ (T \ K) = ∅ := inter_sdiff_self K T
  have e4 : kpC G C K ∩ (cpr G C T \ kpC G C K) = ∅ := inter_sdiff_self _ _
  have e5 : K \ (T \ K) = K := by
    ext x
    simp only [mem_sdiff]
    tauto
  have e6 : (cpr G C T \ kpC G C K) \ kpC G C K = cpr G C T \ kpC G C K := by
    ext x
    simp only [mem_sdiff]
    tauto
  have e7 : (T \ K) \ K = T \ K := by
    ext x
    simp only [mem_sdiff]
    tauto
  have e8 : kpC G C K \ (cpr G C T \ kpC G C K) = kpC G C K := by
    ext x
    simp only [mem_sdiff]
    tauto
  rw [e1, e2, e3, e4, e5, e6, e7, e8, hS, theta_empty, theta_kpC, hub.thetaStar_eq] at hun
  -- `h(S_T) = 3 + 2κ(S_T) ≥ w(T)` and `κ(S_T) ≤ m(T) - 4`
  have h4 := theta_eq_four_add (G := G) m hJ'C T
  rw [hS] at h4
  have hw := wsum_sdiff_add (G := G) m C hKT
  have hcT := card_sdiff_add_card_eq_card hKT
  have hcJ : #(cpr G C T \ kpC G C K) + #(kpC G C K) = #(cpr G C T ∪ kpC G C K) :=
    card_sdiff_add_card _ _
  have hec : (0 : ℤ) ≤ ec G T (C \ (cpr G C T ∪ kpC G C K)) := Nat.cast_nonneg _
  have hk := kappa_bounds hK hT.1 hJ'C (by omega) (by rw [hS])
  have hmT := msum_sdiff_add m hKT
  have hQ : 1 ≤ #(T \ K) := by
    have : (T \ K).Nonempty := by
      rw [nonempty_iff_ne_empty, Ne, sdiff_eq_empty_iff_subset]
      exact fun h => hTK (Subset.antisymm h hKT)
    exact this.card_pos
  refine ⟨by linarith, ?_, ?_, hQ, ?_⟩
  · have : (#T : ℤ) - #(cpr G C T ∪ kpC G C K) =
        ((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K)) := by
      push_cast [← hcT, ← hcJ]
      ring
    linarith
  · have : (#T : ℤ) - #(cpr G C T ∪ kpC G C K) =
        ((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K)) := by
      push_cast [← hcT, ← hcJ]
      ring
    linarith [hk.2]
  · have : (#T : ℤ) - #(cpr G C T ∪ kpC G C K) =
        ((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K)) := by
      push_cast [← hcT, ← hcJ]
      ring
    linarith [hk.1]

/-- **PAPER4 Lemma 3.5(a)**: the `C`-parts of the petals of two distinct big members are
disjoint, since `θ(S_T ∩ S_T') ≥ 2` and a `C`-vertex outside `K⁺_C` lowers `θ(K⁺)` by at least 1.
-/
lemma petal_J_disjoint (hub : IsHub G A C m K) {T T' : Finset V}
    (hT : IsMaxOver G m A C T) (hT3 : 3 ≤ #T) (hT' : IsMaxOver G m A C T') (hT3' : 3 ≤ #T')
    (hne : T ≠ T') : Disjoint (cpr G C T \ kpC G C K) (cpr G C T' \ kpC G C K) := by
  have hS := theta_S hub hT hT3
  have hS' := theta_S hub hT' hT3'
  have hun := theta_union_add_theta_inter (G := G) m T T' (cpr G C T ∪ kpC G C K)
    (cpr G C T' ∪ kpC G C K)
  have hU := hT.union_le hT' hne
  have hle := theta_le_thetaStar (G := G) m
    (union_subset (union_subset (cpr_subset (G := G) C T) (kpC_subset (G := G) C K))
      (union_subset (cpr_subset (G := G) C T') (kpC_subset (G := G) C K))) (T ∪ T')
  have eZ : (cpr G C T ∪ kpC G C K) ∩ (cpr G C T' ∪ kpC G C K) =
      kpC G C K ∪ ((cpr G C T \ kpC G C K) ∩ (cpr G C T' \ kpC G C K)) := by
    ext x
    simp only [mem_union, mem_inter, mem_sdiff]
    tauto
  have hdisj : Disjoint (kpC G C K) ((cpr G C T \ kpC G C K) ∩ (cpr G C T' \ kpC G C K)) :=
    disjoint_sdiff.mono_right inter_subset_left
  rw [hub.inter T T' hT hT3 hT' hT3' hne, eZ, theta_union_right m K hdisj, theta_kpC,
    hub.thetaStar_eq, hS, hS'] at hun
  -- every `c` in both petals has `e(c, K) ≤ 1`
  have hZ : ∑ c ∈ (cpr G C T \ kpC G C K) ∩ (cpr G C T' \ kpC G C K), ((dg G K c : ℤ) - 2) ≤
      ∑ _c ∈ (cpr G C T \ kpC G C K) ∩ (cpr G C T' \ kpC G C K), (-1 : ℤ) := by
    refine sum_le_sum fun c hc => ?_
    obtain ⟨hcT, hcL⟩ := mem_sdiff.1 (mem_inter.1 hc).1
    have hcC := cpr_subset C T hcT
    have : dg G K c < 2 := by
      by_contra h
      exact hcL (mem_filter.2 ⟨hcC, by omega⟩)
    have : (dg G K c : ℤ) ≤ 1 := by exact_mod_cast (by omega : dg G K c ≤ 1)
    linarith
  rw [sum_const, nsmul_eq_mul, mul_neg_one] at hZ
  have hcross : (0 : ℤ) ≤ (ec G (T \ T') ((cpr G C T' ∪ kpC G C K) \ (cpr G C T ∪ kpC G C K)) :
      ℤ) + (ec G (T' \ T) ((cpr G C T ∪ kpC G C K) \ (cpr G C T' ∪ kpC G C K)) : ℤ) := by
    positivity
  rw [disjoint_iff_inter_eq_empty]
  apply card_eq_zero.1
  have : (#((cpr G C T \ kpC G C K) ∩ (cpr G C T' \ kpC G C K)) : ℤ) ≤ 0 := by linarith
  omega


lemma hub_false (hK : FiveData G A C m) (hcov : ∀ a ∈ A, 4 ≤ dg G C a + m a)
    (hall : CoveredByOverloads G A C m) {K : Finset V}
    (hub : IsHub G A C m K) : False := by
  classical
  -- the identities of `K⁺`
  obtain ⟨hk1, hk2, hk3, -⟩ := kplus_facts hK hub.subset hub.three_le hub.thetaStar_eq
  have hLC : kpC G C K ⊆ C := kpC_subset C K
  set L := kpC G C K with hL
  set ℬ : Finset (Finset V) := A.powerset.filter (fun T => IsMaxOver G m A C T ∧ 3 ≤ #T)
    with hℬ
  have memℬ : ∀ T, T ∈ ℬ ↔ IsMaxOver G m A C T ∧ 3 ≤ #T := fun T => by
    rw [hℬ, mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.1.1, h⟩⟩
  have hwK := hK.wsum_nonneg' hub.subset
  have hmK5 := hK.msum_le hub.subset
  have hmK4 := hub.msum_ge
  have hecK : (0 : ℤ) ≤ ec G K (C \ L) := Nat.cast_nonneg _
  -- the petals are disjoint
  have hdQ : (ℬ : Set (Finset V)).PairwiseDisjoint (fun T => T \ K) := by
    intro T hT T' hT' hne
    obtain ⟨hTm, hT3⟩ := (memℬ T).1 (mem_coe.1 hT)
    obtain ⟨hT'm, hT3'⟩ := (memℬ T').1 (mem_coe.1 hT')
    have hi := hub.inter T T' hTm hT3 hT'm hT3' hne
    show Disjoint (T \ K) (T' \ K)
    rw [disjoint_left]
    intro x hx hx'
    rw [mem_sdiff] at hx hx'
    exact hx.2 (hi ▸ mem_inter.2 ⟨hx.1, hx'.1⟩)
  have hdJ : (ℬ : Set (Finset V)).PairwiseDisjoint (fun T => cpr G C T \ L) := by
    intro T hT T' hT' hne
    obtain ⟨hTm, hT3⟩ := (memℬ T).1 (mem_coe.1 hT)
    obtain ⟨hT'm, hT3'⟩ := (memℬ T').1 (mem_coe.1 hT')
    exact petal_J_disjoint hub hTm hT3 hT'm hT3' hne
  set U := ℬ.biUnion (fun T => T \ K) with hU
  set Jall := ℬ.biUnion (fun T => cpr G C T \ L) with hJall
  have hUA : U ⊆ A \ K := fun x hx => by
    obtain ⟨T, hT, hxT⟩ := mem_biUnion.1 hx
    obtain ⟨hxT, hxK⟩ := mem_sdiff.1 hxT
    exact mem_sdiff.2 ⟨((memℬ T).1 hT).1.1 hxT, hxK⟩
  have hJC : Jall ⊆ C \ L := fun x hx => by
    obtain ⟨T, -, hxT⟩ := mem_biUnion.1 hx
    obtain ⟨hxT, hxL⟩ := mem_sdiff.1 hxT
    exact mem_sdiff.2 ⟨cpr_subset C T hxT, hxL⟩
  -- sums over the petals
  have sW : wsum G m C U = ∑ T ∈ ℬ, wsum G m C (T \ K) := sum_biUnion hdQ
  have sM : msum m U = ∑ T ∈ ℬ, msum m (T \ K) := sum_biUnion hdQ
  have sC : #U = ∑ T ∈ ℬ, #(T \ K) := card_biUnion hdQ
  have sE1 : ∑ T ∈ ℬ, (ec G K (cpr G C T \ L) : ℤ) ≤ ec G K (C \ L) := by
    have h1 : ∑ T ∈ ℬ, ec G K (cpr G C T \ L) = ec G Jall K := by
      rw [show ec G Jall K = ∑ c ∈ Jall, dg G K c from rfl, sum_biUnion hdJ]
      exact sum_congr rfl fun T _ => ec_comm _ _
    have h2 : ec G Jall K ≤ ec G K (C \ L) := by
      rw [ec_comm K]
      exact ec_mono_left hJC K
    exact_mod_cast h1 ▸ h2
  have sE2 : ∑ T ∈ ℬ, (ec G (T \ K) L : ℤ) ≤ ec G L (A \ K) := by
    have h1 : ∑ T ∈ ℬ, ec G (T \ K) L = ec G U L := by
      rw [show ec G U L = ∑ x ∈ U, dg G L x from rfl, sum_biUnion hdQ]
      rfl
    have h2 : ec G U L ≤ ec G L (A \ K) := by
      rw [ec_comm L]
      exact ec_mono_left hUA L
    exact_mod_cast h1 ▸ h2
  -- the partition `A = R ∪ K ∪ U`; every vertex of `R` is a singleton member
  have hKU : Disjoint K U := disjoint_left.2 fun x hxK hxU => (mem_sdiff.1 (hUA hxU)).2 hxK
  have hKUA : K ∪ U ⊆ A := union_subset hub.subset (hUA.trans sdiff_subset)
  have pW := wsum_sdiff_add (G := G) m C hKUA
  rw [wsum_union_of_disjoint m C hKU] at pW
  have pM := msum_sdiff_add m hKUA
  rw [msum_union_of_disjoint m hKU] at pM
  have pC := card_sdiff_add_card_eq_card hKUA
  rw [card_union_of_disjoint hKU] at pC
  set R := A \ (K ∪ U) with hR
  have hRm : (#R : ℤ) ≤ msum m R := by
    have h1 : ∀ v ∈ R, (1 : ℤ) ≤ m v := by
      intro v hv
      obtain ⟨hvA, hvKU⟩ := mem_sdiff.1 hv
      have : 1 ≤ m v := one_le_m_of_not_big hK hall hvA fun T hT hT3 hvT => by
        apply hvKU
        by_cases hvK : v ∈ K
        · exact mem_union_left _ hvK
        · exact mem_union_right _
            (mem_biUnion.2 ⟨T, (memℬ T).2 ⟨hT, hT3⟩, mem_sdiff.2 ⟨hvT, hvK⟩⟩)
      exact_mod_cast this
    have h2 := sum_le_sum h1
    rw [sum_const, nsmul_eq_mul, mul_one] at h2
    exact h2
  have hRw : wsum G m C R ≤ 2 * #R := wsum_le_two_mul hcov sdiff_subset
  have hRw0 : 0 ≤ wsum G m C R := hK.wsum_nonneg' sdiff_subset
  have hRm0 : 0 ≤ msum m R := msum_nonneg m R
  have hUm0 : 0 ≤ msum m U := msum_nonneg m U
  have hW8 := hK.wsum_eq_eight
  have hM5 := hK.msum_eq
  -- the per-petal data, as integers
  have hpet : ∀ T ∈ ℬ,
      msum m (T \ K) + 4 - 4 * (#(T \ K) : ℤ) - 2 * (#(cpr G C T \ L) : ℤ) +
          (ec G (T \ K) (cpr G C T \ L) : ℤ) =
        3 - ((ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L) ∧
      wsum G m C K + wsum G m C (T \ K) ≤
        3 + 2 * (((#K : ℤ) - #L) + ((#(T \ K) : ℤ) - #(cpr G C T \ L))) ∧
      ((#K : ℤ) - #L) + ((#(T \ K) : ℤ) - #(cpr G C T \ L)) ≤
        msum m K + msum m (T \ K) - 4 ∧
      (1 : ℤ) ≤ #(T \ K) ∧ (0 : ℤ) ≤ #(cpr G C T \ L) ∧
      (0 : ℤ) ≤ (ec G (T \ K) (cpr G C T \ L) : ℤ) ∧
      (ec G (T \ K) (cpr G C T \ L) : ℤ) ≤ (#(T \ K) : ℤ) * #(cpr G C T \ L) ∧
      0 ≤ wsum G m C (T \ K) ∧ 0 ≤ msum m (T \ K) ∧
      msum m K + msum m (T \ K) ≤ 5 ∧ wsum G m C (T \ K) ≤ 2 * (#(T \ K) : ℤ) ∧
      (3 ≤ (#(T \ K) : ℤ) + #(cpr G C T \ L) →
        msum m (T \ K) + 4 - 4 * (#(T \ K) : ℤ) - 2 * (#(cpr G C T \ L) : ℤ) +
            (ec G (T \ K) (cpr G C T \ L) : ℤ) ≤
          msum m (T \ K) - 3 - ((#(T \ K) : ℤ) - #(cpr G C T \ L))) ∧
      -1 ≤ ((#K : ℤ) - #L) + ((#(T \ K) : ℤ) - #(cpr G C T \ L)) := by
    intro T hT
    obtain ⟨hTm, hT3⟩ := (memℬ T).1 hT
    obtain ⟨hθQ, hwQ, hkQ, hQ1, hκlower⟩ := petal_facts hK hub hTm hT3
    have hKT := (hub.big T hTm hT3).1
    have hQA : T \ K ⊆ A := sdiff_subset.trans hTm.1
    have hJC' : cpr G C T \ L ⊆ C := sdiff_subset.trans (cpr_subset C T)
    have hmT := hK.msum_le hTm.1
    have hmTs := msum_sdiff_add m hKT
    have he : ec G (T \ K) (cpr G C T \ L) ≤ #(T \ K) * #(cpr G C T \ L) := ec_le_card_mul _ _
    unfold theta at hθQ
    refine ⟨hθQ, hwQ, hkQ, by exact_mod_cast hQ1, by positivity, by positivity,
      by exact_mod_cast he, hK.wsum_nonneg' hQA, msum_nonneg m _, by linarith,
      wsum_le_two_mul hcov hQA, ?_, hκlower⟩
    intro h3
    have h := theta_le_large hK.block m hQA hJC' (by omega)
    unfold theta at h
    exact h
  have sEsplit : ∑ T ∈ ℬ, ((ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L) =
      ∑ T ∈ ℬ, (ec G K (cpr G C T \ L) : ℤ) + ∑ T ∈ ℬ, (ec G (T \ K) L : ℤ) := sum_add_distrib
  have hLoss0 : 0 ≤ columnLoss G A L := loss_nonneg hK.block hLC
  rcases (by omega : (#K : ℤ) - #L = -1 ∨ (#K : ℤ) - #L = 0) with hβ | hδ
  · have hwK0 : wsum G m C K = 0 := by linarith
    have hecK0 : (ec G K (C \ L) : ℤ) = 0 := by linarith
    have hbd : (ec G L (A \ K) : ℤ) ≤ msum m K + 6 := by linarith
    have hβT : ∀ T ∈ ℬ, 3 * wsum G m C (T \ K) ≤
        2 * (((ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L) + msum m (T \ K)) := by
      intro T hT
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _, h10, h11, h12, h13⟩ := hpet T hT
      refine beta_petal_cost h4 h5 h6 h7 h8 h11 ?_ ?_ ?_ h1 ?_
      · linarith
      · linarith
      · linarith
      · intro hlarge
        have hb := h12 hlarge
        linarith
    have s1 := sum_le_sum hβT
    rw [← mul_sum, ← mul_sum, sum_add_distrib, sEsplit] at s1
    have hmR1 : 1 ≤ msum m R := by
      have : 2 + 2 * msum m R ≤ 3 * wsum G m C R := by linarith
      linarith
    have hmK4' : msum m K = 4 := by linarith
    have hmU0 : msum m U = 0 := by linarith
    have hmR : msum m R = 1 := by linarith
    have hcR : #R = 1 := by
      have h1 : (#R : ℤ) ≤ 1 := by linarith
      have h2 : R.Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro he
        rw [he, msum_empty] at hmR
        omega
      have := h2.card_pos
      omega
    have hwR : wsum G m C R ≤ 2 := by
      rw [hcR] at hRw
      simpa using hRw
    have hmQ0 : ∀ T ∈ ℬ, msum m (T \ K) = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun T _ => msum_nonneg m (T \ K))).1 (sM ▸ hmU0)
    have hsT : ∀ T ∈ ℬ,
        0 ≤ 2 * ((ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L) -
          3 * wsum G m C (T \ K) ∧
        (2 ≤ (#(T \ K) : ℤ) + #(cpr G C T \ L) →
          5 ≤ 2 * ((ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L) -
            3 * wsum G m C (T \ K)) := by
      intro T hT
      have hb := hβT T hT
      rw [hmQ0 T hT] at hb
      refine ⟨by linarith, fun htwo => ?_⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _, _, h11, h12, h13⟩ := hpet T hT
      rw [hmQ0 T hT] at h1 h3 h12
      have hs : 3 * wsum G m C (T \ K) + 5 ≤
          2 * ((ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L) := by
        refine beta_zero_nonsingle_slack h4 h5 htwo h6 h7 h8 h11 ?_ ?_ ?_ ?_ ?_
        · linarith
        · linarith
        · linarith
        · simpa using h1
        · intro hlarge
          have hb := h12 hlarge
          linarith
      linarith
    have s2 : ∑ T ∈ ℬ,
        (2 * ((ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L) -
          3 * wsum G m C (T \ K)) ≤ 2 := by
      rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sEsplit]
      linarith
    have hone : ∀ T ∈ ℬ, #(T \ K) = 1 ∧ #(cpr G C T \ L) = 0 := by
      intro T hT
      have hl := single_le_sum (fun T hT => (hsT T hT).1) hT
      have hu := hl.trans s2
      have hcard := (hpet T hT).2.2.2.1
      have hj : (0 : ℤ) ≤ #(cpr G C T \ L) := Nat.cast_nonneg _
      have hlt : (#(T \ K) : ℤ) + #(cpr G C T \ L) < 2 := by
        by_contra hn
        have hb := (hsT T hT).2 (by omega)
        omega
      constructor <;> omega
    have hE3 : ∀ T ∈ ℬ, (ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L = 3 := by
      intro T hT
      obtain ⟨h1, _, _, _, _, h6, h7, _⟩ := hpet T hT
      obtain ⟨hq, hj⟩ := hone T hT
      rw [hq, hj, hmQ0 T hT] at h1
      rw [hq, hj] at h7
      push_cast at h1 h7
      linarith
    have hsumE : ∑ T ∈ ℬ, ((ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L) = 3 * #ℬ := by
      rw [sum_congr rfl hE3, sum_const, nsmul_eq_mul]
      ring
    have hsumC : #U = #ℬ := by
      rw [sC, sum_congr rfl fun T hT => (hone T hT).1, sum_const, smul_eq_mul, mul_one]
    have hwU : wsum G m C U ≤ 2 * #U := wsum_le_two_mul hcov (hUA.trans sdiff_subset)
    have hB3 : #ℬ = 3 := by
      have h1 : (#ℬ : ℤ) ≤ 3 := by linarith
      have h2 : (3 : ℤ) ≤ #ℬ := by linarith
      omega
    have hcA : #A = #K + 4 := by omega
    have hcC := hK.block.card
    have hcL : #L = #K + 1 := by omega
    have hcCL : #(C \ L) = 1 := by
      have := card_sdiff_add_card_eq_card hLC
      omega
    obtain ⟨c₀, hc₀⟩ := card_pos.1 (by omega : 0 < #(C \ L))
    have hc₀C := (mem_sdiff.1 hc₀).1
    have hdK : dg G K c₀ = 0 := by
      have h0 : ec G (C \ L) K = 0 := by
        rw [ec_comm]
        exact_mod_cast hecK0
      have hb := single_le_sum (f := fun x => dg G K x) (fun _ _ => Nat.zero_le _) hc₀
      change dg G K c₀ ≤ ec G (C \ L) K at hb
      omega
    have h5 := (hK.block.scar c₀ hc₀C).1
    have hsplit := dg_sdiff_add (G := G) hub.subset c₀
    have hle := dg_le_card (G := G) (A \ K) c₀
    have hcAK := card_sdiff_add_card_eq_card hub.subset
    omega
  · have hmK5' : msum m K = 5 := by linarith
    have hmR0 : msum m R = 0 := by linarith
    have hcR0 : (#R : ℤ) = 0 := by linarith [(Nat.cast_nonneg #R : (0 : ℤ) ≤ #R)]
    have hwR0 : wsum G m C R = 0 := by linarith
    have hδT : ∀ T ∈ ℬ, wsum G m C (T \ K) + 1 ≤
        (ec G K (cpr G C T \ L) : ℤ) + ec G (T \ K) L := by
      intro T hT
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hpet T hT
      have hmQ0 : msum m (T \ K) = 0 := by linarith
      rw [hmQ0] at h1 h12
      refine delta_petal_cost h4 h5 h6 h7 h8 hwK h11 ?_ ?_ ?_ ?_ ?_
      · linarith
      · linarith
      · linarith
      · simpa using h1
      · intro hlarge
        have hb := h12 hlarge
        linarith
    have s1 := sum_le_sum hδT
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, sEsplit] at s1
    obtain ⟨T₁, T₂, hT₁, hT₁3, hT₂, hT₂3, hne⟩ := hub.exists_pair
    have hB : (2 : ℤ) ≤ #ℬ := by
      exact_mod_cast (one_lt_card.2
        ⟨T₁, (memℬ T₁).2 ⟨hT₁, hT₁3⟩, T₂, (memℬ T₂).2 ⟨hT₂, hT₂3⟩, hne⟩)
    linarith

lemma good_theta (h : FiveData G A C m) (hcov : ∀ a ∈ A, 4 ≤ dg G C a + m a) :
    ∃ p ∈ A, ∀ T ⊆ A, p ∈ T → thetaStar G m C T ≤ 0 := by
  by_contra! hall
  have hall' : CoveredByOverloads G A C m := fun p hp => by
    obtain ⟨T, hT, hpT, hpos⟩ := hall p hp
    exact ⟨T, hT, hpT, by omega⟩
  obtain ⟨T₁, T₂, h₁, h₂, hne, h3⟩ := exists_hub_pair h hall'
  exact hub_false h hcov hall' (isHub_of_pair h h₁ h₂ hne h3)

theorem covered_five_supply : CoveredFiveSupply.{u} := by
  intro V _ G _ A C h m hm hcap hcov
  have hd : FiveData G A C m := ⟨h, hm, hcap⟩
  obtain ⟨p, hp, hgood⟩ := good_theta hd hcov
  refine ⟨p, hp, ?_, ?_⟩
  · have ht := hgood {p} (singleton_subset_iff.2 hp) (mem_singleton_self p)
    rw [thetaStar_singleton] at ht
    omega
  · intro T hT
    have hTA : T ⊆ A := hT.trans (erase_subset p A)
    have hpnot : p ∉ T := fun hpT => (mem_erase.1 (hT hpT)).1 rfl
    have hpc : p ∈ A \ T := mem_sdiff.2 ⟨hp, hpnot⟩
    have ht := hgood (A \ T) sdiff_subset hpc
    have hi := complement_scar_demand (G := G) (sdiff_subset (s := A) (t := T))
      h.card h.edges hm
    rw [sdiff_sdiff_right_self, inf_eq_right.mpr hTA] at hi
    linarith

end Erdos585.QB6CoveredFive
