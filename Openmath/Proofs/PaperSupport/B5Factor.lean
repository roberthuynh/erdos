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
import Openmath.Proofs.PaperSupport.B5Defs

/- 

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset Sum
namespace Erdos585.B5Factor
open QB4 B5
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {k : ℕ}
omit [DecidableEq V] in
/-- Truncated subtraction of the target, summed over vertices above that target. -/
lemma sum_sub_target_add {S : Finset V} {d : V → ℕ} (h : ∀ v ∈ S, k ≤ d v) :
    ∑ v ∈ S, (d v - k) + k * #S = ∑ v ∈ S, d v := by
  rw [mul_comm, ← smul_eq_mul, ← sum_const, ← sum_add_distrib]
  exact sum_congr rfl fun v hv => Nat.sub_add_cancel (h v hv)

/-! ### Degrees from the cut condition -/

/-- The cut condition at `({p}, ∅)` gives `deg_Q p ≥ k`. -/
lemma target_le_dg_left {P Q : Finset V}
    (hcut : ∀ A ⊆ P, ∀ C ⊆ Q, k * #A ≤ ec G A (Q \ C) + k * #C) {p : V} (hp : p ∈ P) :
    k ≤ dg G Q p := by
  have h := hcut {p} (singleton_subset_iff.2 hp) ∅ (empty_subset _)
  rw [sdiff_empty, card_singleton, card_empty, ec, sum_singleton] at h
  omega

/-- The cut condition at `(P, Q - q)` gives `deg_P q ≥ k` when `|P| = |Q|`. -/
lemma target_le_dg_right {P Q : Finset V} (hcard : #P = #Q)
    (hcut : ∀ A ⊆ P, ∀ C ⊆ Q, k * #A ≤ ec G A (Q \ C) + k * #C) {q : V} (hq : q ∈ Q) :
    k ≤ dg G P q := by
  have h := hcut P Subset.rfl (Q.erase q) (erase_subset q Q)
  rw [sdiff_erase_self hq, card_erase_of_mem hq, ec_comm, ec, sum_singleton] at h
  have hQ := card_pos.2 ⟨q, hq⟩
  have hprod : k * (#Q - 1) + k = k * #Q := by
    calc k * (#Q - 1) + k = k * ((#Q - 1) + 1) := by rw [Nat.mul_add]; simp
      _ = k * #Q := by congr 1; omega
  rw [hcard] at h
  omega

/-! ### Tutte's gadget -/

variable (G) in
/-- The index set of the gadget for the pair `(P, Q)`: the adjacent pairs of `P × Q`, and
`deg_P q - k` slots for each `q ∈ Q`. -/
def gadgetIndex (P Q : Finset V) : Finset ((V × V) ⊕ (V × ℕ)) :=
  (adjPairs G P Q).disjSum (slots Q fun q => dg G P q - k)

variable (G) in
/-- Tutte's gadget for the pair `(P, Q)`. An adjacent pair `e` may be matched to itself or to a
slot of its first vertex `p`, of which there are `deg_Q p - k`. A slot of `q` may be matched to an
adjacent pair whose second vertex is `q`. -/
def gadget (P Q : Finset V) : (V × V) ⊕ (V × ℕ) → Finset ((V × V) ⊕ (V × ℕ)) :=
  Sum.elim (fun e => ({e} : Finset (V × V)).disjSum (slots {e.1} fun p => dg G Q p - k))
    (fun c => ((adjPairs G P Q).filter fun e => e.2 = c.1).disjSum ∅)

lemma inl_mem_gadgetIndex {P Q : Finset V} {e : V × V} :
    inl e ∈ gadgetIndex (k := k) G P Q ↔ e ∈ adjPairs G P Q :=
  inl_mem_disjSum

lemma inr_mem_gadgetIndex {P Q : Finset V} {c : V × ℕ} :
    inr c ∈ gadgetIndex (k := k) G P Q ↔ c.1 ∈ Q ∧ c.2 < dg G P c.1 - k := by
  rw [gadgetIndex, inr_mem_disjSum, mem_slots]

lemma inl_mem_gadget_inl {P Q : Finset V} {a e : V × V} :
    inl a ∈ gadget (k := k) G P Q (inl e) ↔ a = e := by
  simp [gadget]

lemma inr_mem_gadget_inl {P Q : Finset V} {e : V × V} {s : V × ℕ} :
    inr s ∈ gadget (k := k) G P Q (inl e) ↔ s.1 = e.1 ∧ s.2 < dg G Q s.1 - k := by
  rw [gadget, Sum.elim_inl, inr_mem_disjSum, mem_slots, mem_singleton]

lemma inl_mem_gadget_inr {P Q : Finset V} {a : V × V} {c : V × ℕ} :
    inl a ∈ gadget (k := k) G P Q (inr c) ↔ a ∈ adjPairs G P Q ∧ a.2 = c.1 := by
  rw [gadget, Sum.elim_inr, inl_mem_disjSum, mem_filter]

lemma inr_notMem_gadget_inr {P Q : Finset V} {s c : V × ℕ} : inr s ∉ gadget (k := k) G P Q (inr c) := by
  rw [gadget, Sum.elim_inr, inr_mem_disjSum]
  exact notMem_empty s

/-- **Hall's condition for the gadget** follows from the cut condition. For a set `S` of indices
with adjacent pairs `S_E` and slots `S_C`, put `A = fst S_E` and `C = fst S_C`. Then
`|S| ≤ |S_E| + Σ_{q ∈ C} (deg_P q - k)`, while the neighborhood of `S` contains `S_E`, every
adjacent pair at `C`, and every slot of `A`. The overlap of `S_E` with the pairs at `C` is at most
`e(A, C)`, and the remaining inequality is the cut condition at `(A, C)`. -/
lemma gadget_hall {P Q : Finset V}
    (hcut : ∀ A ⊆ P, ∀ C ⊆ Q, k * #A ≤ ec G A (Q \ C) + k * #C)
    (hP4 : ∀ p ∈ P, k ≤ dg G Q p) (hQ4 : ∀ q ∈ Q, k ≤ dg G P q)
    (S : Finset ((V × V) ⊕ (V × ℕ))) (hS : S ⊆ gadgetIndex (k := k) G P Q) :
    #S ≤ #(S.biUnion (gadget (k := k) G P Q)) := by
  have hSE : S.toLeft ⊆ adjPairs G P Q := fun e he =>
    inl_mem_gadgetIndex (k := k).1 (hS (mem_toLeft.1 he))
  have hSC : ∀ c ∈ S.toRight, c.1 ∈ Q ∧ c.2 < dg G P c.1 - k := fun c hc =>
    inr_mem_gadgetIndex (k := k).1 (hS (mem_toRight.1 hc))
  have hAP : S.toLeft.image Prod.fst ⊆ P := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := mem_image.1 hp
    exact (mem_product.1 (mem_filter.1 (hSE he)).1).1
  have hCQ : S.toRight.image Prod.fst ⊆ Q := by
    intro q hq
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hq
    exact (hSC c hc).1
  set A := S.toLeft.image Prod.fst with hA
  set C := S.toRight.image Prod.fst with hC
  set EC := (adjPairs G P Q).filter fun e => e.2 ∈ C with hEC
  -- the slots in `S` lie over `C`
  have h2 : #S.toRight ≤ ∑ q ∈ C, (dg G P q - k) := by
    rw [← card_slots]
    exact card_le_card fun c hc => mem_slots.2 ⟨mem_image_of_mem _ hc, (hSC c hc).2⟩
  -- the neighborhood of `S` in the gadget
  have h3 : #((S.toLeft ∪ EC).disjSum (slots A fun p => dg G Q p - k)) ≤
      #(S.biUnion (gadget (k := k) G P Q)) := by
    refine card_le_card fun x hx => mem_biUnion.2 ?_
    rcases x with e | s
    · rcases mem_union.1 (inl_mem_disjSum.1 hx) with he | he
      · exact ⟨inl e, mem_toLeft.1 he, inl_mem_gadget_inl (k := k).2 rfl⟩
      · obtain ⟨heE, heC⟩ := mem_filter.1 he
        obtain ⟨c, hc, hce⟩ := mem_image.1 heC
        exact ⟨inr c, mem_toRight.1 hc, inl_mem_gadget_inr (k := k).2 ⟨heE, hce.symm⟩⟩
    · obtain ⟨hsA, hs⟩ := mem_slots.1 (inr_mem_disjSum.1 hx)
      obtain ⟨e, he, hes⟩ := mem_image.1 hsA
      exact ⟨inl e, mem_toLeft.1 he, inr_mem_gadget_inl (k := k).2 ⟨hes.symm, hs⟩⟩
  rw [card_disjSum, card_slots] at h3
  have h1 := card_toLeft_add_card_toRight (u := S)
  have h4 := card_union_add_card_inter S.toLeft EC
  have h5 : #EC = ec G C P := by
    rw [hEC, adjPairs_filter_snd_mem hCQ, card_adjPairs, ec_comm]
  have h6 : #(S.toLeft ∩ EC) ≤ ec G A C := by
    rw [← card_adjPairs]
    refine card_le_card fun e he => ?_
    obtain ⟨heS, heC⟩ := mem_inter.1 he
    exact mem_filter.2 ⟨mem_product.2 ⟨mem_image_of_mem _ heS, (mem_filter.1 heC).2⟩,
      (mem_filter.1 (hSE heS)).2⟩
  have h7 : ∑ p ∈ A, (dg G Q p - k) + k * #A = ec G A Q :=
    sum_sub_target_add (k := k) fun p hp => hP4 p (hAP hp)
  have h8 : ∑ q ∈ C, (dg G P q - k) + k * #C = ec G C P :=
    sum_sub_target_add (k := k) fun q hq => hQ4 q (hCQ hq)
  have h9 := ec_sdiff_add_right (G := G) hCQ A
  have h10 := hcut A hAP C hCQ
  omega

/-! ### From a matching of the gadget to a k-factor -/

/-- The kept pairs at `p ∈ P`. The deleted pairs at `p` are matched to distinct slots of `p`, so at
most `deg_Q p - k` pairs at `p` are deleted and at least k are kept. -/
lemma target_le_card_kept {P Q : Finset V} (hP4 : ∀ p ∈ P, k ≤ dg G Q p)
    {g : (V × V) ⊕ (V × ℕ) → (V × V) ⊕ (V × ℕ)}
    (hginj : ∀ i ∈ gadgetIndex (k := k) G P Q, ∀ j ∈ gadgetIndex (k := k) G P Q, g i = g j → i = j)
    (hgt : ∀ i ∈ gadgetIndex (k := k) G P Q, g i ∈ gadget (k := k) G P Q i) {p : V} (hp : p ∈ P) :
    k ≤ #{x ∈ (adjPairs G P Q).filter (fun e => g (inl e) = inl e) | x.1 = p} := by
  have hEp := card_adjPairs_filter_fst (G := G) (Q := Q) hp
  have hsplit := card_filter_add_card_filter_not (s := (adjPairs G P Q).filter fun e => e.1 = p)
    (fun e => g (inl e) = inl e)
  have hout : #(((adjPairs G P Q).filter fun e => e.1 = p).filter
      fun e => ¬ g (inl e) = inl e) ≤ dg G Q p - k := by
    have h := card_le_card_of_injOn
      (s := ((adjPairs G P Q).filter fun e => e.1 = p).filter fun e => ¬ g (inl e) = inl e)
      (t := (∅ : Finset (V × V)).disjSum (slots {p} fun p => dg G Q p - k))
      (fun e => g (inl e)) ?_ ?_
    · rwa [card_disjSum, card_empty, zero_add, card_slots, sum_singleton] at h
    · intro e he
      rw [mem_coe, mem_filter, mem_filter] at he
      obtain ⟨⟨heE, rfl⟩, hne⟩ := he
      have hmem := hgt (inl e) (inl_mem_gadgetIndex (k := k).2 heE)
      simp only [mem_coe]
      generalize hx : g (inl e) = x at hmem hne ⊢
      rcases x with a | s
      · exact absurd (congrArg inl (inl_mem_gadget_inl (k := k).1 hmem)) hne
      · obtain ⟨hs1, hs2⟩ := inr_mem_gadget_inl (k := k).1 hmem
        exact inr_mem_disjSum.2 (mem_slots.2 ⟨mem_singleton.2 hs1, hs2⟩)
    · intro e he e' he' hee
      rw [mem_coe, mem_filter, mem_filter] at he he'
      exact inl_injective (hginj _ (inl_mem_gadgetIndex (k := k).2 he.1.1) _
        (inl_mem_gadgetIndex (k := k).2 he'.1.1) hee)
  rw [filter_comm]
  have := hP4 p hp
  omega

/-- The kept pairs at `q ∈ Q`. The slots of `q` are matched to distinct pairs at `q`, all deleted
by injectivity, so at least `deg_P q - k` pairs at `q` are deleted and at most k are kept. -/
lemma card_kept_le_target {P Q : Finset V}
    {g : (V × V) ⊕ (V × ℕ) → (V × V) ⊕ (V × ℕ)}
    (hginj : ∀ i ∈ gadgetIndex (k := k) G P Q, ∀ j ∈ gadgetIndex (k := k) G P Q, g i = g j → i = j)
    (hgt : ∀ i ∈ gadgetIndex (k := k) G P Q, g i ∈ gadget (k := k) G P Q i) {q : V} (hq : q ∈ Q) :
    #{x ∈ (adjPairs G P Q).filter (fun e => g (inl e) = inl e) | x.2 = q} ≤ k := by
  have hEq := card_adjPairs_filter_snd (G := G) (P := P) hq
  have hsplit := card_filter_add_card_filter_not (s := (adjPairs G P Q).filter fun e => e.2 = q)
    (fun e => g (inl e) = inl e)
  have hslot : ∀ j < dg G P q - k, inr (q, j) ∈ gadgetIndex (k := k) G P Q := fun j hj =>
    inr_mem_gadgetIndex (k := k).2 ⟨hq, hj⟩
  have hin : dg G P q - k ≤ #(((adjPairs G P Q).filter fun e => e.2 = q).filter
      fun e => ¬ g (inl e) = inl e) := by
    have h := card_le_card_of_injOn (s := range (dg G P q - k))
      (t := (((adjPairs G P Q).filter fun e => e.2 = q).filter
        fun e => ¬ g (inl e) = inl e).disjSum (∅ : Finset (V × ℕ)))
      (fun j => g (inr (q, j))) ?_ ?_
    · rwa [card_range, card_disjSum, card_empty, add_zero] at h
    · intro j hj
      simp only [coe_range, Set.mem_Iio] at hj
      have hmem := hgt _ (hslot j hj)
      simp only [mem_coe]
      generalize hx : g (inr (q, j)) = x at hmem ⊢
      rcases x with e | s
      · obtain ⟨heE, heq⟩ := inl_mem_gadget_inr (k := k).1 hmem
        refine inl_mem_disjSum.2 (mem_filter.2 ⟨mem_filter.2 ⟨heE, heq⟩, fun hgood => ?_⟩)
        exact inl_ne_inr (hginj _ (inl_mem_gadgetIndex (k := k).2 heE) _ (hslot j hj) (hgood.trans hx.symm))
      · exact absurd hmem (inr_notMem_gadget_inr (k := k))
    · intro j hj j' hj' hjj
      simp only [coe_range, Set.mem_Iio] at hj hj'
      have := hginj _ (hslot j hj) _ (hslot j' hj') hjj
      simpa using this
  rw [filter_comm]
  omega

/-- **The bipartite k-factor criterion** (C1-PAPER Lemma 1.k, the direction used). If
`|P| = |Q|` and `k |A| ≤ e(A, Q - C) + k |C|` for all `A ⊆ P` and `C ⊆ Q`, then the bipartite
graph `G[P, Q]` has a k-factor: a set `F` of adjacent pairs of `P × Q` with every `p ∈ P` the
first entry of exactly k pairs and every `q ∈ Q` the second entry of exactly k pairs. -/
theorem exists_target_factor (P Q : Finset V) (hcard : #P = #Q)
    (hcut : ∀ A ⊆ P, ∀ C ⊆ Q, k * #A ≤ ec G A (Q \ C) + k * #C) :
    ∃ F ⊆ P ×ˢ Q, (∀ x ∈ F, G.Adj x.1 x.2) ∧
      (∀ p ∈ P, #{x ∈ F | x.1 = p} = k) ∧ (∀ q ∈ Q, #{x ∈ F | x.2 = q} = k) := by
  have hP4 : ∀ p ∈ P, k ≤ dg G Q p := fun p hp => target_le_dg_left (k := k) hcut hp
  have hQ4 : ∀ q ∈ Q, k ≤ dg G P q := fun q hq => target_le_dg_right (k := k) hcard hcut hq
  rcases P.eq_empty_or_nonempty with hPe | ⟨p0, -⟩
  · have hQe : Q = ∅ := card_eq_zero.1 (by rw [← hcard, hPe, card_empty])
    exact ⟨∅, empty_subset _, by simp, by simp [hPe], by simp [hQe]⟩
  have : Nonempty ((V × V) ⊕ (V × ℕ)) := ⟨inr (p0, 0)⟩
  obtain ⟨g, hginj, hgt⟩ := exists_injOn_of_hall (gadgetIndex (k := k) G P Q) (gadget (k := k) G P Q)
    fun S hS => gadget_hall (k := k) hcut hP4 hQ4 S hS
  set F := (adjPairs G P Q).filter fun e => g (inl e) = inl e with hF
  have hFPQ : F ⊆ P ×ˢ Q := (filter_subset _ _).trans (filter_subset _ _)
  have hFP : ∀ p ∈ P, k ≤ #{x ∈ F | x.1 = p} := fun p hp => target_le_card_kept (k := k) hP4 hginj hgt hp
  have hFQ : ∀ q ∈ Q, #{x ∈ F | x.2 = q} ≤ k := fun q hq => card_kept_le_target (k := k) hginj hgt hq
  -- double counting the kept pairs
  have hsumP : #F = ∑ p ∈ P, #{x ∈ F | x.1 = p} :=
    card_eq_sum_card_fiberwise fun x hx => (mem_product.1 (hFPQ hx)).1
  have hsumQ : #F = ∑ q ∈ Q, #{x ∈ F | x.2 = q} :=
    card_eq_sum_card_fiberwise fun x hx => (mem_product.1 (hFPQ hx)).2
  have hlo : ∑ _p ∈ P, k ≤ ∑ p ∈ P, #{x ∈ F | x.1 = p} := sum_le_sum hFP
  have hhi : ∑ q ∈ Q, #{x ∈ F | x.2 = q} ≤ ∑ _q ∈ Q, k := sum_le_sum hFQ
  have hcP : ∑ _p ∈ P, (k : ℕ) = k * #P := by rw [sum_const, smul_eq_mul, mul_comm]
  have hcQ : ∑ _q ∈ Q, (k : ℕ) = k * #Q := by rw [sum_const, smul_eq_mul, mul_comm]
  have hcPQ : k * #P = k * #Q := congrArg (fun n => k * n) hcard
  have heqP : ∑ _p ∈ P, k = ∑ p ∈ P, #{x ∈ F | x.1 = p} := by omega
  have heqQ : ∑ q ∈ Q, #{x ∈ F | x.2 = q} = ∑ _q ∈ Q, k := by omega
  refine ⟨F, hFPQ, fun x hx => (mem_filter.1 (filter_subset _ _ hx)).2, fun p hp => ?_,
    fun q hq => ?_⟩
  · exact ((sum_eq_sum_iff_of_le hFP).1 heqP p hp).symm
  · exact (sum_eq_sum_iff_of_le hFQ).1 heqQ q hq


#print axioms exists_target_factor
end Erdos585.B5Factor
