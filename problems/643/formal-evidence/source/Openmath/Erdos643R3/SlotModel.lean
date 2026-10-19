import Mathlib
import Openmath.Erdos643R3.WeightingBound



set_option autoImplicit false

namespace Erdos643R3
namespace SlotModel

open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.WeightingBound

variable {V : Type*} [Fintype V] [DecidableEq V]

section Defs

variable (H : Finset (Finset V))

/-- The group of the apex `a` in the view `(a,b,c)`: `L(bc) \ {a}`. -/
def grp (a b c : V) : Finset V := (link H {b, c}).erase a

/-- Adjacency in the relation with apex `w`: `x ≠ y` and `{w,x,y} ∈ H`. -/
def rel (w x y : V) : Prop := x ≠ y ∧ ({w, x, y} : Finset V) ∈ H

instance decRel (w x y : V) : Decidable (rel H w x y) := instDecidableAnd

/-- `R_c`-neighbours (slots of `B = grp b c a`) of a slot `z` of `A = grp a b c`. -/
def nc (a b c z : V) : Finset V := (grp H b c a).filter (fun y => rel H c z y)

/-- `R_b`-neighbours (slots of `C = grp c a b`) of a slot `z` of `A = grp a b c`. -/
def nb (a b c z : V) : Finset V := (grp H c a b).filter (fun x => rel H b x z)

end Defs

variable {H : Finset (Finset V)}

/-! ## Membership -/

theorem mem_grp {a b c z : V} :
    z ∈ grp H a b c ↔ z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ ({z, b, c} : Finset V) ∈ H := by
  simp only [grp, mem_erase, mem_link, mem_insert, mem_singleton, not_or]
  tauto

theorem mem_nc {a b c z y : V} :
    y ∈ nc H a b c z ↔ y ∈ grp H b c a ∧ z ≠ y ∧ ({c, z, y} : Finset V) ∈ H := by
  unfold nc; rw [mem_filter]; rfl

theorem mem_nb {a b c z x : V} :
    x ∈ nb H a b c z ↔ x ∈ grp H c a b ∧ x ≠ z ∧ ({b, x, z} : Finset V) ∈ H := by
  unfold nb; rw [mem_filter]; rfl

omit [Fintype V] in
/-- Reordering the three vertices of a triple. -/
lemma triple_perm {x y z x' y' z' : V}
    (h : ∀ t : V, (t = x ∨ t = y ∨ t = z) ↔ (t = x' ∨ t = y' ∨ t = z')) :
    ({x, y, z} : Finset V) = {x', y', z'} := by
  ext t; simp only [mem_insert, mem_singleton]; exact h t

omit [Fintype V] in
lemma not_mem_of_inter_empty {P q : Finset V} (h : P ∩ q = ∅) {t : V} (hP : t ∈ P) (hq : t ∈ q) :
    False := by
  have : t ∈ P ∩ q := mem_inter.mpr ⟨hP, hq⟩
  rw [h] at this
  exact notMem_empty t this

/-! ## Lemma 1: `s_{q_v} = 1 + d(v)` -/

/-- An `R_b`-neighbour `x` of the slot `z` of `A` gives the member `{b,x}` of `CN(a,z)`. -/
theorem pair_b_mem_CN {a b c z x : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hz : z ∈ grp H a b c) (hx : x ∈ nb H a b c z) : ({b, x} : Finset V) ∈ CN H {a, z} := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  obtain ⟨hza, hzb, hzc, -⟩ := mem_grp.mp hz
  obtain ⟨hxC, hxz, hbxz⟩ := mem_nb.mp hx
  obtain ⟨hxc, hxa, hxb, hxab⟩ := mem_grp.mp hxC
  refine pair_mem_CN (Ne.symm hxb) (Ne.symm hab) (Ne.symm hzb) hxa hxz ?_ ?_
  · rw [show (insert a ({b, x} : Finset V)) = {x, a, b} from triple_perm (fun t => by tauto)]
    exact hxab
  · rw [show (insert z ({b, x} : Finset V)) = {b, x, z} from triple_perm (fun t => by tauto)]
    exact hbxz

/-- An `R_c`-neighbour `y` of the slot `z` of `A` gives the member `{c,y}` of `CN(a,z)`. -/
theorem pair_c_mem_CN {a b c z y : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hz : z ∈ grp H a b c) (hy : y ∈ nc H a b c z) : ({c, y} : Finset V) ∈ CN H {a, z} := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  obtain ⟨hza, hzb, hzc, -⟩ := mem_grp.mp hz
  obtain ⟨hyB, hzy, hczy⟩ := mem_nc.mp hy
  obtain ⟨hyb, hyc, hya, hyca⟩ := mem_grp.mp hyB
  refine pair_mem_CN (Ne.symm hyc) (Ne.symm hac) (Ne.symm hzc) hya (Ne.symm hzy) ?_ ?_
  · rw [show (insert a ({c, y} : Finset V)) = {y, c, a} from triple_perm (fun t => by tauto)]
    exact hyca
  · rw [show (insert z ({c, y} : Finset V)) = {c, z, y} from triple_perm (fun t => by tauto)]
    exact hczy

/-- `bc ∈ CN(a,z)` for a slot `z` of `A`. -/
theorem base_mem_CN {a b c z : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hz : z ∈ grp H a b c) : ({b, c} : Finset V) ∈ CN H {a, z} :=
  option_mem_CN hH hT (mem_of_mem_erase hz)

/-- Every member of `CN(a,z)` is `bc`, some `{b,x}` with `x` an `R_b`-neighbour, or some `{c,y}` with `y` an
`R_c`-neighbour (proof of Lemma 1; uses F1). -/
theorem mem_CN_slot {a b c z : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hz : z ∈ grp H a b c) {P : Finset V}
    (hP : P ∈ CN H {a, z}) :
    P = {b, c} ∨ (∃ x ∈ nb H a b c z, P = {b, x}) ∨ (∃ y ∈ nc H a b c z, P = {c, y}) := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  obtain ⟨hza, hzb, hzc, -⟩ := mem_grp.mp hz
  have hbase := base_mem_CN hT hH hz
  have hint := CN_intersecting hH hav (Ne.symm hza) hP hbase
  obtain ⟨hPp, hdis, haP, hzP⟩ := mem_CN_pair.mp hP
  have hPc : P.card = 2 := mem_pairs.mp hPp
  have hqa : a ∈ ({a, z} : Finset V) := mem_insert_self a {z}
  have hqz : z ∈ ({a, z} : Finset V) := mem_insert_of_mem (mem_singleton_self z)
  obtain ⟨t, htP, htbc⟩ := not_disjoint_iff.mp hint
  by_cases hbP : b ∈ P
  · obtain ⟨u, hub, rfl⟩ := exists_eq_pair_of_mem hPc hbP
    by_cases huc : u = c
    · left; rw [huc]
    · right; left
      have hua : u ≠ a := fun h => not_mem_of_inter_empty hdis (mem_insert_of_mem (mem_singleton.mpr rfl))
        (by rw [h]; exact hqa)
      have huz : u ≠ z := fun h => not_mem_of_inter_empty hdis (mem_insert_of_mem (mem_singleton.mpr rfl))
        (by rw [h]; exact hqz)
      refine ⟨u, mem_nb.mpr ⟨mem_grp.mpr ⟨huc, hua, hub, ?_⟩, huz, ?_⟩, rfl⟩
      · rw [show ({u, a, b} : Finset V) = insert a {b, u} from triple_perm (fun t => by tauto)]
        exact haP
      · rw [show ({b, u, z} : Finset V) = insert z {b, u} from triple_perm (fun t => by tauto)]
        exact hzP
  · have hcP : c ∈ P := by
      rw [mem_insert, mem_singleton] at htbc
      rcases htbc with rfl | rfl
      · exact absurd htP hbP
      · exact htP
    obtain ⟨u, huc, rfl⟩ := exists_eq_pair_of_mem hPc hcP
    right; right
    have hub : u ≠ b := fun h => hbP (by rw [h]; exact mem_insert_of_mem (mem_singleton_self b))
    have hua : u ≠ a := fun h => not_mem_of_inter_empty hdis (mem_insert_of_mem (mem_singleton.mpr rfl))
      (by rw [h]; exact hqa)
    have huz : u ≠ z := fun h => not_mem_of_inter_empty hdis (mem_insert_of_mem (mem_singleton.mpr rfl))
      (by rw [h]; exact hqz)
    refine ⟨u, mem_nc.mpr ⟨mem_grp.mpr ⟨hub, huc, hua, ?_⟩, Ne.symm huz, ?_⟩, rfl⟩
    · rw [show ({u, c, a} : Finset V) = insert a {c, u} from triple_perm (fun t => by tauto)]
      exact haP
    · rw [show ({c, z, u} : Finset V) = insert z {c, u} from triple_perm (fun t => by tauto)]
      exact hzP

/-- `CN(a,z) = {bc} ∪ {bx : x ∈ nb} ∪ {cy : y ∈ nc}`. -/
theorem CN_slot_eq {a b c z : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hz : z ∈ grp H a b c) :
    CN H {a, z} = insert {b, c} ((nb H a b c z).image (fun x => ({b, x} : Finset V)) ∪
      (nc H a b c z).image (fun y => ({c, y} : Finset V))) := by
  ext P
  simp only [mem_insert, mem_union, mem_image]
  constructor
  · intro hP
    rcases mem_CN_slot hT hH hav hz hP with h | ⟨x, hx, h⟩ | ⟨y, hy, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨x, hx, h.symm⟩)
    · exact Or.inr (Or.inr ⟨y, hy, h.symm⟩)
  · rintro (rfl | ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact base_mem_CN hT hH hz
    · exact pair_b_mem_CN hT hH hz hx
    · exact pair_c_mem_CN hT hH hz hy

/-- **Lemma 1** (pw2312 §2). For a slot `z` of `A`: `s_{az} = 1 + d_{R_b}(z) + d_{R_c}(z)`. -/
theorem card_CN_slot {a b c z : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hz : z ∈ grp H a b c) :
    (CN H {a, z}).card = 1 + (nb H a b c z).card + (nc H a b c z).card := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  rw [CN_slot_eq hT hH hav hz]
  have hxb : ∀ x ∈ nb H a b c z, x ≠ b ∧ x ≠ c := fun x hx => by
    obtain ⟨hxC, -, -⟩ := mem_nb.mp hx
    obtain ⟨hxc, -, hxb, -⟩ := mem_grp.mp hxC
    exact ⟨hxb, hxc⟩
  have hyc : ∀ y ∈ nc H a b c z, y ≠ b ∧ y ≠ c := fun y hy => by
    obtain ⟨hyB, -, -⟩ := mem_nc.mp hy
    obtain ⟨hyb, hyc, -, -⟩ := mem_grp.mp hyB
    exact ⟨hyb, hyc⟩
  have hnot : ({b, c} : Finset V) ∉ (nb H a b c z).image (fun x => ({b, x} : Finset V)) ∪
      (nc H a b c z).image (fun y => ({c, y} : Finset V)) := by
    simp only [mem_union, mem_image, not_or, not_exists, not_and]
    refine ⟨fun x hx he => (hxb x hx).2 ?_, fun y hy he => (hyc y hy).1 ?_⟩
    · have : c ∈ ({b, x} : Finset V) := by rw [he]; exact mem_insert_of_mem (mem_singleton_self c)
      rw [mem_insert, mem_singleton] at this
      rcases this with h | h
      · exact absurd h.symm hbc
      · exact h.symm
    · have : b ∈ ({c, y} : Finset V) := by rw [he]; exact mem_insert_self b {c}
      rw [mem_insert, mem_singleton] at this
      rcases this with h | h
      · exact absurd h hbc
      · exact h.symm
  have hdisj : Disjoint ((nb H a b c z).image (fun x => ({b, x} : Finset V)))
      ((nc H a b c z).image (fun y => ({c, y} : Finset V))) := by
    rw [disjoint_left]
    simp only [mem_image]
    rintro P ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    have : b ∈ ({c, y} : Finset V) := by rw [he]; exact mem_insert_self b {x}
    rw [mem_insert, mem_singleton] at this
    rcases this with h | h
    · exact hbc h
    · exact (hyc y hy).1 h.symm
  have hinj1 : Set.InjOn (fun x => ({b, x} : Finset V)) (nb H a b c z) := by
    intro x hx x' hx' he
    have : x ∈ ({b, x'} : Finset V) := by
      rw [← show ({b, x} : Finset V) = {b, x'} from he]; exact mem_insert_of_mem (mem_singleton_self x)
    rw [mem_insert, mem_singleton] at this
    rcases this with h | h
    · exact absurd h (hxb x hx).1
    · exact h
  have hinj2 : Set.InjOn (fun y => ({c, y} : Finset V)) (nc H a b c z) := by
    intro y hy y' hy' he
    have : y ∈ ({c, y'} : Finset V) := by
      rw [← show ({c, y} : Finset V) = {c, y'} from he]; exact mem_insert_of_mem (mem_singleton_self y)
    rw [mem_insert, mem_singleton] at this
    rcases this with h | h
    · exact absurd h (hyc y hy).2
    · exact h
  rw [card_insert_of_notMem hnot, card_union_of_disjoint hdisj, card_image_of_injOn hinj1,
    card_image_of_injOn hinj2]
  omega

/-! ## Lemma 2 -/

/-- **Lemma 2** (pw2312 §2), pointwise form: an `R_b`-neighbour and an `R_c`-neighbour of the same slot of `A` are
the same vertex. -/
theorem nb_eq_nc {a b c z x y : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hz : z ∈ grp H a b c)
    (hx : x ∈ nb H a b c z) (hy : y ∈ nc H a b c z) : x = y := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  obtain ⟨hza, -, -, -⟩ := mem_grp.mp hz
  have h := CN_intersecting hH hav (Ne.symm hza) (pair_b_mem_CN hT hH hz hx) (pair_c_mem_CN hT hH hz hy)
  obtain ⟨hxC, -, -⟩ := mem_nb.mp hx
  obtain ⟨hxc, -, -, -⟩ := mem_grp.mp hxC
  obtain ⟨hyB, -, -⟩ := mem_nc.mp hy
  obtain ⟨hyb, -, -, -⟩ := mem_grp.mp hyB
  rcases mem_or_mem_of_not_disjoint h with h1 | h1
  · rw [mem_insert, mem_singleton] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 hbc
    · exact absurd h1.symm hyb
  · rw [mem_insert, mem_singleton] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 hxc
    · exact h1

/-- **Lemma 2** (pw2312 §2). If a slot `z` of `A` has neighbours in both of its relations, it has exactly one in
each, and both are slots of the same vertex `w`. -/
theorem lemma2 {a b c z : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hz : z ∈ grp H a b c)
    (hb : (nb H a b c z).Nonempty) (hc : (nc H a b c z).Nonempty) :
    ∃ w, nb H a b c z = {w} ∧ nc H a b c z = {w} := by
  obtain ⟨x, hx⟩ := hb
  obtain ⟨y, hy⟩ := hc
  have hxy := nb_eq_nc hT hH hav hz hx hy
  subst hxy
  refine ⟨x, ?_, ?_⟩
  · exact eq_singleton_iff_unique_mem.mpr ⟨hx, fun x' hx' => nb_eq_nc hT hH hav hz hx' hy⟩
  · exact eq_singleton_iff_unique_mem.mpr ⟨hy, fun y' hy' => (nb_eq_nc hT hH hav hz hx hy').symm⟩

/-- Lemma 2 in cardinality form. -/
theorem lemma2_card {a b c z : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hz : z ∈ grp H a b c)
    (hb : 0 < (nb H a b c z).card) (hc : 0 < (nc H a b c z).card) :
    (nb H a b c z).card = 1 ∧ (nc H a b c z).card = 1 := by
  obtain ⟨w, h1, h2⟩ := lemma2 hT hH hav hz (card_pos.mp hb) (card_pos.mp hc)
  rw [h1, h2, card_singleton]
  exact ⟨rfl, rfl⟩

/-! ## `σ` and `τ` as sums over slots -/

section Sums

variable (H) in
/-- The cost `1/(2(1 + d(z)))` of a slot `z` of `A` in the view `(a,b,c)`. -/
def slotCost (a b c z : V) : ℚ :=
  1 / (2 * (1 + ((nb H a b c z).card : ℚ) + ((nc H a b c z).card : ℚ)))

variable (H) in
/-- `1/k_bc = 1/(1 + |A|)`, the `σ`-term of the pair `bc` in the view `(a,b,c)`. -/
def groupSigma (a b c : V) : ℚ := 1 / (1 + ((grp H a b c).card : ℚ))

/-- The options through `bc`, by Lemma 1. -/
theorem tau_group {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    ∑ z ∈ (link H {b, c}).erase a, 1 / (2 * ((CN H {a, z}).card : ℚ)) =
      ∑ z ∈ grp H a b c, slotCost H a b c z := by
  refine sum_congr rfl (fun z hz => ?_)
  rw [card_CN_slot hT hH hav hz, slotCost]
  push_cast
  ring_nf

omit [Fintype V] in
theorem triple_rot {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) : ({b, c, a} : Finset V) ∈ H := by
  rw [show ({b, c, a} : Finset V) = {a, b, c} from triple_perm (fun t => by tauto)]; exact hT

/-- `τ(T)` as the sum of the slot costs over the three groups (pw2312 §2, after Lemma 1). -/
theorem tauW_slots {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    tauW H {a, b, c} = ∑ z ∈ grp H a b c, slotCost H a b c z + ∑ y ∈ grp H b c a, slotCost H b c a y +
      ∑ x ∈ grp H c a b, slotCost H c a b x := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  have hT1 := triple_rot hT
  have hT2 := triple_rot hT1
  rw [tauW_triple hab hac hbc, tau_group hT hH hav, pair_comm a c, tau_group hT1 hH hav, tau_group hT2 hH hav]

/-- `k_bc = 1 + |A|`. -/
theorem codeg_eq_one_add_card_grp {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H) :
    (codeg H {b, c} : ℚ) = 1 + ((grp H a b c).card : ℚ) := by
  obtain ⟨-, -, hbc⟩ := triple_ne (hH _ hT)
  have ha := (apex_mem hH hT).2.1
  rw [codeg_eq_card_link hH (card_pair hbc), grp, card_erase_of_mem ha]
  have : 1 ≤ (link H {b, c}).card := one_le_card.mpr ⟨a, ha⟩
  rw [Nat.cast_sub this]
  push_cast
  ring_nf

/-- `σ(T)` as the sum of the three group terms `1/(1 + |X|)`. -/
theorem sigmaW_slots {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H) :
    sigmaW H {a, b, c} = groupSigma H a b c + groupSigma H b c a + groupSigma H c a b := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  have hT1 := triple_rot hT
  have hT2 := triple_rot hT1
  rw [sigmaW_triple hab hac hbc, groupSigma, groupSigma, groupSigma, ← codeg_eq_one_add_card_grp hT hH,
    ← codeg_eq_one_add_card_grp hT1 hH, ← codeg_eq_one_add_card_grp hT2 hH, pair_comm c a]

end Sums

/-! ## Slot types and the per-group counts -/

section Types

variable (H)

/-- Slots of `A` that are type 1 in `R_c` (in the view `(a,b,c)`: `|nc| > 0`, `|nb| = 0`); count `ac = f_0`. -/
def fset (a b c : V) : Finset V :=
  (grp H a b c).filter (fun z => 0 < (nc H a b c z).card ∧ (nb H a b c z).card = 0)

/-- Slots of `A` that are type 1 in `R_b` (`|nb| > 0`, `|nc| = 0`); count `ab = g_0`. -/
def gset (a b c : V) : Finset V :=
  (grp H a b c).filter (fun z => 0 < (nb H a b c z).card ∧ (nc H a b c z).card = 0)

/-- Type-2 slots of `A` (neighbours in both relations); count `tA = t_0`. -/
def tset (a b c : V) : Finset V :=
  (grp H a b c).filter (fun z => 0 < (nb H a b c z).card ∧ 0 < (nc H a b c z).card)

/-- Isolated slots of `A`; count `i_A`. -/
def iset (a b c : V) : Finset V :=
  (grp H a b c).filter (fun z => (nb H a b c z).card = 0 ∧ (nc H a b c z).card = 0)

end Types

omit [Fintype V] [DecidableEq V] in
/-- Splitting a sum over a finset into the four classes of two counts `p` (the `nb`-degree) and `q` (the
`nc`-degree). -/
theorem sum_four_classes (s : Finset V) (p q : V → ℕ) (F : V → ℚ) :
    ∑ z ∈ s, F z = ∑ z ∈ s.filter (fun z => p z = 0 ∧ q z = 0), F z +
      ∑ z ∈ s.filter (fun z => 0 < q z ∧ p z = 0), F z +
      ∑ z ∈ s.filter (fun z => 0 < p z ∧ q z = 0), F z +
      ∑ z ∈ s.filter (fun z => 0 < p z ∧ 0 < q z), F z := by
  simp only [sum_filter, ← sum_add_distrib]
  refine sum_congr rfl (fun z _ => ?_)
  by_cases hp : p z = 0 <;> by_cases hq : q z = 0 <;> simp [hp, hq, Nat.pos_iff_ne_zero]

/-- `|A| = i_A + f_0 + g_0 + t_0`. -/
theorem card_grp_eq (a b c : V) :
    ((grp H a b c).card : ℚ) = ((iset H a b c).card : ℚ) + ((fset H a b c).card : ℚ) +
      ((gset H a b c).card : ℚ) + ((tset H a b c).card : ℚ) := by
  have h := sum_four_classes (grp H a b c) (fun z => (nb H a b c z).card) (fun z => (nc H a b c z).card)
    (fun _ => (1 : ℚ))
  simp only [sum_const, nsmul_eq_mul, mul_one] at h
  exact h

/-- The exact contribution of one group (pw2312 Lemma 3, before any inequality): with `i, f, g, t` the class
counts of `A`, `1/k_bc + Σ_{z ∈ A} 1/(2(1+d(z))) = 1/(1+f+g+t+i) + i/2 + t/6 + Σ_{f-slots} 1/(2(1+d_{R_c}))
+ Σ_{g-slots} 1/(2(1+d_{R_b}))`. Type-2 slots cost `1/6` by Lemma 2. -/
theorem group_exact {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    groupSigma H a b c + ∑ z ∈ grp H a b c, slotCost H a b c z =
      1 / (1 + ((fset H a b c).card : ℚ) + ((gset H a b c).card : ℚ) + ((tset H a b c).card : ℚ) +
        ((iset H a b c).card : ℚ)) + ((iset H a b c).card : ℚ) / 2 + ((tset H a b c).card : ℚ) / 6 +
      ∑ z ∈ fset H a b c, 1 / (2 * (1 + ((nc H a b c z).card : ℚ))) +
      ∑ z ∈ gset H a b c, 1 / (2 * (1 + ((nb H a b c z).card : ℚ))) := by
  have hsplit := sum_four_classes (grp H a b c) (fun z => (nb H a b c z).card)
    (fun z => (nc H a b c z).card) (slotCost H a b c)
  have hi : ∑ z ∈ iset H a b c, slotCost H a b c z = ((iset H a b c).card : ℚ) / 2 := by
    rw [div_eq_mul_one_div, ← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl (fun z hz => ?_)
    obtain ⟨-, h1, h2⟩ := mem_filter.mp hz
    rw [slotCost, h1, h2]; norm_num
  have ht : ∑ z ∈ tset H a b c, slotCost H a b c z = ((tset H a b c).card : ℚ) / 6 := by
    rw [div_eq_mul_one_div, ← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl (fun z hz => ?_)
    obtain ⟨hz', h1, h2⟩ := mem_filter.mp hz
    obtain ⟨e1, e2⟩ := lemma2_card hT hH hav hz' h1 h2
    rw [slotCost, e1, e2]; norm_num
  have hf : ∑ z ∈ fset H a b c, slotCost H a b c z =
      ∑ z ∈ fset H a b c, 1 / (2 * (1 + ((nc H a b c z).card : ℚ))) := by
    refine sum_congr rfl (fun z hz => ?_)
    obtain ⟨-, -, h2⟩ := mem_filter.mp hz
    rw [slotCost, h2]; norm_num
  have hg : ∑ z ∈ gset H a b c, slotCost H a b c z =
      ∑ z ∈ gset H a b c, 1 / (2 * (1 + ((nb H a b c z).card : ℚ))) := by
    refine sum_congr rfl (fun z hz => ?_)
    obtain ⟨-, -, h2⟩ := mem_filter.mp hz
    rw [slotCost, h2]; norm_num
  have e1 : ∑ z ∈ (grp H a b c).filter (fun z => (nb H a b c z).card = 0 ∧ (nc H a b c z).card = 0),
      slotCost H a b c z = ∑ z ∈ iset H a b c, slotCost H a b c z := rfl
  have e2 : ∑ z ∈ (grp H a b c).filter (fun z => 0 < (nc H a b c z).card ∧ (nb H a b c z).card = 0),
      slotCost H a b c z = ∑ z ∈ fset H a b c, slotCost H a b c z := rfl
  have e3 : ∑ z ∈ (grp H a b c).filter (fun z => 0 < (nb H a b c z).card ∧ (nc H a b c z).card = 0),
      slotCost H a b c z = ∑ z ∈ gset H a b c, slotCost H a b c z := rfl
  have e4 : ∑ z ∈ (grp H a b c).filter (fun z => 0 < (nb H a b c z).card ∧ 0 < (nc H a b c z).card),
      slotCost H a b c z = ∑ z ∈ tset H a b c, slotCost H a b c z := rfl
  rw [hsplit, e1, e2, e3, e4, hi, ht, hf, hg, groupSigma, card_grp_eq]
  ring

end SlotModel
end Erdos643R3
