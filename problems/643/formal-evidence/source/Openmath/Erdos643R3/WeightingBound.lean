import Mathlib
import Openmath.Erdos643R3.Weighting
import Openmath.Erdos643R3.WeightingAuxArith



set_option autoImplicit false

namespace Erdos643R3
namespace WeightingBound

open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.WeightingAux

section FinsetFacts

variable {α : Type*} [DecidableEq α]

lemma erase_triple_a {a b c : α} (hab : a ≠ b) (hac : a ≠ c) :
    ({a, b, c} : Finset α).erase a = {b, c} := by
  apply erase_insert
  rw [mem_insert, mem_singleton]
  rintro (h | h)
  · exact hab h
  · exact hac h

lemma erase_triple_b {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) :
    ({a, b, c} : Finset α).erase b = {a, c} := by
  rw [erase_insert_of_ne hab,
    erase_insert (show b ∉ ({c} : Finset α) by rw [mem_singleton]; exact hbc)]

lemma erase_triple_c {a b c : α} (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset α).erase c = {a, b} := by
  rw [erase_insert_of_ne hac, erase_insert_of_ne hbc, erase_singleton, insert_empty]

lemma triple_bac (a b c : α) : ({b, a, c} : Finset α) = {a, b, c} := insert_comm b a {c}

lemma triple_cab (a b c : α) : ({c, a, b} : Finset α) = {a, b, c} := by
  ext t; simp only [mem_insert, mem_singleton]; tauto

lemma triple_bca (a b c : α) : ({b, c, a} : Finset α) = {a, b, c} := by
  ext t; simp only [mem_insert, mem_singleton]; tauto

lemma triple_cba (a b c : α) : ({c, b, a} : Finset α) = {a, b, c} := by
  ext t; simp only [mem_insert, mem_singleton]; tauto

lemma triple_acb (a b c : α) : ({a, c, b} : Finset α) = {a, b, c} := by
  ext t; simp only [mem_insert, mem_singleton]; tauto

end FinsetFacts

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## `σ` and `τ` of a labelled triple -/

/-- `τ({a,b,c})` is the sum of the option sums through `bc` (apex `a`), `ca` (apex `b`) and `ab` (apex `c`). -/
theorem tauW_triple {H : Finset (Finset V)} {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    tauW H {a, b, c} =
      ∑ z ∈ (link H {b, c}).erase a, 1 / (2 * ((CN H {a, z}).card : ℚ)) +
      ∑ z ∈ (link H {a, c}).erase b, 1 / (2 * ((CN H {b, z}).card : ℚ)) +
      ∑ z ∈ (link H {a, b}).erase c, 1 / (2 * ((CN H {c, z}).card : ℚ)) := by
  have ha : a ∉ ({b, c} : Finset V) := by
    rw [mem_insert, mem_singleton]
    rintro (h | h)
    · exact hab h
    · exact hac h
  have hb : b ∉ ({c} : Finset V) := by rw [mem_singleton]; exact hbc
  unfold tauW
  rw [sum_insert ha, sum_insert hb, sum_singleton, erase_triple_a hab hac, erase_triple_b hab hbc,
    erase_triple_c hac hbc]
  ring

omit [Fintype V] in
/-- `σ({a,b,c}) = 1/k_bc + 1/k_ac + 1/k_ab`. -/
theorem sigmaW_triple {H : Finset (Finset V)} {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    sigmaW H {a, b, c} =
      1 / (codeg H {b, c} : ℚ) + 1 / (codeg H {a, c} : ℚ) + 1 / (codeg H {a, b} : ℚ) := by
  have ha : a ∉ ({b, c} : Finset V) := by
    rw [mem_insert, mem_singleton]
    rintro (h | h)
    · exact hab h
    · exact hac h
  have hb : b ∉ ({c} : Finset V) := by rw [mem_singleton]; exact hbc
  have hT3 : ({a, b, c} : Finset V).card = 3 := card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  rw [sigmaW_eq_sum_vertices hT3, sum_insert ha, sum_insert hb, sum_singleton,
    erase_triple_a hab hac, erase_triple_b hab hbc, erase_triple_c hac hbc]
  ring

/-- The number of options through a pair `p` of `T` (apex `w ∈ L(p)`) is `k_p - 1`. -/
theorem card_options {H : Finset (Finset V)} (hH : Uniform H) {p : Finset V} (hp : p.card = 2)
    {w : V} (hw : w ∈ link H p) : (((link H p).erase w).card : ℚ) = (codeg H p : ℚ) - 1 := by
  have h1 := card_erase_of_mem hw
  have h2 : 1 ≤ (link H p).card := one_le_card.mpr ⟨w, hw⟩
  rw [codeg_eq_card_link hH hp, h1, Nat.cast_sub h2, Nat.cast_one]

/-! ## Draft Lemma 5: the `(2,2,2)` triangle analysis -/

/-- For an option `{a,z}` through `bc` with `L(ab) ⊆ {c,x}` and `L(ac) ⊆ {b,y}`, the members of `CN(a,z)` are among
`bc, bx, cy`; so `s_{az} ≥ 3` forces `bx, cy ∈ CN(a,z)`, hence `x = y` and `x ≠ z`. -/
theorem triangle_222 {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {a b c z x y : V}
    (hT : ({a, b, c} : Finset V) ∈ H) (hz : z ∈ link H {b, c}) (hza : z ≠ a)
    (hLab : link H {a, b} ⊆ {c, x}) (hLac : link H {a, c} ⊆ {b, y}) (hxc : x ≠ c) (hyb : y ≠ b)
    (h3 : 3 ≤ (CN H {a, z}).card) : x = y ∧ x ≠ z := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  have hbcCN := option_mem_CN hH hT hz
  have hsub : CN H {a, z} ⊆ {{b, c}, {b, x}, {c, y}} := by
    intro P hP
    obtain ⟨hPp, -, haP, -⟩ := mem_CN_pair.mp hP
    have hmeet := mem_or_mem_of_not_disjoint (CN_intersecting hH hav (Ne.symm hza) hbcCN hP)
    rw [mem_insert, mem_insert, mem_singleton]
    rcases hmeet with hb | hc
    · obtain ⟨u, -, rfl⟩ := exists_eq_pair_of_mem (mem_pairs.mp hPp) hb
      have hu : u ∈ link H {a, b} := by
        rw [mem_link_iff_of_uniform hH (card_pair hab)]
        rw [triple_cab]; exact haP
      have hu' := hLab hu
      rw [mem_insert, mem_singleton] at hu'
      rcases hu' with h | h
      · left; rw [h]
      · right; left; rw [h]
    · obtain ⟨u, -, rfl⟩ := exists_eq_pair_of_mem (mem_pairs.mp hPp) hc
      have hu : u ∈ link H {a, c} := by
        rw [mem_link_iff_of_uniform hH (card_pair hac)]
        rw [triple_cab]; exact haP
      have hu' := hLac hu
      rw [mem_insert, mem_singleton] at hu'
      rcases hu' with h | h
      · left; rw [h]; exact pair_comm c b
      · right; right; rw [h]
  have hbx : ({b, x} : Finset V) ∈ CN H {a, z} := by
    by_contra hn
    have hsub2 : CN H {a, z} ⊆ {{b, c}, {c, y}} := by
      intro P hP
      have hP3 := hsub hP
      rw [mem_insert, mem_insert, mem_singleton] at hP3
      rw [mem_insert, mem_singleton]
      rcases hP3 with h | h | h
      · exact Or.inl h
      · have hm : ({b, x} : Finset V) ∈ CN H {a, z} := h ▸ hP
        exact absurd hm hn
      · exact Or.inr h
    have h1 := card_le_card hsub2
    have h2 : ({{b, c}, {c, y}} : Finset (Finset V)).card ≤ 2 := card_le_two
    omega
  have hcy : ({c, y} : Finset V) ∈ CN H {a, z} := by
    by_contra hn
    have hsub2 : CN H {a, z} ⊆ {{b, c}, {b, x}} := by
      intro P hP
      have hP3 := hsub hP
      rw [mem_insert, mem_insert, mem_singleton] at hP3
      rw [mem_insert, mem_singleton]
      rcases hP3 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · have hm : ({c, y} : Finset V) ∈ CN H {a, z} := h ▸ hP
        exact absurd hm hn
    have h1 := card_le_card hsub2
    have h2 : ({{b, c}, {b, x}} : Finset (Finset V)).card ≤ 2 := card_le_two
    omega
  have hxz : x ≠ z := by
    intro h
    have hdis := (mem_CN_pair.mp hbx).2.1
    have hm : x ∈ ({b, x} : Finset V) ∩ {a, z} := by
      rw [mem_inter]
      refine ⟨mem_insert_of_mem (mem_singleton_self x), ?_⟩
      rw [h]; exact mem_insert_of_mem (mem_singleton_self z)
    rw [hdis] at hm
    exact notMem_empty x hm
  refine ⟨?_, hxz⟩
  have hmeet := mem_or_mem_of_not_disjoint (CN_intersecting hH hav (Ne.symm hza) hbx hcy)
  rw [mem_insert, mem_singleton, mem_insert, mem_singleton] at hmeet
  rcases hmeet with (h | h) | (h | h)
  · exact absurd h hbc
  · exact absurd h.symm hyb
  · exact absurd h hxc
  · exact h

/-! ## Facts about a labelled triple `T = {a,b,c} ∈ H` -/

/-- The apex of each pair of `T` lies in the link of that pair. -/
theorem apex_mem {H : Finset (Finset V)} (hH : Uniform H) {a b c : V}
    (hT : ({a, b, c} : Finset V) ∈ H) :
    c ∈ link H {a, b} ∧ a ∈ link H {b, c} ∧ b ∈ link H {a, c} := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  have hTb : ({b, a, c} : Finset V) ∈ H := by rw [triple_bac]; exact hT
  have hTc : ({c, a, b} : Finset V) ∈ H := by rw [triple_cab]; exact hT
  exact ⟨(mem_link_iff_of_uniform hH (card_pair hab)).mpr hTc,
    (mem_link_iff_of_uniform hH (card_pair hbc)).mpr hT,
    (mem_link_iff_of_uniform hH (card_pair hac)).mpr hTb⟩

/-- (3.1) for the options through `bc` (apex `a`): `1 ≤ s_{az} ≤ max(3, k_ab, k_ac)`. -/
theorem opt_bound_a {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {a b c : V}
    (hT : ({a, b, c} : Finset V) ∈ H) :
    ∀ z ∈ (link H {b, c}).erase a, 1 ≤ (CN H {a, z}).card ∧
      (CN H {a, z}).card ≤ max 3 (max (codeg H {a, b}) (codeg H {a, c})) := by
  intro z hz
  obtain ⟨hza, hz'⟩ := mem_erase.mp hz
  exact ⟨one_le_card.mpr ⟨_, option_mem_CN hH hT hz'⟩, option_bound hH hav hT hz' hza⟩

/-- (3.1) for the options through `ca` (apex `b`): `1 ≤ s_{bz} ≤ max(3, k_ab, k_bc)`. -/
theorem opt_bound_b {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {a b c : V}
    (hT : ({a, b, c} : Finset V) ∈ H) :
    ∀ z ∈ (link H {a, c}).erase b, 1 ≤ (CN H {b, z}).card ∧
      (CN H {b, z}).card ≤ max 3 (max (codeg H {a, b}) (codeg H {b, c})) := by
  have hTb : ({b, a, c} : Finset V) ∈ H := by rw [triple_bac]; exact hT
  intro z hz
  obtain ⟨hzb, hz'⟩ := mem_erase.mp hz
  have hbd := option_bound hH hav hTb hz' hzb
  rw [pair_comm b a] at hbd
  exact ⟨one_le_card.mpr ⟨_, option_mem_CN hH hTb hz'⟩, hbd⟩

/-- (3.1) for the options through `ab` (apex `c`): `1 ≤ s_{cz} ≤ max(3, k_ac, k_bc)`. -/
theorem opt_bound_c {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {a b c : V}
    (hT : ({a, b, c} : Finset V) ∈ H) :
    ∀ z ∈ (link H {a, b}).erase c, 1 ≤ (CN H {c, z}).card ∧
      (CN H {c, z}).card ≤ max 3 (max (codeg H {a, c}) (codeg H {b, c})) := by
  have hTc : ({c, a, b} : Finset V) ∈ H := by rw [triple_cab]; exact hT
  intro z hz
  obtain ⟨hzc, hz'⟩ := mem_erase.mp hz
  have hbd := option_bound hH hav hTc hz' hzc
  rw [pair_comm c a, pair_comm c b] at hbd
  exact ⟨one_le_card.mpr ⟨_, option_mem_CN hH hTc hz'⟩, hbd⟩

/-! ## Draft Lemma 5: type `(2,2,2)` -/

/-- **Lemma 5.** If the three pairs of `T` have codegree 2, then `τ(T) ≥ 7/12`: all three options have `s ≤ 3`,
and `s_{az} = s_{by} = 3` is impossible (it forces `x ≠ z` and `z = x` by `triangle_222`). -/
theorem light_222 {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {a b c : V}
    (hT : ({a, b, c} : Finset V) ∈ H)
    (e1 : codeg H {a, b} = 2) (e2 : codeg H {b, c} = 2) (e3 : codeg H {a, c} = 2) :
    7 / 12 ≤ ∑ z ∈ (link H {b, c}).erase a, 1 / (2 * ((CN H {a, z}).card : ℚ)) +
      ∑ z ∈ (link H {a, c}).erase b, 1 / (2 * ((CN H {b, z}).card : ℚ)) +
      ∑ z ∈ (link H {a, b}).erase c, 1 / (2 * ((CN H {c, z}).card : ℚ)) := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  obtain ⟨hc_ab, ha_bc, hb_ac⟩ := apex_mem hH hT
  have hLab2 : (link H {a, b}).card = 2 := by
    rw [← codeg_eq_card_link hH (card_pair hab)]; exact e1
  have hLbc2 : (link H {b, c}).card = 2 := by
    rw [← codeg_eq_card_link hH (card_pair hbc)]; exact e2
  have hLac2 : (link H {a, c}).card = 2 := by
    rw [← codeg_eq_card_link hH (card_pair hac)]; exact e3
  obtain ⟨x, hxc, hLab⟩ := exists_eq_pair_of_mem hLab2 hc_ab
  obtain ⟨z, hza, hLbc⟩ := exists_eq_pair_of_mem hLbc2 ha_bc
  obtain ⟨y, hyb, hLac⟩ := exists_eq_pair_of_mem hLac2 hb_ac
  have hZc1 : (link H {a, b}).erase c = {x} := by
    rw [hLab]; exact erase_insert (fun h => hxc (mem_singleton.mp h).symm)
  have hZa1 : (link H {b, c}).erase a = {z} := by
    rw [hLbc]; exact erase_insert (fun h => hza (mem_singleton.mp h).symm)
  have hZb1 : (link H {a, c}).erase b = {y} := by
    rw [hLac]; exact erase_insert (fun h => hyb (mem_singleton.mp h).symm)
  have hx_mem : x ∈ (link H {a, b}).erase c := by rw [hZc1]; exact mem_singleton_self x
  have hz_mem : z ∈ (link H {b, c}).erase a := by rw [hZa1]; exact mem_singleton_self z
  have hy_mem : y ∈ (link H {a, c}).erase b := by rw [hZb1]; exact mem_singleton_self y
  have sa1 := opt_bound_a hH hav hT z hz_mem
  have sb1 := opt_bound_b hH hav hT y hy_mem
  have sc1 := opt_bound_c hH hav hT x hx_mem
  rw [e1, e3] at sa1
  rw [e1, e2] at sb1
  rw [e3, e2] at sc1
  rw [hZc1, hZa1, hZb1, sum_singleton, sum_singleton, sum_singleton]
  have hz' : z ∈ link H {b, c} := by
    rw [hLbc]; exact mem_insert_of_mem (mem_singleton_self z)
  have hy' : y ∈ link H {c, a} := by
    rw [pair_comm c a, hLac]; exact mem_insert_of_mem (mem_singleton_self y)
  have hLab' : link H {a, b} ⊆ {c, x} := fun t ht => by rw [hLab] at ht; exact ht
  have hLac' : link H {a, c} ⊆ {b, y} := fun t ht => by rw [hLac] at ht; exact ht
  have hLbc' : link H {b, c} ⊆ {a, z} := fun t ht => by rw [hLbc] at ht; exact ht
  have hLba' : link H {b, a} ⊆ {c, x} := fun t ht => by
    rw [pair_comm b a, hLab] at ht; exact ht
  have hTb' : ({b, c, a} : Finset V) ∈ H := by rw [triple_bca]; exact hT
  have t1 : 3 ≤ (CN H {a, z}).card → x = y ∧ x ≠ z :=
    triangle_222 (x := x) (y := y) hH hav hT hz' hza hLab' hLac' hxc hyb
  have t2 : 3 ≤ (CN H {b, y}).card → z = x ∧ z ≠ y :=
    triangle_222 (a := b) (b := c) (c := a) (z := y) (x := z) (y := x) hH hav hTb' hy' hyb
      hLbc' hLba' hza hxc
  have hor : (CN H {a, z}).card ≤ 2 ∨ (CN H {b, y}).card ≤ 2 := by
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have r1 := t1 (by omega)
    have r2 := t2 (by omega)
    exact r1.2 r2.1.symm
  exact light_arith (CN H {a, z}).card (CN H {b, y}).card (CN H {c, x}).card
    ⟨sa1.1, by omega⟩ ⟨sb1.1, by omega⟩ ⟨sc1.1, by omega⟩ hor

/-! ## The per-triple inequality -/

/-- Case B of §3 (`k_ab ≤ k_bc ≤ k_ca`, `k_bc ≥ 4`): `M_ab = M_bc = k_ca`, `M_ca = k_bc`; sub-cases B1 (`ρ ≥ 7/9`) and
B2 (`ρ < 7/9`, exchange lemma on `U = ∪_z U_z` and `V = ∪_z V_z`). -/
theorem per_triple_caseB {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {a b c : V}
    (hT : ({a, b, c} : Finset V) ∈ H)
    (h12 : codeg H {a, b} ≤ codeg H {b, c}) (h23 : codeg H {b, c} ≤ codeg H {a, c})
    (hB : 4 ≤ codeg H {b, c}) :
    4 / 3 ≤ tauW H {a, b, c} + sigmaW H {a, b, c} / 2 := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  rw [tauW_triple hab hac hbc, sigmaW_triple hab hac hbc]
  obtain ⟨hc_ab, ha_bc, hb_ac⟩ := apex_mem hH hT
  have hTc : ({c, a, b} : Finset V) ∈ H := by rw [triple_cab]; exact hT
  have hk1pos : 1 ≤ codeg H {a, b} := by
    rw [codeg_eq_card_link hH (card_pair hab)]; exact one_le_card.mpr ⟨c, hc_ab⟩
  have hZc := card_options hH (card_pair hab) hc_ab
  have hZa := card_options hH (card_pair hbc) ha_bc
  have hZb := card_options hH (card_pair hac) hb_ac
  have hsa := opt_bound_a hH hav hT
  have hsb := opt_bound_b hH hav hT
  have hsc := opt_bound_c hH hav hT
  have sa : ∀ z ∈ (link H {b, c}).erase a,
      1 ≤ (CN H {a, z}).card ∧ (CN H {a, z}).card ≤ codeg H {a, c} := by
    intro z hz
    have := (hsa z hz).2
    exact ⟨(hsa z hz).1, by omega⟩
  have sb : ∀ z ∈ (link H {a, c}).erase b,
      1 ≤ (CN H {b, z}).card ∧ (CN H {b, z}).card ≤ codeg H {b, c} := by
    intro z hz
    have := (hsb z hz).2
    exact ⟨(hsb z hz).1, by omega⟩
  by_cases hρ : 7 * codeg H {b, c} ≤ 9 * codeg H {a, b}
  · -- B1: `ρ ≥ 7/9`
    have sc : ∀ z ∈ (link H {a, b}).erase c,
        1 ≤ (CN H {c, z}).card ∧ (CN H {c, z}).card ≤ codeg H {a, c} := by
      intro z hz
      have := (hsc z hz).2
      exact ⟨(hsc z hz).1, by omega⟩
    have tc := sum_ge_of_le _ _ _ sc
    have ta := sum_ge_of_le _ _ _ sa
    have tb := sum_ge_of_le _ _ _ sb
    rw [hZc] at tc
    rw [hZa] at ta
    rw [hZb] at tb
    have := B1_arith _ _ _ hk1pos h12 h23 hB hρ _ _ _ tc ta tb
    linarith
  · -- B2: `ρ < 7/9`
    have hρ' : 9 * codeg H {a, b} < 7 * codeg H {b, c} := by omega
    obtain ⟨U, hU⟩ : ∃ U : Finset V, U = ((link H {a, b}).erase c).biUnion
        (fun z => (link H {a, c} ∩ link H {a, z}).erase b) := ⟨_, rfl⟩
    obtain ⟨W, hW⟩ : ∃ W : Finset V, W = ((link H {a, b}).erase c).biUnion
        (fun z => (link H {b, c} ∩ link H {b, z}).erase a) := ⟨_, rfl⟩
    have hUsub : U ⊆ (link H {a, c}).erase b := by
      intro u hu
      rw [hU, mem_biUnion] at hu
      obtain ⟨z, -, hu⟩ := hu
      obtain ⟨hub, hu'⟩ := mem_erase.mp hu
      exact mem_erase.mpr ⟨hub, (mem_inter.mp hu').1⟩
    have hWsub : W ⊆ (link H {b, c}).erase a := by
      intro v hv
      rw [hW, mem_biUnion] at hv
      obtain ⟨z, -, hv⟩ := hv
      obtain ⟨hva, hv'⟩ := mem_erase.mp hv
      exact mem_erase.mpr ⟨hva, (mem_inter.mp hv').1⟩
    have hUb : ∀ u ∈ U, (CN H {b, u}).card ≤ max 3 (codeg H {a, b}) := by
      intro u hu
      rw [hU, mem_biUnion] at hu
      obtain ⟨z, hz, hu⟩ := hu
      obtain ⟨hzc, hz'⟩ := mem_erase.mp hz
      obtain ⟨hub, hu'⟩ := mem_erase.mp hu
      exact (exchange hH hav hT hz' hzc hu' hub).2.2.2
    have hWa : ∀ v ∈ W, (CN H {a, v}).card ≤ max 3 (codeg H {a, b}) := by
      intro v hv
      rw [hW, mem_biUnion] at hv
      obtain ⟨z, hz, hv⟩ := hv
      obtain ⟨hzc, hz'⟩ := mem_erase.mp hz
      obtain ⟨hva, hv'⟩ := mem_erase.mp hv
      exact (exchange_mirror hH hav hT hz' hzc hv' hva).2.2.2
    have hUz : ∀ z ∈ (link H {a, b}).erase c,
        (link H {a, c} ∩ link H {a, z}).card ≤ U.card + 1 := by
      intro z hz
      calc (link H {a, c} ∩ link H {a, z}).card ≤ (insert b U).card := by
            apply card_le_card
            intro t ht
            rw [mem_insert]
            by_cases htb : t = b
            · exact Or.inl htb
            · right
              rw [hU, mem_biUnion]
              exact ⟨z, hz, mem_erase.mpr ⟨htb, ht⟩⟩
        _ ≤ U.card + 1 := card_insert_le _ _
    have hWz : ∀ z ∈ (link H {a, b}).erase c,
        (link H {b, c} ∩ link H {b, z}).card ≤ W.card + 1 := by
      intro z hz
      calc (link H {b, c} ∩ link H {b, z}).card ≤ (insert a W).card := by
            apply card_le_card
            intro t ht
            rw [mem_insert]
            by_cases hta : t = a
            · exact Or.inl hta
            · right
              rw [hW, mem_biUnion]
              exact ⟨z, hz, mem_erase.mpr ⟨hta, ht⟩⟩
        _ ≤ W.card + 1 := card_insert_le _ _
    have sc : ∀ z ∈ (link H {a, b}).erase c,
        1 ≤ (CN H {c, z}).card ∧ (CN H {c, z}).card ≤ max 3 (1 + max U.card W.card) := by
      intro z hz
      obtain ⟨hzc, hz'⟩ := mem_erase.mp hz
      have h := option_bound_link hH hav hTc hz' hzc
      rw [pair_comm c a, pair_comm c b] at h
      have h1 := hUz z hz
      have h2 := hWz z hz
      exact ⟨(hsc z hz).1, by omega⟩
    have tc := sum_ge_of_le _ _ _ sc
    have tb := sum_ge_split _ _ hUsub (fun z => (CN H {b, z}).card) _ _ sb hUb
    have ta := sum_ge_split _ _ hWsub (fun z => (CN H {a, z}).card) _ _ sa hWa
    rw [hZc] at tc
    rw [hZb] at tb
    rw [hZa] at ta
    have := B2_arith _ _ _ U.card W.card hk1pos hB h23 hρ' _ _ _ tc tb ta
    linarith

/-- Case A of §3 (`k_ab ≤ k_bc ≤ k_ca`, `k_bc ≤ 3`): `M_ca = 3`; `k_ca ≥ 9`, the 40-row table (`k_ca ≤ 8`) and the
`(2,2,2)` row via Lemma 5. -/
theorem per_triple_caseA {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {a b c : V}
    (hT : ({a, b, c} : Finset V) ∈ H)
    (h12 : codeg H {a, b} ≤ codeg H {b, c}) (h23 : codeg H {b, c} ≤ codeg H {a, c})
    (hB3 : codeg H {b, c} ≤ 3) :
    4 / 3 ≤ tauW H {a, b, c} + sigmaW H {a, b, c} / 2 := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  rw [tauW_triple hab hac hbc, sigmaW_triple hab hac hbc]
  obtain ⟨hc_ab, ha_bc, hb_ac⟩ := apex_mem hH hT
  have hk1pos : 1 ≤ codeg H {a, b} := by
    rw [codeg_eq_card_link hH (card_pair hab)]; exact one_le_card.mpr ⟨c, hc_ab⟩
  have hZc := card_options hH (card_pair hab) hc_ab
  have hZa := card_options hH (card_pair hbc) ha_bc
  have hZb := card_options hH (card_pair hac) hb_ac
  have hsa := opt_bound_a hH hav hT
  have hsb := opt_bound_b hH hav hT
  have hsc := opt_bound_c hH hav hT
  have e6 : (1 : ℚ) / (2 * ((3 : ℕ) : ℚ)) = 1 / 6 := by norm_num
  have sb3 : ∀ z ∈ (link H {a, c}).erase b,
      1 ≤ (CN H {b, z}).card ∧ (CN H {b, z}).card ≤ 3 := by
    intro z hz
    have := (hsb z hz).2
    exact ⟨(hsb z hz).1, by omega⟩
  have tb := sum_ge_of_le _ _ _ sb3
  rw [hZb, e6] at tb
  by_cases h9 : 9 ≤ codeg H {a, c}
  · have hc0 : 0 ≤ ∑ z ∈ (link H {a, b}).erase c, 1 / (2 * ((CN H {c, z}).card : ℚ)) :=
      sum_nonneg (fun z _ => by positivity)
    have ha0 : 0 ≤ ∑ z ∈ (link H {b, c}).erase a, 1 / (2 * ((CN H {a, z}).card : ℚ)) :=
      sum_nonneg (fun z _ => by positivity)
    have := caseA_tail (codeg H {a, b}) (codeg H {b, c}) _ h9 _ _ _ hc0 ha0 tb
    linarith
  · by_cases h4 : 4 ≤ codeg H {a, c}
    · have sa : ∀ z ∈ (link H {b, c}).erase a,
          1 ≤ (CN H {a, z}).card ∧ (CN H {a, z}).card ≤ codeg H {a, c} := by
        intro z hz
        have := (hsa z hz).2
        exact ⟨(hsa z hz).1, by omega⟩
      have sc : ∀ z ∈ (link H {a, b}).erase c,
          1 ≤ (CN H {c, z}).card ∧ (CN H {c, z}).card ≤ codeg H {a, c} := by
        intro z hz
        have := (hsc z hz).2
        exact ⟨(hsc z hz).1, by omega⟩
      have tc := sum_ge_of_le _ _ _ sc
      have ta := sum_ge_of_le _ _ _ sa
      rw [hZc] at tc
      rw [hZa] at ta
      have := caseA_mid _ _ _ hk1pos h12 hB3 h4 (by omega) _ _ _ tc ta tb
      linarith
    · by_cases h222 : codeg H {a, b} = 2 ∧ codeg H {b, c} = 2 ∧ codeg H {a, c} = 2
      · obtain ⟨e1, e2, e3⟩ := h222
        have hl := light_222 hH hav hT e1 e2 e3
        have := case222 _ _ _ e1 e2 e3 _ _ _ hl
        linarith
      · have sa : ∀ z ∈ (link H {b, c}).erase a,
            1 ≤ (CN H {a, z}).card ∧ (CN H {a, z}).card ≤ 3 := by
          intro z hz
          have := (hsa z hz).2
          exact ⟨(hsa z hz).1, by omega⟩
        have sc : ∀ z ∈ (link H {a, b}).erase c,
            1 ≤ (CN H {c, z}).card ∧ (CN H {c, z}).card ≤ 3 := by
          intro z hz
          have := (hsc z hz).2
          exact ⟨(hsc z hz).1, by omega⟩
        have tc := sum_ge_of_le _ _ _ sc
        have ta := sum_ge_of_le _ _ _ sa
        rw [hZc, e6] at tc
        rw [hZa, e6] at ta
        have := caseA_low _ _ _ hk1pos h12 h23 (by omega) h222 _ _ _ tc ta tb
        linarith

/-- **Proposition (sorted labelling).** For avoiding `H`, `T = {a,b,c} ∈ H` with `k_ab ≤ k_bc ≤ k_ca`:
`τ(T) + σ(T)/2 ≥ 4/3`. -/
theorem per_triple_sorted {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {a b c : V}
    (hT : ({a, b, c} : Finset V) ∈ H)
    (h12 : codeg H {a, b} ≤ codeg H {b, c}) (h23 : codeg H {b, c} ≤ codeg H {a, c}) :
    4 / 3 ≤ tauW H {a, b, c} + sigmaW H {a, b, c} / 2 := by
  by_cases hB : 4 ≤ codeg H {b, c}
  · exact per_triple_caseB hH hav hT h12 h23 hB
  · exact per_triple_caseA hH hav hT h12 h23 (by omega)

/-- **Proposition.** For every triple `T` of an avoiding uniform `H`: `τ(T) + σ(T)/2 ≥ 4/3`. -/
theorem per_triple {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {T : Finset V} (hT : T ∈ H) :
    4 / 3 ≤ tauW H T + sigmaW H T / 2 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp (hH T hT)
  have key : ∀ x y z : V, ({x, y, z} : Finset V) = {a, b, c} →
      codeg H {x, y} ≤ codeg H {y, z} → codeg H {y, z} ≤ codeg H {x, z} →
      4 / 3 ≤ tauW H {a, b, c} + sigmaW H {a, b, c} / 2 := by
    intro x y z e h1 h2
    have hT' : ({x, y, z} : Finset V) ∈ H := by rw [e]; exact hT
    have h := per_triple_sorted hH hav hT' h1 h2
    rw [e] at h
    exact h
  have hba : codeg H {b, a} = codeg H {a, b} := by rw [pair_comm]
  have hcb : codeg H {c, b} = codeg H {b, c} := by rw [pair_comm]
  have hca : codeg H {c, a} = codeg H {a, c} := by rw [pair_comm]
  by_cases hpq : codeg H {a, b} ≤ codeg H {b, c}
  · by_cases hqr : codeg H {b, c} ≤ codeg H {a, c}
    · exact key a b c rfl hpq hqr
    · by_cases hpr : codeg H {a, b} ≤ codeg H {a, c}
      · exact key b a c (triple_bac a b c) (by rw [hba]; exact hpr) (by omega)
      · exact key c a b (triple_cab a b c) (by rw [hca]; omega) (by rw [hcb]; exact hpq)
  · by_cases hpr : codeg H {a, b} ≤ codeg H {a, c}
    · exact key c b a (triple_cba a b c) (by rw [hcb, hba]; omega) (by rw [hba, hca]; exact hpr)
    · by_cases hqr : codeg H {b, c} ≤ codeg H {a, c}
      · exact key b c a (triple_bca a b c) (by rw [hca]; exact hqr) (by rw [hca, hba]; omega)
      · exact key a c b (triple_acb a b c) (by rw [hcb]; omega) (by rw [hcb]; omega)

/-- **Proposition (weighted form).** `(3/8) σ(T) + (3/4) τ(T) ≥ 1` for every triple `T` of an avoiding uniform `H`. -/
theorem per_triple_weighted {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {T : Finset V} (hT : T ∈ H) :
    1 ≤ 3 / 8 * sigmaW H T + 3 / 4 * tauW H T := by
  have := per_triple hH hav hT
  linarith

/-! ## The theorem and its corollary -/

/-- **Theorem.** Every finite avoiding 3-graph satisfies `|H| ≤ (3/8)|∂H| + (3/4)|CL(H)|`. -/
theorem card_le_weighted {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    (H.card : ℚ) ≤ 3 / 8 * ((shadow H).card : ℚ) + 3 / 4 * ((colink H).card : ℚ) := by
  have h := Finset.sum_le_sum (fun T hT => per_triple_weighted hH hav hT)
  rw [sum_const, nsmul_eq_mul, mul_one, sum_add_distrib, ← mul_sum, ← mul_sum, sum_sigmaW,
    sum_tauW H hH] at h
  exact h

omit [DecidableEq V] in
/-- The number of pairs of `V` is `C(|V|, 2)`. -/
theorem card_pairs : (pairs V).card = (Fintype.card V).choose 2 := by
  rw [pairs, card_powersetCard, card_univ]

/-- **Corollary.** `|H| ≤ (9/8)|O(H)|` for every finite avoiding 3-graph. -/
theorem card_le_nine_eighths_O {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    (H.card : ℚ) ≤ 9 / 8 * ((O H).card : ℚ) := by
  have h := card_le_weighted hH hav
  have h1 : (shadow H).card ≤ (O H).card := card_le_card subset_union_left
  have h2 : (colink H).card ≤ (O H).card := card_le_card subset_union_right
  have h1' : ((shadow H).card : ℚ) ≤ ((O H).card : ℚ) := by exact_mod_cast h1
  have h2' : ((colink H).card : ℚ) ≤ ((O H).card : ℚ) := by exact_mod_cast h2
  linarith

/-- **Corollary.** Every avoiding 3-graph on a finite vertex type `V` has `|H| ≤ (9/8) C(|V|, 2)`; with
`V = Fin n` this is `ex_3(n) ≤ (9/8) C(n, 2)`. -/
theorem card_le_nine_eighths_choose {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    (H.card : ℚ) ≤ 9 / 8 * (((Fintype.card V).choose 2 : ℕ) : ℚ) := by
  have h := card_le_weighted hH hav
  have h1 : (shadow H).card ≤ (Fintype.card V).choose 2 := by
    rw [← card_pairs]; exact card_le_card (shadow_subset_pairs H)
  have h2 : (colink H).card ≤ (Fintype.card V).choose 2 := by
    rw [← card_pairs]; exact card_le_card (filter_subset _ _)
  have h1' : ((shadow H).card : ℚ) ≤ (((Fintype.card V).choose 2 : ℕ) : ℚ) := by exact_mod_cast h1
  have h2' : ((colink H).card : ℚ) ≤ (((Fintype.card V).choose 2 : ℕ) : ℚ) := by exact_mod_cast h2
  linarith

end WeightingBound
end Erdos643R3
