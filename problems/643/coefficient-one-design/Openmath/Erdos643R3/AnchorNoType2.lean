import Openmath.Erdos643R3.AnchorDecomposition

set_option autoImplicit false
open scoped BigOperators
namespace Erdos643R3.AnchorNoType2
open Finset
open Erdos643R3.Identity Erdos643R3.SlotModel Erdos643R3.AnchorCaps Erdos643R3.AnchorW
open Erdos643R3.AnchorDecomposition

theorem pair_cost_amgm (n p : ℕ) :
    (1 : ℚ) - 1 / (2 * (1 + (n : ℚ))) - 1 / (2 * (1 + (p : ℚ))) ≤
      (n : ℚ) / (2 * (1 + (p : ℚ))) + (p : ℚ) / (2 * (1 + (n : ℚ))) := by
  field_simp
  nlinarith [sq_nonneg ((n : ℚ) - p)]

theorem no_type2_numeric (n p : ℕ) (hp : 1 ≤ p) :
    (11 : ℚ) / 12 ≤ WBox.betaW n 0 +
      (n : ℚ) / (2 * (1 + (p : ℚ))) + (p : ℚ) / (2 * (1 + (n : ℚ))) := by
  have hamgm := pair_cost_amgm n p
  have hp' : (1 : ℚ) ≤ p := by exact_mod_cast hp
  have h1 : (1 : ℚ) / (2 * (1 + (p : ℚ))) ≤ 1 / 4 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  have h2 : (1 : ℚ) / (2 * (1 + (n : ℚ))) ≤ 1 / (2 + (n : ℚ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg _
    linarith
  simp only [WBox.betaW, ↓reduceIte]
  linarith

/-- The one-group estimate including isolated slots, using the heavy-link condition. -/
theorem heavy_group_numeric (a k i : ℕ) (heavy : 1 ≤ k + i) :
    (11 : ℚ) / 12 ≤ 1 / (2 + (k : ℚ) + i) + WBox.gW a (1 + k) + (i : ℚ) / 2 := by
  by_cases hk : 1 ≤ k
  · have hf := G3hpArith.lemma6 (a := a) (c := 1 + k) (by omega)
    have hi := WBox.remove_isolated (2 + (k : ℚ)) i (by
      have : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      linarith) (by positivity)
    have heq : G3hpArith.f6 a (1 + k) = 1 / (2 + (k : ℚ)) + WBox.gW a (1 + k) := by
      unfold G3hpArith.f6 WBox.gW
      push_cast
      ring
    rw [heq] at hf
    linarith
  · have hk0 : k = 0 := by omega
    subst k
    have hi : (1 : ℚ) ≤ i := by exact_mod_cast (by omega : 1 ≤ i)
    have hg := WBox.gW_one a
    have hrec : (2 : ℚ) / 3 ≤ 1 / (2 + (i : ℚ)) + (i : ℚ) / 2 := by
      field_simp
      nlinarith [mul_nonneg (show 0 ≤ (i : ℚ) - 1 by linarith) (show 0 ≤ (i : ℚ) + 1 by linarith)]
    norm_num
    simp only [one_div] at hrec
    linarith

variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
variable {x y u v w : V}

theorem cross_costs_no_type2 (hB : (tset H u w x).card = 0) (hC : (tset H w x u).card = 0) :
    ((fset H u w x).card : ℚ) / (2 * (1 + ((gset H w x u).card : ℚ))) +
      ((gset H w x u).card : ℚ) / (2 * (1 + ((fset H u w x).card : ℚ))) ≤
      (∑ z ∈ fset H u w x, slotCost H u w x z) +
      (∑ z ∈ gset H w x u, slotCost H w x u z) := by
  have hcapB : ∀ z ∈ fset H u w x, degree H u w x z ≤ (gset H w x u).card := by
    intro z hz
    have hc := cross_degree_cap hz
    change degree H u w x z ≤ _ at hc
    simpa only [hC, add_zero] using hc
  have hcapC : ∀ z ∈ gset H w x u, degree H w x u z ≤ (fset H u w x).card := by
    intro z hz
    have hzm : z ∈ fset H w u x := by rw [fset_swap_gset w x u]; exact hz
    have hc := cross_degree_cap hzm
    change degree H w u x z ≤ _ at hc
    simpa only [degree_swap w x u, gset_swap_fset u w x, tset_swap u w x, hB, add_zero] using hc
  have hb := WBox.sum_cost_cap (fset H u w x) (degree H u w x) (gset H w x u).card hcapB
  have hc := WBox.sum_cost_cap (gset H w x u) (degree H w x u) (fset H u w x).card hcapC
  simp only [cost_degree] at hb hc
  linarith

theorem hW_nonneg_cross (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hB : (tset H u w x).card = 0) (hC : (tset H w x u).card = 0)
    (hp : 1 ≤ (gset H w x u).card) : 0 ≤ hW H x u w := by
  have hb := beta_le_wBase h hcard
  have hc := cross_costs_no_type2 hB hC
  have hn := no_type2_numeric (fset H u w x).card (gset H w x u).card hp
  simp only [hB, add_zero] at hb
  unfold hW
  rw [hB, hC]
  push_cast
  linarith

theorem wBase_no_cross (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hheavy : 3 ≤ codeg H {x,w}) (hB : (tset H u w x).card = 0)
    (hxB : (fset H u w x).card = 0) : (11 : ℚ) / 12 ≤ wBase H x u w := by
  have hm := h.mirror
  have hcm : (CN H {w,u}).card = 2 := by rw [pair_comm w u]; exact hcard
  have hvB : v ∈ gset H u w x := by
    have hv := v_type1_C hm
    rwa [fset_swap_gset u w x] at hv
  have hvdeg : degree H u w x v ≤ 1 + (fset H x u w).card := by
    have hv := v_degree_C_le_Au hm hcm
    change degree H u x w v ≤ _ at hv
    rwa [degree_swap u w x, gset_swap_fset x u w] at hv
  have hW : ∀ z ∈ (gset H u w x).erase v, degree H u w x z ≤ (fset H x u w).card := by
    intro z hz
    obtain ⟨hzv,hzB⟩ := mem_erase.mp hz
    obtain ⟨hzgrp,-,hzero⟩ := mem_filter.mp hzB
    have hzgrpm : z ∈ grp H u x w := by rw [grp_swap u w x]; exact hzgrp
    have hh := Ru_degree_cap hm hcm hzgrpm hzv
    rw [nc_swap_nb u w x, gset_swap_fset x u w] at hh
    unfold degree
    omega
  have hA : ∀ z ∈ fset H x u w, degree H x u w z ≤ 1 + ((gset H u w x).erase v).card := by
    intro z hz
    have hzm : z ∈ gset H x w u := by rw [gset_swap_fset x u w]; exact hz
    have hh := Au_degree_cap (v := v) hzm
    change degree H x w u z ≤ _ at hh
    rw [degree_swap x u w, RU, fset_swap_gset u w x, tset_swap u w x, hB, add_zero] at hh
    exact hh
  have hc := card_grp_eq (H := H) u w x
  rw [hxB, hB] at hc
  push_cast at hc
  have he := card_erase_add_one hvB
  have he' : (((gset H u w x).erase v).card : ℚ) + 1 = (gset H u w x).card := by exact_mod_cast he
  have hdeg := codeg_eq_one_add_card_grp (triple_rot h.xuw) h.uniform
  rw [pair_comm w x] at hdeg
  have hheavy' : (3 : ℚ) ≤ codeg H {x,w} := by exact_mod_cast hheavy
  have hki : 1 ≤ ((gset H u w x).erase v).card + (iset H u w x).card := by
    have hki' : (1 : ℚ) ≤ (((gset H u w x).erase v).card : ℚ) + (iset H u w x).card := by linarith
    exact_mod_cast hki'
  have hnum := heavy_group_numeric (fset H x u w).card ((gset H u w x).erase v).card
    (iset H u w x).card hki
  have hvc := WBox.slotCost_antitone hvdeg
  have hwc := WBox.sum_cost_cap ((gset H u w x).erase v) (degree H u w x) (fset H x u w).card hW
  have hac := WBox.sum_cost_cap (fset H x u w) (degree H x u w) (1 + ((gset H u w x).erase v).card) hA
  simp only [cost_degree] at hvc hwc hac
  have hcost : WBox.gW (fset H x u w).card (1 + ((gset H u w x).erase v).card) ≤
      slotCost H u w x v + (∑ z ∈ (gset H u w x).erase v, slotCost H u w x z) +
        (∑ z ∈ fset H x u w, slotCost H x u w z) := by
    unfold WBox.gW
    unfold WBox.slotCost at hvc
    push_cast at hvc hac ⊢
    ring_nf at hvc hwc hac ⊢
    linarith
  have hden : (2 : ℚ) + ((gset H u w x).erase v).card + (iset H u w x).card =
      1 + (grp H u w x).card := by linarith
  rw [hden] at hnum
  have hsum := sum_erase_add (gset H u w x) (slotCost H u w x) hvB
  unfold wBase groupSigma
  linarith

/-- S11 and the no-cross one-group branch, in the actual anchor slot model. -/
theorem hW_nonneg (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hheavy : 3 ≤ codeg H {x,w})
    (hB : (tset H u w x).card = 0) (hC : (tset H w x u).card = 0) : 0 ≤ hW H x u w := by
  by_cases hxC : 1 ≤ (gset H w x u).card
  · exact hW_nonneg_cross h hcard hB hC hxC
  · have hzC : (gset H w x u).card = 0 := by omega
    have hzB : (fset H u w x).card = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hc := cross_degree_cap hz
      have hp := (mem_filter.mp hz).2.1
      omega
    have hb := wBase_no_cross h hcard hheavy hB hzB
    unfold hW
    rw [card_eq_zero.mp hzB, card_eq_zero.mp hzC, hB, hC]
    simp only [sum_empty, Nat.cast_zero, add_zero, zero_div]
    linarith

end Erdos643R3.AnchorNoType2
