import Openmath.Erdos643R3.AnchorViewSwap
import Openmath.Erdos643R3.WCost

set_option autoImplicit false
open scoped BigOperators
namespace Erdos643R3.AnchorW
open Finset
open Erdos643R3.Identity Erdos643R3.SlotModel Erdos643R3.AnchorCaps
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

def degree (H : Finset (Finset V)) (a b c z : V) : ℕ :=
  (nb H a b c z).card + (nc H a b c z).card

theorem degree_swap (a b c z : V) : degree H a c b z = degree H a b c z := by
  unfold degree
  rw [nb_swap_nc a b c z, nc_swap_nb a b c z]
  omega

theorem cost_degree (a b c z : V) : WBox.slotCost (degree H a b c z) = slotCost H a b c z := by
  unfold WBox.slotCost degree slotCost
  push_cast
  congr 2
  ring

variable {x y u v w : V}

/-- The concrete cross-slot estimate in Lemma W. All caps are derived from H. -/
theorem cross_threshold (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hmass : 1 ≤ (tset H w x u).card + (tset H u w x).card) :
    WBox.tauW (tset H w x u).card (tset H u w x).card false ≤
      WBox.betaW ((fset H u w x).card + (tset H u w x).card) (tset H u w x).card +
      (∑ z ∈ fset H u w x, slotCost H u w x z) +
      (∑ z ∈ gset H w x u, slotCost H w x u z) +
      (((tset H w x u).card : ℚ) + (tset H u w x).card) / 6 - 11 / 12 := by
  have hmirror := h.mirror
  have hcardm : (CN H {w,u}).card = 2 := by rw [pair_comm w u]; exact hcard
  have hB : ∀ z ∈ fset H u w x, 1 ≤ degree H u w x z := by
    intro z hz
    have hp := (mem_filter.mp hz).2.1
    unfold degree
    omega
  have hC : ∀ z ∈ gset H w x u, 1 ≤ degree H w x u z := by
    intro z hz
    have hp := (mem_filter.mp hz).2.1
    unfold degree
    omega
  have hcapB : ∀ z ∈ fset H u w x, degree H u w x z ≤
      (gset H w x u).card + (tset H w x u).card := by
    intro z hz
    exact cross_degree_cap hz
  have hcapC : ∀ z ∈ gset H w x u, degree H w x u z ≤
      (fset H u w x).card + (tset H u w x).card := by
    intro z hz
    have hzm : z ∈ fset H w u x := by rw [fset_swap_gset w x u]; exact hz
    have hc := cross_degree_cap hzm
    change degree H w u x z ≤ _ at hc
    rwa [degree_swap w x u, gset_swap_fset u w x, tset_swap u w x] at hc
  have hstarB : 1 ≤ (tset H w x u).card → ∃ p ∈ fset H u w x,
      ∀ z ∈ fset H u w x, z ≠ p → degree H u w x z ≤ (gset H w x u).card := by
    intro hm
    obtain ⟨p,hp,ho,-⟩ := host_cross_caps h hcard (card_pos.mp hm)
    exact ⟨p,hp,ho⟩
  have hstarC : 1 ≤ (tset H u w x).card → ∃ p ∈ gset H w x u,
      ∀ z ∈ gset H w x u, z ≠ p → degree H w x u z ≤ (fset H u w x).card := by
    intro hm
    have hnon : (tset H u x w).Nonempty := by rw [tset_swap u w x]; exact card_pos.mp hm
    obtain ⟨p,hp,ho,-⟩ := host_cross_caps hmirror hcardm hnon
    rw [fset_swap_gset w x u] at hp
    refine ⟨p,hp,?_⟩
    intro z hz hzp
    have hzm : z ∈ fset H w u x := by rw [fset_swap_gset w x u]; exact hz
    have hh := ho z hzm hzp
    change degree H w u x z ≤ _ at hh
    rwa [degree_swap w x u, gset_swap_fset u w x] at hh
  have hh := WBox.threshold_le_finite_costs (fset H u w x) (gset H w x u)
    (degree H u w x) (degree H w x u) (tset H w x u).card (tset H u w x).card
    hmass hB hC hcapB hcapC hstarB hstarC
  simpa only [cost_degree] using hh

/-- The R_w part of the host anchor; the isolated slots are charged at 1/2. -/
def wBase (H : Finset (Finset V)) (x u w : V) : ℚ :=
  groupSigma H u w x + (∑ z ∈ gset H u w x, slotCost H u w x z) +
    (∑ z ∈ fset H x u w, slotCost H x u w z) + ((iset H u w x).card : ℚ) / 2

theorem beta_le_wBase (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    WBox.betaW ((fset H u w x).card + (tset H u w x).card) (tset H u w x).card ≤
      wBase H x u w := by
  have hmirror := h.mirror
  have hcardm : (CN H {w,u}).card = 2 := by rw [pair_comm w u]; exact hcard
  have hvB : v ∈ gset H u w x := by
    have hv := v_type1_C hmirror
    rwa [fset_swap_gset u w x] at hv
  have hvdeg : degree H u w x v ≤ 1 + (fset H x u w).card := by
    have hv := v_degree_C_le_Au hmirror hcardm
    change degree H u x w v ≤ _ at hv
    rwa [degree_swap u w x, gset_swap_fset x u w] at hv
  have hW : ∀ z ∈ (gset H u w x).erase v, degree H u w x z ≤ (fset H x u w).card := by
    intro z hz
    obtain ⟨hzv,hzB⟩ := mem_erase.mp hz
    obtain ⟨hzgrp,-,hzero⟩ := mem_filter.mp hzB
    have hzgrpm : z ∈ grp H u x w := by rw [grp_swap u w x]; exact hzgrp
    have hh := Ru_degree_cap hmirror hcardm hzgrpm hzv
    rw [nc_swap_nb u w x, gset_swap_fset x u w] at hh
    unfold degree
    omega
  have hA : ∀ z ∈ fset H x u w, degree H x u w z ≤
      1 + ((gset H u w x).erase v).card + (tset H u w x).card := by
    intro z hz
    have hzm : z ∈ gset H x w u := by rw [gset_swap_fset x u w]; exact hz
    have hh := Au_degree_cap (v := v) hzm
    change degree H x w u z ≤ _ at hh
    rwa [degree_swap x u w, RU, fset_swap_gset u w x, tset_swap u w x] at hh
  have hstar : 1 ≤ (tset H u w x).card → ∃ p ∈ fset H x u w,
      ∀ z ∈ fset H x u w, z ≠ p → degree H x u w z ≤ 1 + ((gset H u w x).erase v).card := by
    intro hm
    have hnon : (tset H u x w).Nonempty := by rw [tset_swap u w x]; exact card_pos.mp hm
    obtain ⟨p,hp,ho,-⟩ := host_Au_caps hmirror hcardm hnon
    rw [gset_swap_fset x u w] at hp
    refine ⟨p,hp,?_⟩
    intro z hz hzp
    have hzm : z ∈ gset H x w u := by rw [gset_swap_fset x u w]; exact hz
    have hh := ho z hzm hzp
    change degree H x w u z ≤ _ at hh
    rwa [degree_swap x u w, RU, fset_swap_gset u w x] at hh
  have hb := WBox.betaW_le_finite_costs ((gset H u w x).erase v) (fset H x u w)
    (degree H u w x) (degree H x u w) (degree H u w x v)
    ((fset H u w x).card + (tset H u w x).card) (tset H u w x).card (iset H u w x).card
    hvdeg hW hA hstar
  simp only [cost_degree] at hb
  have hsum := sum_erase_add (gset H u w x) (slotCost H u w x) hvB
  have hc := card_grp_eq (H := H) u w x
  have he := card_erase_add_one hvB
  have he' : (((gset H u w x).erase v).card : ℚ) + 1 = (gset H u w x).card := by
    exact_mod_cast he
  have hden : (2 : ℚ) + ((gset H u w x).erase v).card +
      (((fset H u w x).card + (tset H u w x).card : ℕ) : ℚ) + (iset H u w x).card =
      1 + (grp H u w x).card := by
    push_cast
    linarith
  rw [hden] at hb
  unfold wBase groupSigma
  linarith

/-- Lemma W for the original host slot functions. The CN cardinality hypothesis
is exactly S1(a), obtained from G1(iii) at a deficient bicone triple. -/
theorem lemmaW (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hmass : 1 ≤ (tset H w x u).card + (tset H u w x).card) :
    WBox.tauW (tset H w x u).card (tset H u w x).card false ≤
      wBase H x u w + (∑ z ∈ fset H u w x, slotCost H u w x z) +
      (∑ z ∈ gset H w x u, slotCost H w x u z) +
      (((tset H w x u).card : ℚ) + (tset H u w x).card) / 6 - 11 / 12 := by
  have hx := cross_threshold h hcard hmass
  have hb := beta_le_wBase h hcard
  linarith

end Erdos643R3.AnchorW
