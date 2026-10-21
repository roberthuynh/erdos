import Openmath.Erdos643R3.AnchorW
import Openmath.Erdos643R3.L1Top

set_option autoImplicit false
open scoped BigOperators
namespace Erdos643R3.AnchorDecomposition
open Finset
open Erdos643R3.Identity Erdos643R3.SlotModel Erdos643R3.AnchorCaps Erdos643R3.AnchorW
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

theorem group_cost_split {a b c : V} (hT : ({a,b,c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    (∑ z ∈ grp H a b c, slotCost H a b c z) =
      ((iset H a b c).card : ℚ) / 2 + ((tset H a b c).card : ℚ) / 6 +
      (∑ z ∈ fset H a b c, slotCost H a b c z) + (∑ z ∈ gset H a b c, slotCost H a b c z) := by
  have hh := group_exact hT hH hav
  have hf : (∑ z ∈ fset H a b c, slotCost H a b c z) =
      ∑ z ∈ fset H a b c, 1 / (2 * (1 + ((nc H a b c z).card : ℚ))) := by
    apply sum_congr rfl
    intro z hz
    have hzero := (mem_filter.mp hz).2.2
    simp [slotCost, hzero]
  have hg : (∑ z ∈ gset H a b c, slotCost H a b c z) =
      ∑ z ∈ gset H a b c, 1 / (2 * (1 + ((nb H a b c z).card : ℚ))) := by
    apply sum_congr rfl
    intro z hz
    have hzero := (mem_filter.mp hz).2.2
    simp [slotCost, hzero]
  have hsig : groupSigma H a b c =
      1 / (1 + ((fset H a b c).card : ℚ) + (gset H a b c).card +
        (tset H a b c).card + (iset H a b c).card) := by
    unfold groupSigma
    rw [card_grp_eq]
    congr 1
    ring
  rw [← hf, ← hg, hsig] at hh
  linarith

def uMinus (H : Finset (Finset V)) (x u w : V) : ℚ :=
  groupSigma H w x u + (∑ z ∈ fset H w x u, slotCost H w x u z) +
    (∑ z ∈ gset H x u w, slotCost H x u w z)

def hW (H : Finset (Finset V)) (x u w : V) : ℚ :=
  wBase H x u w + (∑ z ∈ fset H u w x, slotCost H u w x z) +
    (∑ z ∈ gset H w x u, slotCost H w x u z) +
    (((tset H w x u).card : ℚ) + (tset H u w x).card) / 6 - 11 / 12

def gU (H : Finset (Finset V)) (x u v w : V) : ℚ :=
  uMinus H x u w + ((iset H w x u).card : ℚ) / 2 + L1Top.charge H {x,u,v} - 11 / 12

variable {x y u v w : V}

/-- S2 in the exact host slot model, grouped for the one-deficient-side case. -/
theorem charge_split (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    L1Top.charge H {x,u,w} = groupSigma H x u w + ((iset H x u w).card : ℚ) / 2 +
      uMinus H x u w + ((iset H w x u).card : ℚ) / 2 + hW H x u w - 11 / 12 := by
  have hA := group_cost_split h.xuw h.uniform h.avoiding
  have hB := group_cost_split (triple_rot h.xuw) h.uniform h.avoiding
  have hC := group_cost_split (triple_rot (triple_rot h.xuw)) h.uniform h.avoiding
  have ht := only_type2_A h hcard
  rw [ht, card_singleton] at hA
  have hsigma := sigmaW_slots h.xuw h.uniform
  have htau := tauW_slots h.xuw h.uniform h.avoiding
  unfold L1Top.charge
  rw [hsigma, htau, hA, hB, hC]
  unfold uMinus hW wBase
  push_cast
  ring

/-- Identity (1) of the one-deficient-side argument, with the actual charge,
actual active-bicone count, and actual deficit. No sign conclusion is assumed. -/
theorem charge_minus_deficit (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    L1Top.charge H {x,u,w} - (L1Top.act H {x,u,w} : ℚ) * L1Top.deficit H {x,u,v} =
      groupSigma H x u w + ((iset H x u w).card : ℚ) / 2 + gU H x u v w + hW H x u w -
      ((L1Top.act H {x,u,w} : ℚ) - 1) * L1Top.deficit H {x,u,v} := by
  rw [charge_split h hcard]
  unfold gU L1Top.deficit
  ring

theorem hW_ge_tau (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hmass : 1 ≤ (tset H w x u).card + (tset H u w x).card) :
    WBox.tauW (tset H w x u).card (tset H u w x).card false ≤ hW H x u w :=
  lemmaW h hcard hmass

theorem uMinus_mirror (x u w : V) :
    uMinus H x w u + ((iset H u w x).card : ℚ) / 2 = wBase H x u w := by
  unfold uMinus wBase groupSigma
  rw [grp_swap u w x, fset_swap_gset u w x, gset_swap_fset x u w]
  simp only [slotCost_swap u w x, slotCost_swap x u w]

theorem slotCost_nonneg (a b c z : V) : 0 ≤ slotCost H a b c z := by
  unfold slotCost
  positivity

/-- S2 with all nonnegative isolated and cross-slot terms discarded. -/
theorem charge_lower_two_sides (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    groupSigma H x u w +
      (1 + ((tset H w x u).card : ℚ) + (tset H u w x).card) / 6 +
      uMinus H x u w + uMinus H x w u - 2 ≤ L1Top.charge H {x,u,w} := by
  rw [charge_split h hcard]
  unfold hW
  rw [← uMinus_mirror]
  have hiA : (0 : ℚ) ≤ (iset H x u w).card := Nat.cast_nonneg _
  have hiB : (0 : ℚ) ≤ (iset H u w x).card := Nat.cast_nonneg _
  have hiC : (0 : ℚ) ≤ (iset H w x u).card := Nat.cast_nonneg _
  have hsumB : 0 ≤ ∑ z ∈ fset H u w x, slotCost H u w x z :=
    sum_nonneg (fun z _ => slotCost_nonneg u w x z)
  have hsumC : 0 ≤ ∑ z ∈ gset H w x u, slotCost H w x u z :=
    sum_nonneg (fun z _ => slotCost_nonneg w x u z)
  linarith

end Erdos643R3.AnchorDecomposition
