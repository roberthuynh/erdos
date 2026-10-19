import Openmath.Erdos643R3.AnchorSide
import Openmath.Erdos643R3.AnchorNoType2
import Openmath.Erdos643R3.AnchorActivity

set_option autoImplicit false
namespace Erdos643R3.AnchorMargin
open Finset
open Erdos643R3.Identity Erdos643R3.SlotModel Erdos643R3.AnchorCaps
open Erdos643R3.AnchorW Erdos643R3.AnchorDecomposition Erdos643R3.AnchorSide
open Erdos643R3.AnchorAssemblyArith
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
variable {x y u v w : V}

/-- Every host with T1 deficient pays its T1 deficit strictly, including the
no-type2 branch. This is the one-deficient-side theorem. -/
theorem single_margin_host (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hu : 3 ≤ codeg H {x,u}) (hw : 3 ≤ codeg H {x,w})
    (hd : L1Top.Deficient H {x,u,v}) :
    groupSigma H x u w < L1Top.charge H {x,u,w} -
      (L1Top.act H {x,u,w} : ℚ) * L1Top.deficit H {x,u,v} := by
  have hU := gU_gt_threshold h hcard hu hd
  have hWb : WBox.tauW (tset H w x u).card (tset H u w x).card false ≤ hW H x u w := by
    by_cases hm : 1 ≤ (tset H w x u).card + (tset H u w x).card
    · exact hW_ge_tau h hcard hm
    · have hB : (tset H u w x).card = 0 := by omega
      have hC : (tset H w x u).card = 0 := by omega
      have hh := AnchorNoType2.hW_nonneg h hcard hw hB hC
      simpa [hB,hC,WBox.tauW] using hh
  have hD0 : 0 ≤ L1Top.deficit H {x,u,v} := by
    unfold L1Top.Deficient at hd
    unfold L1Top.deficit
    linarith
  have hD := deficit_le_twelfth h
  have ha := AnchorActivity.anchor_act_le h hcard
  have hm := single_margin (L1Top.act H {x,u,w}) (tset H w x u).card (tset H u w x).card
    (L1Top.deficit H {x,u,v}) (gU H x u v w) (hW H x u w) hD0 hD ha hU hWb
  have heq := charge_minus_deficit h hcard
  have hi : (0 : ℚ) ≤ (iset H x u w).card := Nat.cast_nonneg _
  linarith

/-- Every host with both T1 and T2 deficient pays their sum strictly. -/
theorem both_margin_host (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hu : 3 ≤ codeg H {x,u}) (hw : 3 ≤ codeg H {x,w})
    (hd : L1Top.Deficient H {x,u,v}) (he : L1Top.Deficient H {x,v,w}) :
    groupSigma H x u w < L1Top.charge H {x,u,w} - (L1Top.act H {x,u,w} : ℚ) *
      (L1Top.deficit H {x,u,v} + L1Top.deficit H {x,v,w}) := by
  have ht : ({x,w,v} : Finset V) = {x,v,w} := triple_perm (fun z => by tauto)
  have hcm : (CN H {w,u}).card = 2 := by rw [pair_comm w u]; exact hcard
  have hem : L1Top.Deficient H {x,w,v} := by rw [ht]; exact he
  have hU := side_s10 h hcard hu hd
  have hW := side_s10 h.mirror hcm hw hem
  rw [ht, tset_swap u w x] at hW
  have hD0 : 0 ≤ L1Top.deficit H {x,u,v} := by
    unfold L1Top.Deficient at hd
    unfold L1Top.deficit
    linarith
  have hE0 : 0 ≤ L1Top.deficit H {x,v,w} := by
    unfold L1Top.Deficient at he
    unfold L1Top.deficit
    linarith
  have hD := deficit_le_twelfth h
  have hE := deficit_le_twelfth h.mirror
  rw [ht] at hE
  have ha := AnchorActivity.anchor_act_le h hcard
  have hm := both_margin (L1Top.act H {x,u,w}) (tset H w x u).card (tset H u w x).card
    (L1Top.deficit H {x,u,v}) (L1Top.deficit H {x,v,w}) (uMinus H x u w) (uMinus H x w u)
    hD0 hE0 hD hE ha hU hW
  have hl := charge_lower_two_sides h hcard
  linarith

/-- Exhaustive local anchor theorem, retaining the actual deficient predicates
inside the sum instead of assuming either side's deficit is present. -/
theorem full_margin_host (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hu : 3 ≤ codeg H {x,u}) (hw : 3 ≤ codeg H {x,w})
    (hd : L1Top.Deficient H {x,u,v} ∨ L1Top.Deficient H {x,v,w}) :
    groupSigma H x u w < L1Top.charge H {x,u,w} - (L1Top.act H {x,u,w} : ℚ) *
      ((if L1Top.Deficient H {x,u,v} then L1Top.deficit H {x,u,v} else 0) +
       (if L1Top.Deficient H {x,v,w} then L1Top.deficit H {x,v,w} else 0)) := by
  classical
  by_cases hd1 : L1Top.Deficient H {x,u,v}
  · by_cases hd2 : L1Top.Deficient H {x,v,w}
    · simpa only [if_pos hd1, if_pos hd2] using both_margin_host h hcard hu hw hd1 hd2
    · simpa only [if_pos hd1, if_neg hd2, add_zero] using single_margin_host h hcard hu hw hd1
  · have hd2 := hd.resolve_left hd1
    have hT : ({x,w,v} : Finset V) = {x,v,w} := triple_perm (fun z => by tauto)
    have hA : ({x,w,u} : Finset V) = {x,u,w} := triple_perm (fun z => by tauto)
    have hd2m : L1Top.Deficient H {x,w,v} := by rw [hT]; exact hd2
    have hcm : (CN H {w,u}).card = 2 := by rw [pair_comm w u]; exact hcard
    have hm := single_margin_host h.mirror hcm hw hu hd2m
    rw [hT,hA] at hm
    have hs : groupSigma H x w u = groupSigma H x u w := by
      unfold groupSigma
      rw [grp_swap x u w]
    rw [hs] at hm
    simpa only [if_neg hd1, if_pos hd2, zero_add] using hm

end Erdos643R3.AnchorMargin
