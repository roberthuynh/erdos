import Openmath.Erdos643R3.AnchorViewSwap
import Openmath.Erdos643R3.L1Top
set_option autoImplicit false
namespace Erdos643R3.AnchorCaps
open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.WeightingBound Erdos643R3.SlotModel
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
variable {x y u v w : V}

/-- T1 is viewed as (x,v,u), so its light-pair group consists only of w. -/
theorem T1_C (h : Host H x y u v w) : grp H u x v = {w} := by
  unfold grp
  rw [h.light]
  simp [h.uw]

theorem T1_w_C_nc (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    nc H u x v w = {y} := by
  ext s
  constructor
  · intro hs
    obtain ⟨hsA,hws,hvws⟩ := mem_nc.mp hs
    obtain ⟨hsx,hsv,hsu,hsuv⟩ := mem_grp.mp hsA
    have hsPQ : s ∈ link H {u,v} ∩ link H {v,w} := by
      apply mem_inter.mpr
      constructor
      · apply mem_link.mpr
        refine ⟨by simp [hsu,hsv],?_⟩
        rw [show insert s ({u,v} : Finset V) = {s,v,u} from triple_perm (fun t => by tauto)]
        exact hsuv
      · apply mem_link.mpr
        have hsw : s ≠ w := hws.symm
        refine ⟨by simp [hsv,hsw],?_⟩
        rw [show insert s ({v,w} : Finset V) = {v,w,s} from triple_perm (fun t => by tauto)]
        exact hvws
    rw [base_link_inter h hcard] at hsPQ
    simp only [mem_insert,mem_singleton] at hsPQ
    exact mem_singleton.mpr (hsPQ.resolve_left hsx)
  · intro hs
    have : s = y := mem_singleton.mp hs
    subst s
    apply mem_nc.mpr
    refine ⟨mem_grp.mpr ⟨h.xy.symm,h.yv,h.yu,?_⟩,h.yw.symm,?_⟩
    · rw [show ({y,v,u} : Finset V) = {y,u,v} from triple_perm (fun t => by tauto)]
      exact h.yuv
    · rw [show ({v,w,y} : Finset V) = {y,v,w} from triple_perm (fun t => by tauto)]
      exact h.yvw

theorem T1_w_C_nb (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    nb H u x v w = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨hsB,hsw,hxsw⟩ := mem_nb.mp hs
  obtain ⟨hsv,hsu,hsx,hsux⟩ := mem_grp.mp hsB
  have hsXu : s ∈ link H {x,u} := by
    apply mem_link.mpr
    refine ⟨by simp [hsx,hsu],?_⟩
    rw [show insert s ({x,u} : Finset V) = {s,u,x} from triple_perm (fun t => by tauto)]
    exact hsux
  have hsXw : s ∈ link H {x,w} := by
    apply mem_link.mpr
    refine ⟨by simp [hsx,hsw],?_⟩
    rw [show insert s ({x,w} : Finset V) = {x,s,w} from triple_perm (fun t => by tauto)]
    exact hxsw
  have hsint := mem_inter.mpr ⟨hsXu,hsXw⟩
  rw [heavy_link_inter h hcard] at hsint
  exact hsv (mem_singleton.mp hsint)

theorem T1_y_neighbours (h : Host H x y u v w) :
    nb H x v u y = {w} ∧ nc H x v u y = {w} := by
  have hyA : y ∈ grp H x v u := by
    apply mem_grp.mpr
    refine ⟨h.xy.symm,h.yv,h.yu,?_⟩
    rw [show ({y,v,u} : Finset V) = {y,u,v} from triple_perm (fun t => by tauto)]
    exact h.yuv
  have hwC : w ∈ grp H u x v := by rw [T1_C h]; simp
  have hwB : w ∈ grp H v u x := by
    apply mem_grp.mpr
    refine ⟨h.vw.symm,h.uw.symm,h.xw.symm,?_⟩
    rw [show ({w,u,x} : Finset V) = {x,u,w} from triple_perm (fun t => by tauto)]
    exact h.xuw
  have hb : w ∈ nb H x v u y := by
    apply mem_nb.mpr
    refine ⟨hwC,h.yw.symm,?_⟩
    rw [show ({v,w,y} : Finset V) = {y,v,w} from triple_perm (fun t => by tauto)]
    exact h.yvw
  have hc : w ∈ nc H x v u y := by
    apply mem_nc.mpr
    refine ⟨hwB,h.yw,?_⟩
    rw [show ({u,y,w} : Finset V) = {y,u,w} from triple_perm (fun t => by tauto)]
    exact h.yuw
  have hT : ({x,v,u} : Finset V) ∈ H := by
    rw [show ({x,v,u} : Finset V) = {x,u,v} from triple_perm (fun t => by tauto)]
    exact h.xuv
  obtain ⟨s,hs,ht⟩ := lemma2 hT h.uniform h.avoiding hyA ⟨w,hb⟩ ⟨w,hc⟩
  have hsw : w = s := by simpa [hs] using hb
  simpa [← hsw] using And.intro hs ht

/-- Exact charge decomposition preceding S3; no final inequality or degree cap is assumed. -/
theorem T1_charge_decomposition (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    L1Top.charge H {x,u,v} + 13/12 =
      groupSigma H x v u + groupSigma H v u x +
      (∑ z ∈ (grp H x v u).erase y, slotCost H x v u z) +
      (∑ s ∈ grp H v u x, slotCost H v u x s) := by
  have hT : ({x,v,u} : Finset V) ∈ H := by
    rw [show ({x,v,u} : Finset V) = {x,u,v} from triple_perm (fun t => by tauto)]
    exact h.xuv
  have hsy := T1_y_neighbours h
  have hyA : y ∈ grp H x v u := by
    have hy : w ∈ nb H x v u y := by rw [hsy.1]; simp
    have hyuv := h.yuv
    apply mem_grp.mpr
    refine ⟨h.xy.symm,h.yv,h.yu,?_⟩
    rw [show ({y,v,u} : Finset V) = {y,u,v} from triple_perm (fun t => by tauto)]
    exact hyuv
  have hcY : slotCost H x v u y = 1/6 := by
    unfold slotCost
    rw [hsy.1,hsy.2]
    norm_num
  have hcW : slotCost H u x v w = 1/4 := by
    unfold slotCost
    rw [T1_w_C_nb h hcard,T1_w_C_nc h hcard]
    norm_num
  have hsigC : groupSigma H u x v = 1/2 := by
    unfold groupSigma
    rw [T1_C h]
    norm_num
  have hsig := sigmaW_slots hT h.uniform
  have htau := tauW_slots hT h.uniform h.avoiding
  rw [show ({x,v,u} : Finset V) = {x,u,v} from triple_perm (fun t => by tauto)] at hsig htau
  have hsum : (∑ z ∈ (grp H x v u).erase y, slotCost H x v u z) +
      slotCost H x v u y = ∑ z ∈ grp H x v u, slotCost H x v u z :=
    sum_erase_add _ _ hyA
  rw [T1_C h,sum_singleton,hcW] at htau
  unfold L1Top.charge
  rw [hsig,htau,hsigC]
  linarith [hsum]

end Erdos643R3.AnchorCaps
