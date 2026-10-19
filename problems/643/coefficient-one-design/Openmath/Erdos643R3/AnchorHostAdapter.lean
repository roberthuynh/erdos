import Openmath.Erdos643R3.AnchorCaps
set_option autoImplicit false
namespace Erdos643R3.AnchorCaps
open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.WeightingBound Erdos643R3.SlotModel
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
variable {x y u v w : V}

/-- Raw host data follow from the original labelled triangular common link and light-pair link. -/
theorem Host.of_bicone (hH : Uniform H) (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hxy : x ≠ y) (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V)))
    (hl : link H {x,v} = {u,w}) : Host H x y u v w := by
  have huv : ({u,v} : Finset V) ∈ CN H {x,y} := by rw [hCN]; simp
  have hvw : ({v,w} : Finset V) ∈ CN H {x,y} := by rw [hCN]; simp
  have huw : ({u,w} : Finset V) ∈ CN H {x,y} := by rw [hCN]; simp
  have hxuv := (mem_CN_pair.mp huv).2.2.1
  have hxvw := (mem_CN_pair.mp hvw).2.2.1
  have hxuw := (mem_CN_pair.mp huw).2.2.1
  have hyuv := (mem_CN_pair.mp huv).2.2.2
  have hyvw := (mem_CN_pair.mp hvw).2.2.2
  have hyuw := (mem_CN_pair.mp huw).2.2.2
  obtain ⟨hxu,hxv,huv'⟩ := triple_ne (hH _ hxuv)
  obtain ⟨-,hxw,hvw'⟩ := triple_ne (hH _ hxvw)
  obtain ⟨-,-,huw'⟩ := triple_ne (hH _ hxuw)
  obtain ⟨hyu,hyv,-⟩ := triple_ne (hH _ hyuv)
  obtain ⟨-,hyw,-⟩ := triple_ne (hH _ hyvw)
  exact ⟨hH,hav,hxy,hxu,hxv,hxw,hyu,hyv,hyw,huv',huw',hvw',
    hxuv,hxvw,hxuw,hyuv,hyvw,hyuw,hl⟩

/-- Conversely, avoidance makes the six labelled host edges an exact triangular common link. -/
theorem Host.CN_xy (h : Host H x y u v w) :
    CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V)) := by
  rw [CN_slot_eq h.xuw h.uniform h.avoiding (y_group h),
    (y_neighbours h).1,(y_neighbours h).2,image_singleton,image_singleton]
  ext P
  simp only [mem_insert,mem_union,mem_singleton]
  rw [pair_comm w v]
  tauto

end Erdos643R3.AnchorCaps
