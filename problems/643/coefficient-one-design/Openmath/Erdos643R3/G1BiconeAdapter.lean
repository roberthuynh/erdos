import Openmath.Erdos643R3.G1Main

set_option autoImplicit false
namespace Erdos643R3.G1BiconeAdapter
open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.WeightingBound
  Erdos643R3.SlotModel Erdos643R3.Lemma1g Erdos643R3.G1Combinatorics Erdos643R3.L1Top
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

/-- A labelled triangular common-link gives the actual type-2 slot and its partner. -/
theorem labelled_type2 {x y u v w : V} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hxy : x ≠ y)
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V))) :
    ({x,u,v} : Finset V) ∈ H ∧ y ∈ tset H x u v ∧
      nb H x u v y = {w} ∧ nc H x u v y = {w} := by
  have huv : ({u,v} : Finset V) ∈ CN H {x,y} := by rw [hCN]; simp
  have hvw : ({v,w} : Finset V) ∈ CN H {x,y} := by rw [hCN]; simp
  have huw : ({u,w} : Finset V) ∈ CN H {x,y} := by rw [hCN]; simp
  have hxuv := (mem_CN_pair.mp huv).2.2.1
  have hxvw := (mem_CN_pair.mp hvw).2.2.1
  have hxuw := (mem_CN_pair.mp huw).2.2.1
  have hyvw := (mem_CN_pair.mp hvw).2.2.2
  have hyuw := (mem_CN_pair.mp huw).2.2.2
  obtain ⟨hxu,hxv,-⟩ := triple_ne (hH _ hxuv)
  obtain ⟨-,hxw,huwne⟩ := triple_ne (hH _ hxuw)
  obtain ⟨-,-,hvwne⟩ := triple_ne (hH _ hxvw)
  obtain ⟨-,hyw,-⟩ := triple_ne (hH _ hyuw)
  have hyA : y ∈ grp H x u v := G1Bicone.slot_of_witness hxu hxv hxy.symm huv rfl
  have hwC : w ∈ grp H v x u := mem_grp.mpr ⟨hvwne.symm,hxw.symm,huwne.symm,by
    rwa [show ({w,x,u} : Finset V) = {x,u,w} from triple_perm (fun t => by tauto)]⟩
  have hwB : w ∈ grp H u v x := mem_grp.mpr ⟨huwne.symm,hvwne.symm,hxw.symm,by
    rwa [show ({w,v,x} : Finset V) = {x,v,w} from triple_perm (fun t => by tauto)]⟩
  have hwb : w ∈ nb H x u v y := mem_nb.mpr ⟨hwC,hyw.symm,by
    rwa [show ({u,w,y} : Finset V) = {y,u,w} from triple_perm (fun t => by tauto)]⟩
  have hwc : w ∈ nc H x u v y := mem_nc.mpr ⟨hwB,hyw,by
    rwa [show ({v,y,w} : Finset V) = {y,v,w} from triple_perm (fun t => by tauto)]⟩
  have hyT : y ∈ tset H x u v := mem_filter.mpr ⟨hyA,card_pos.mpr ⟨w,hwb⟩,card_pos.mpr ⟨w,hwc⟩⟩
  obtain ⟨w',hb,hc⟩ := lemma2 hxuv hH hav hyA ⟨w,hwb⟩ ⟨w,hwc⟩
  have he : w = w' := by rw [hb] at hwb; exact mem_singleton.mp hwb
  exact ⟨hxuv,hyT,by rwa [← he] at hb,by rwa [← he] at hc⟩

/-- Theorem G1 inside any labelled bicone, at the apex x and base pair uv. -/
theorem deficient_geometric {x y u v w : V} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hxy : x ≠ y)
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V)))
    (hd : Deficient H {x,u,v}) : GeometricG1 (H := H) x u v w := by
  obtain ⟨hT,hy,hb,hc⟩ := labelled_type2 hH hav hxy hCN
  apply G1Main.deficient_geometric hT hH hav _ hy hb hc
  unfold Deficient charge at hd
  linarith

end Erdos643R3.G1BiconeAdapter
