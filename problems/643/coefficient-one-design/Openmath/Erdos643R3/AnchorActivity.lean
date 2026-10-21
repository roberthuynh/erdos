import Openmath.Erdos643R3.AnchorCaps
import Openmath.Erdos643R3.G1BiconeAdapter

set_option autoImplicit false
namespace Erdos643R3.AnchorActivity
open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.WeightingBound
  Erdos643R3.SlotModel Erdos643R3.Lemma1g Erdos643R3.L1Top
  Erdos643R3.AnchorCaps
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

/-- Three different apices sharing two triangle sides give three common-link pairs. -/
theorem three_pairs_le {a b c x y z : V} (hH : Uniform H)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (he : ∀ t ∈ ({x,y,z} : Finset V), ({t,a,b} : Finset V) ∈ H ∧ ({t,a,c} : Finset V) ∈ H) :
    3 ≤ (CN H {b,c}).card := by
  have hp : ∀ t ∈ ({x,y,z} : Finset V), ({t,a} : Finset V) ∈ CN H {b,c} := by
    intro t ht
    obtain ⟨hb,hc⟩ := he t ht
    obtain ⟨hta,htb,hab⟩ := triple_ne (hH _ hb)
    obtain ⟨-,htc,hac⟩ := triple_ne (hH _ hc)
    apply pair_mem_CN hta htb htc hab hac
    · convert hb using 1 <;> ext s <;> simp only [mem_insert,mem_singleton] <;> tauto
    · convert hc using 1 <;> ext s <;> simp only [mem_insert,mem_singleton] <;> tauto
  have hinj : Set.InjOn (fun t => ({t,a} : Finset V)) ({x,y,z} : Finset V) := by
    intro t ht s hs heq
    have hta := (triple_ne (hH _ (he t ht).1)).1
    have hmem : t ∈ ({s,a} : Finset V) := by
      change ({t,a} : Finset V) = {s,a} at heq
      rw [← heq]; simp
    simpa [hta] using hmem
  have hs : ({x,y,z} : Finset V).image (fun t => ({t,a} : Finset V)) ⊆ CN H {b,c} := by
    intro P hP
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hP
    exact hp t ht
  have hc := card_le_card hs
  rw [card_image_of_injOn hinj] at hc
  simpa [hxy,hxz,hyz] using hc

/-- G1 rules out deficiency when a triangle has a third apex. -/
theorem third_apex_not_deficient {x y z a b c : V} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hCN : CN H {x,y} = ({{a,b},{b,c},{a,c}} : Finset (Finset V)))
    (hza : ({z,a,b} : Finset V) ∈ H) (hzb : ({z,b,c} : Finset V) ∈ H)
    (hzc : ({z,a,c} : Finset V) ∈ H) : ¬ Deficient H {x,a,b} := by
  intro hd
  have hg := G1BiconeAdapter.deficient_geometric hH hav hxy hCN hd
  have he : ∀ t ∈ ({x,y,z} : Finset V),
      ({t,a,b} : Finset V) ∈ H ∧ ({t,b,c} : Finset V) ∈ H ∧ ({t,a,c} : Finset V) ∈ H := by
    have hab : ({a,b} : Finset V) ∈ CN H {x,y} := by rw [hCN]; simp
    have hbc : ({b,c} : Finset V) ∈ CN H {x,y} := by rw [hCN]; simp
    have hac : ({a,c} : Finset V) ∈ CN H {x,y} := by rw [hCN]; simp
    intro t ht
    simp only [mem_insert,mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨(mem_CN_pair.mp hab).2.2.1,(mem_CN_pair.mp hbc).2.2.1,(mem_CN_pair.mp hac).2.2.1⟩
    · exact ⟨(mem_CN_pair.mp hab).2.2.2,(mem_CN_pair.mp hbc).2.2.2,(mem_CN_pair.mp hac).2.2.2⟩
    · exact ⟨hza,hzb,hzc⟩
  have hbc : 3 ≤ (CN H {b,c}).card := three_pairs_le hH hxy hxz hyz (fun t ht => ⟨(he t ht).1,(he t ht).2.2⟩)
  have hac : 3 ≤ (CN H {a,c}).card := by
    apply three_pairs_le hH hxy hxz hyz
    intro t ht
    refine ⟨?_,(he t ht).2.1⟩
    convert (he t ht).1 using 1 <;> ext s <;> simp only [mem_insert,mem_singleton] <;> tauto
  by_cases hl : codeg H {x,a} = 2
  · have := (hg.2.1 hl).2
    omega
  · have := (hg.2.2 (hg.1.mpr hl)).2
    omega

/-- A bicone over a triangle with a third apex is inactive, on all six members. -/
theorem third_apex_not_active {x y z a b c : V} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hCN : CN H {x,y} = ({{a,b},{b,c},{a,c}} : Finset (Finset V)))
    (hza : ({z,a,b} : Finset V) ∈ H) (hzb : ({z,b,c} : Finset V) ∈ H)
    (hzc : ({z,a,c} : Finset V) ∈ H) : ¬ Active H {x,y} := by
  have hrot : CN H {x,y} = ({{b,c},{c,a},{b,a}} : Finset (Finset V)) := by
    rw [hCN]; ext P; simp only [mem_insert,mem_singleton,pair_comm c a,pair_comm b a]; tauto
  have hswap : CN H {x,y} = ({{a,c},{c,b},{a,b}} : Finset (Finset V)) := by
    rw [hCN]; ext P; simp only [mem_insert,mem_singleton,pair_comm c b]; tauto
  have hzba : ({z,b,a} : Finset V) ∈ H := by
    convert hza using 1 <;> ext t <;> simp only [mem_insert,mem_singleton] <;> tauto
  have hzca : ({z,c,a} : Finset V) ∈ H := by
    convert hzc using 1 <;> ext t <;> simp only [mem_insert,mem_singleton] <;> tauto
  have hzcb : ({z,c,b} : Finset V) ∈ H := by
    convert hzb using 1 <;> ext t <;> simp only [mem_insert,mem_singleton] <;> tauto
  rintro ⟨-,T,hT,hd⟩
  rw [bicone_of_CN_eq hCN] at hT
  simp only [mem_insert,mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl
  · exact third_apex_not_deficient hH hav hxy hxz hyz hCN hza hzb hzc hd
  · exact third_apex_not_deficient hH hav hxy hxz hyz hrot hzb hzca hzba hd
  · exact third_apex_not_deficient hH hav hxy hxz hyz hswap hzc hzcb hza hd
  · exact third_apex_not_deficient hH hav hxy.symm hyz hxz (by rwa [pair_comm y x]) hza hzb hzc hd
  · exact third_apex_not_deficient hH hav hxy.symm hyz hxz (by rwa [pair_comm y x]) hzb hzca hzba hd
  · exact third_apex_not_deficient hH hav hxy.symm hyz hxz (by rwa [pair_comm y x]) hzc hzcb hza hd

/-- S8(b): two type-2 slots in C force every associated bicone to be inactive. -/
theorem type2_C_not_active {x y u v w r : V} (h : Host H x y u v w)
    (hcard : (CN H {u,w}).card = 2) (hm : 2 ≤ (tset H w x u).card)
    (hr : r ∈ tset H w x u) : ¬ Active H {w,r} := by
  obtain ⟨p,-,-,hpnot,hp⟩ := shared_partner_C h hcard ⟨r,hr⟩
  obtain ⟨s,hs,hsr⟩ := exists_mem_ne (by omega : 1 < (tset H w x u).card) r
  have hrC := (mem_filter.mp hr).1
  have hsC := (mem_filter.mp hs).1
  have hrw := (mem_grp.mp hrC).1
  have hsw := (mem_grp.mp hsC).1
  have hsxu := (mem_grp.mp hsC).2.2.2
  have hspb : p ∈ nb H w x u s := by simp [(hp s hs).1]
  have hspc : p ∈ nc H w x u s := by simp [(hp s hs).2]
  have hsxp := (mem_nb.mp hspb).2.2
  have hsup := (mem_nc.mp hspc).2.2
  have hT : ({w,x,u} : Finset V) ∈ H := by
    convert h.xuw using 1 <;> ext t <;> simp only [mem_insert,mem_singleton] <;> tauto
  have hCN := CN_type2 hT h.uniform h.avoiding hrC (hp r hr).1 (hp r hr).2
  apply third_apex_not_active h.uniform h.avoiding hrw.symm hsw.symm hsr.symm
  · rw [hCN]; ext P; simp only [mem_insert,mem_singleton]; tauto
  · exact hsxu
  · convert hsup using 1 <;> ext t <;> simp only [mem_insert,mem_singleton] <;> tauto
  · convert hsxp using 1 <;> ext t <;> simp only [mem_insert,mem_singleton] <;> tauto

/-- Type-2 slots do not depend on the order of the two opposite vertices. -/
theorem tset_swap {a b c : V} (hT : ({a,b,c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) : tset H a b c = tset H a c b := by
  have hT' : ({a,c,b} : Finset V) ∈ H := by
    convert hT using 1 <;> ext t <;> simp only [mem_insert,mem_singleton] <;> tauto
  have hgrp : grp H a b c = grp H a c b := by simp only [grp,pair_comm b c]
  ext z
  simp only [tset,mem_filter]
  constructor
  · rintro ⟨hz,hb,hc⟩
    have hz' : z ∈ grp H a c b := hgrp ▸ hz
    exact ⟨hz',(triangular_iff_type2 hT' hH hav hz').mp ((triangular_iff_type2 hT hH hav hz).mpr ⟨hb,hc⟩)⟩
  · rintro ⟨hz,hb,hc⟩
    have hz' : z ∈ grp H a b c := hgrp.symm ▸ hz
    exact ⟨hz',(triangular_iff_type2 hT hH hav hz').mp ((triangular_iff_type2 hT' hH hav hz).mpr ⟨hb,hc⟩)⟩

noncomputable def activeSlots (a b c : V) : Finset V :=
  (tset H a b c).filter (fun z => Active H {a,z})

/-- Counts genuine active bicones via their slot representatives. -/
theorem act_le_activeSlots {a b c : V} (hT : ({a,b,c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    act H {a,b,c} ≤ (activeSlots (H := H) a b c).card +
      (activeSlots (H := H) b c a).card + (activeSlots (H := H) c a b).card := by
  classical
  have hm {a b c z : V} (hT : ({a,b,c} : Finset V) ∈ H) (hz : z ∈ grp H a b c)
      (ha : Active H {a,z}) : z ∈ activeSlots (H := H) a b c := by
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hz,(triangular_iff_type2 hT hH hav hz).mp ha.1⟩,ha⟩
  let A := (activeSlots (H := H) a b c).image (fun z => ({a,z} : Finset V))
  let B := (activeSlots (H := H) b c a).image (fun z => ({b,z} : Finset V))
  let C := (activeSlots (H := H) c a b).image (fun z => ({c,z} : Finset V))
  have hsub : (activePairs H).filter (fun q => ({a,b,c} : Finset V) ∈ bicone H q) ⊆ A ∪ B ∪ C := by
    intro q hq
    obtain ⟨ha,hmem⟩ := mem_filter.mp hq
    have haq : Active H q := (mem_filter.mp ha).2
    have ho := (G1Bicone.mem_bicone_iff_option hT hH haq.1.1).mp hmem
    simp only [options,mem_union,mem_image] at ho
    rcases ho with (⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩) | ⟨z,hz,rfl⟩
    · exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨z,hm hT hz haq,rfl⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨z,hm (triple_rot hT) hz haq,rfl⟩))
    · exact mem_union_right _ (mem_image.mpr ⟨z,hm (triple_rot (triple_rot hT)) hz haq,rfl⟩)
  have h1 := card_le_card hsub
  have h2 := card_union_le (A ∪ B) C
  have h3 := card_union_le A B
  have hA := card_image_le (s := activeSlots (H := H) a b c) (f := fun z => ({a,z} : Finset V))
  have hB := card_image_le (s := activeSlots (H := H) b c a) (f := fun z => ({b,z} : Finset V))
  have hC := card_image_le (s := activeSlots (H := H) c a b) (f := fun z => ({c,z} : Finset V))
  change act H {a,b,c} ≤ (A ∪ B ∪ C).card at h1
  change A.card ≤ _ at hA
  change B.card ≤ _ at hB
  change C.card ≤ _ at hC
  omega

/-- A side contributes one active bicone only when it has exactly one type-2 slot. -/
theorem activeSlots_C_le {x y u v w : V} (h : Host H x y u v w)
    (hcard : (CN H {u,w}).card = 2) :
    (activeSlots (H := H) w x u).card ≤ if (tset H w x u).card = 1 then 1 else 0 := by
  classical
  have hle := card_le_card (filter_subset (fun r => Active H {w,r}) (tset H w x u))
  change (activeSlots (H := H) w x u).card ≤ (tset H w x u).card at hle
  split_ifs with hm
  · omega
  · have he : activeSlots (H := H) w x u = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨hr,ha⟩ := mem_filter.mp hr
      have hp : 0 < (tset H w x u).card := card_pos.mpr ⟨r,hr⟩
      exact type2_C_not_active h hcard (by omega) hr ha
    simp [he]

/-- S8(c), an upper bound on the actual activity of the host anchor. -/
theorem anchor_act_le {x y u v w : V} (h : Host H x y u v w)
    (hcard : (CN H {u,w}).card = 2) :
    act H {x,u,w} ≤ 1 + (if (tset H w x u).card = 1 then 1 else 0) +
      (if (tset H u w x).card = 1 then 1 else 0) := by
  classical
  have hle := act_le_activeSlots h.xuw h.uniform h.avoiding
  have hA := card_le_card (filter_subset (fun r => Active H {x,r}) (tset H x u w))
  change (activeSlots (H := H) x u w).card ≤ (tset H x u w).card at hA
  rw [only_type2_A h hcard,card_singleton] at hA
  have hC := activeSlots_C_le h hcard
  have hB := activeSlots_C_le h.mirror (by rwa [pair_comm w u])
  have hT : ({u,x,w} : Finset V) ∈ H := by
    convert h.xuw using 1 <;> ext t <;> simp only [mem_insert,mem_singleton] <;> tauto
  have he := tset_swap hT h.uniform h.avoiding
  have he' : activeSlots (H := H) u x w = activeSlots (H := H) u w x := by
    unfold activeSlots; rw [he]
  rw [he,he'] at hB
  omega

/-- The common-link cardinality required above follows from an actual deficient side. -/
theorem card_CN_uw_of_deficient {x y u v w : V} (h : Host H x y u v w)
    (hd : Deficient H {x,u,v}) : (CN H {u,w}).card = 2 := by
  have hCN := CN_type2 h.xuw h.uniform h.avoiding (y_group h)
    (y_neighbours h).1 (y_neighbours h).2
  have hCN' : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V)) := by
    rw [hCN]; ext P; simp only [mem_insert,mem_singleton,pair_comm w v]; tauto
  have hg := G1BiconeAdapter.deficient_geometric h.uniform h.avoiding h.xy hCN' hd
  have hl : codeg H {x,v} = 2 := by
    rw [codeg_eq_card_link h.uniform (card_pair h.xv),h.light,card_pair h.uw]
  exact (hg.2.2 hl).2

/-- Fully instantiated S8(c): no common-link or activity conclusion is assumed. -/
theorem anchor_act_le_of_deficient {x y u v w : V} (h : Host H x y u v w)
    (hd : Deficient H {x,u,v} ∨ Deficient H {x,v,w}) :
    act H {x,u,w} ≤ 1 + (if (tset H w x u).card = 1 then 1 else 0) +
      (if (tset H u w x).card = 1 then 1 else 0) := by
  apply anchor_act_le h
  rcases hd with hd | hd
  · exact card_CN_uw_of_deficient h hd
  · have hd' : Deficient H {x,w,v} := by
      convert hd using 1 <;> ext t <;> simp only [mem_insert,mem_singleton] <;> tauto
    have hc := card_CN_uw_of_deficient h.mirror hd'
    simpa only [pair_comm w u] using hc

end Erdos643R3.AnchorActivity
