import Openmath.Erdos643R3.SlotModel

/-! Concrete host structural lemmas for the both-heavy anchor in setting S.
All neighbour sets are the existing `SlotModel` sets; no cap is postulated. -/
set_option autoImplicit false
namespace Erdos643R3.AnchorCaps
open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.WeightingBound
open Erdos643R3.SlotModel
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

/-- Host data only: six bicone edges and the light-pair link. -/
structure Host (H : Finset (Finset V)) (x y u v w : V) : Prop where
  uniform : Uniform H
  avoiding : ¬ Erdos643.HypergraphBasics.Forbidden H
  xy : x ≠ y
  xu : x ≠ u
  xv : x ≠ v
  xw : x ≠ w
  yu : y ≠ u
  yv : y ≠ v
  yw : y ≠ w
  uv : u ≠ v
  uw : u ≠ w
  vw : v ≠ w
  xuv : ({x,u,v} : Finset V) ∈ H
  xvw : ({x,v,w} : Finset V) ∈ H
  xuw : ({x,u,w} : Finset V) ∈ H
  yuv : ({y,u,v} : Finset V) ∈ H
  yvw : ({y,v,w} : Finset V) ∈ H
  yuw : ({y,u,w} : Finset V) ∈ H
  light : link H {x,v} = {u,w}

variable {x y u v w : V}

/-- Interchanging the two heavy sides preserves the exact host setting. -/
theorem Host.mirror (h : Host H x y u v w) : Host H x y w v u where
  uniform := h.uniform
  avoiding := h.avoiding
  xy := h.xy
  xu := h.xw
  xv := h.xv
  xw := h.xu
  yu := h.yw
  yv := h.yv
  yw := h.yu
  uv := h.vw.symm
  uw := h.uw.symm
  vw := h.uv.symm
  xuv := by
    rw [show ({x,w,v} : Finset V) = {x,v,w} from triple_perm (fun t => by tauto)]
    exact h.xvw
  xvw := by
    rw [show ({x,v,u} : Finset V) = {x,u,v} from triple_perm (fun t => by tauto)]
    exact h.xuv
  xuw := by
    rw [show ({x,w,u} : Finset V) = {x,u,w} from triple_perm (fun t => by tauto)]
    exact h.xuw
  yuv := by
    rw [show ({y,w,v} : Finset V) = {y,v,w} from triple_perm (fun t => by tauto)]
    exact h.yvw
  yvw := by
    rw [show ({y,v,u} : Finset V) = {y,u,v} from triple_perm (fun t => by tauto)]
    exact h.yuv
  yuw := by
    rw [show ({y,w,u} : Finset V) = {y,u,w} from triple_perm (fun t => by tauto)]
    exact h.yuw
  light := by rw [pair_comm w u]; exact h.light

lemma y_group (h : Host H x y u v w) : y ∈ grp H x u w :=
  mem_grp.mpr ⟨h.xy.symm, h.yu, h.yw, h.yuw⟩

lemma v_group_C (h : Host H x y u v w) : v ∈ grp H w x u := by
  apply mem_grp.mpr
  refine ⟨h.vw, h.xv.symm, h.uv.symm, ?_⟩
  convert h.xuv using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto

lemma v_group_B (h : Host H x y u v w) : v ∈ grp H u w x := by
  apply mem_grp.mpr
  refine ⟨h.uv.symm, h.vw, h.xv.symm, ?_⟩
  convert h.xvw using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto

/-- S1(b): y has the singleton neighbourhood {v} in each anchor relation. -/
theorem y_neighbours (h : Host H x y u v w) :
    nb H x u w y = {v} ∧ nc H x u w y = {v} := by
  have hb : v ∈ nb H x u w y := by
    apply mem_nb.mpr
    refine ⟨v_group_C h, h.yv.symm, ?_⟩
    convert h.yuv using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
  have hc : v ∈ nc H x u w y := by
    apply mem_nc.mpr
    refine ⟨v_group_B h, h.yv, ?_⟩
    convert h.yvw using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
  obtain ⟨s, hs, ht⟩ := lemma2 h.xuw h.uniform h.avoiding (y_group h)
    ⟨v,hb⟩ ⟨v,hc⟩
  have : v = s := by simpa [hs] using hb
  simpa [← this] using And.intro hs ht

/-- S1(c): the distinguished slot v in C has no R_x neighbour. -/
theorem v_no_Rx_C (h : Host H x y u v w) : nb H w x u v = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨hsg, hsv, hxs⟩ := mem_nb.mp hs
  obtain ⟨hsu, hsw, hsx, -⟩ := mem_grp.mp hsg
  have hsl : s ∈ link H {x,v} := by
    apply mem_link.mpr
    refine ⟨by simp [hsx, hsv], ?_⟩
    convert hxs using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
  rw [h.light] at hsl
  simp only [mem_insert, mem_singleton] at hsl
  exact hsl.elim hsu hsw

/-- The mirror no-R_x conclusion for v in B. -/
theorem v_no_Rx_B (h : Host H x y u v w) : nc H u w x v = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨hsg, hvs, hxs⟩ := mem_nc.mp hs
  obtain ⟨hsw, hsx, hsu, -⟩ := mem_grp.mp hsg
  have hsl : s ∈ link H {x,v} := by
    apply mem_link.mpr
    refine ⟨by simp [hsx, hvs.symm], ?_⟩
    convert hxs using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
  rw [h.light] at hsl
  simp only [mem_insert, mem_singleton] at hsl
  exact hsl.elim hsu hsw

/-- Exact R_u neighbour set, S1(c), before separating its distinguished y member. -/
theorem v_Ru_inter (h : Host H x y u v w) :
    nc H w x u v = ((link H {u,v}) ∩ link H {u,w}).erase x := by
  ext s
  constructor
  · intro hs
    obtain ⟨hsg, hvs, huv⟩ := mem_nc.mp hs
    obtain ⟨hsx, hsu, hsw, hsuw⟩ := mem_grp.mp hsg
    apply mem_erase.mpr
    refine ⟨hsx, mem_inter.mpr ⟨?_, ?_⟩⟩
    · apply mem_link.mpr
      refine ⟨by simp [hsu, hvs.symm], ?_⟩
      convert huv using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
    · exact mem_link.mpr ⟨by simp [hsu, hsw], hsuw⟩
  · intro hs
    obtain ⟨hsx, hsuv, hsuw⟩ := (mem_erase.mp hs).imp_right mem_inter.mp
    obtain ⟨hsuv', huv⟩ := mem_link.mp hsuv
    obtain ⟨hsuw', huw⟩ := mem_link.mp hsuw
    simp only [mem_insert, mem_singleton, not_or] at hsuv' hsuw'
    have hsu : s ≠ u := hsuw'.1
    have hsw : s ≠ w := hsuw'.2
    have hsv : s ≠ v := hsuv'.2
    apply mem_nc.mpr
    refine ⟨mem_grp.mpr ⟨hsx, hsu, hsw, huw⟩, hsv.symm, ?_⟩
    convert huv using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto

/-- J1, the nondistinguished neighbours shared by the two base-pair links. -/
def J (H : Finset (Finset V)) (x y u v w : V) : Finset V :=
  ((link H {u,v}) ∩ link H {u,w}) \ {x,y}

/-- S1(c) with the exact J1 definition. -/
theorem v_Ru (h : Host H x y u v w) :
    nc H w x u v = insert y (J H x y u v w) := by
  rw [v_Ru_inter h]
  have hy : y ∈ (link H {u,v}) ∩ link H {u,w} := by
    apply mem_inter.mpr
    exact ⟨mem_link.mpr ⟨by simp [h.yu, h.yv], h.yuv⟩,
      mem_link.mpr ⟨by simp [h.yu, h.yw], h.yuw⟩⟩
  ext s
  simp only [mem_erase, mem_insert, J, mem_sdiff, mem_insert, mem_singleton, not_or]
  constructor
  · rintro ⟨hsx, hs⟩
    by_cases hsy : s = y
    · exact Or.inl hsy
    · exact Or.inr ⟨hs, hsx, hsy⟩
  · rintro (rfl | ⟨hs, hsx, -⟩)
    · exact ⟨h.xy.symm, hy⟩
    · exact ⟨hsx, hs⟩

/-- S1(c): the distinguished v slot has total degree 1+|J1|. -/
theorem v_degree_C (h : Host H x y u v w) :
    (nb H w x u v).card + (nc H w x u v).card = 1 + (J H x y u v w).card := by
  rw [v_no_Rx_C h, v_Ru h, card_empty, zero_add, card_insert_of_notMem]
  · omega
  · simp [J]

/-- The exact slot cost used on the u-side and, by relabelling, the w-side. -/
theorem v_cost_C (h : Host H x y u v w) :
    slotCost H w x u v = 1 / (2 * (2 + ((J H x y u v w).card : ℚ))) := by
  have hd := v_degree_C h
  unfold slotCost
  have hd' : ((nb H w x u v).card : ℚ) + ((nc H w x u v).card : ℚ) =
      1 + ((J H x y u v w).card : ℚ) := by exact_mod_cast hd
  congr 2
  linarith

/-- S1(a)'s common-link identity, conditional only on the G1(iii) cardinality consequence. -/
theorem CN_uw (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    CN H {u,w} = {{x,v},{y,v}} := by
  have hx : ({x,v} : Finset V) ∈ CN H {u,w} := by
    apply pair_mem_CN h.xv h.xu h.xw h.uv.symm h.vw
    · convert h.xuv using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
    · convert h.xvw using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
  have hy : ({y,v} : Finset V) ∈ CN H {u,w} := by
    apply pair_mem_CN h.yv h.yu h.yw h.uv.symm h.vw
    · convert h.yuv using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
    · convert h.yvw using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
  have hne : ({x,v} : Finset V) ≠ {y,v} := by
    intro he
    have : x ∈ ({y,v} : Finset V) := he ▸ mem_insert_self x {v}
    simpa [h.xy, h.xv] using this
  symm
  apply eq_of_subset_of_card_le
  · intro P hP
    simp only [mem_insert, mem_singleton] at hP
    exact hP.elim (fun he => he ▸ hx) (fun he => he ▸ hy)
  · simp [hcard, hne]

/-- S1(a): the two heavy apex-pair links meet precisely at v. -/
theorem heavy_link_inter (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    link H {x,u} ∩ link H {x,w} = {v} := by
  ext s
  constructor
  · intro hs
    obtain ⟨hsu, hsw⟩ := mem_inter.mp hs
    obtain ⟨hsxu, hxus⟩ := mem_link.mp hsu
    obtain ⟨hsxw, hxws⟩ := mem_link.mp hsw
    simp only [mem_insert, mem_singleton, not_or] at hsxu hsxw
    have hp : ({x,s} : Finset V) ∈ CN H {u,w} := by
      apply pair_mem_CN (Ne.symm hsxu.1) h.xu h.xw hsxu.2 hsxw.2
      · convert hxus using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
      · convert hxws using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
    rw [CN_uw h hcard] at hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with he | he
    · have : s ∈ ({x,v} : Finset V) := he ▸ mem_insert_of_mem (mem_singleton_self s)
      simpa [hsxu.1] using this
    · have : x ∈ ({y,v} : Finset V) := he ▸ mem_insert_self x {s}
      simp [h.xy, h.xv] at this
  · intro hs
    have : s = v := mem_singleton.mp hs
    subst s
    apply mem_inter.mpr
    constructor
    · apply mem_link.mpr
      refine ⟨by simp [h.xv.symm, h.uv.symm], ?_⟩
      convert h.xuv using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
    · apply mem_link.mpr
      refine ⟨by simp [h.xv.symm, h.vw], ?_⟩
      convert h.xvw using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto

/-- S1(a): the two base-pair links meet precisely in x and y. -/
theorem base_link_inter (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    link H {u,v} ∩ link H {v,w} = {x,y} := by
  ext s
  constructor
  · intro hs
    obtain ⟨hsu, hsw⟩ := mem_inter.mp hs
    obtain ⟨hsuv, huvs⟩ := mem_link.mp hsu
    obtain ⟨hsvw, hvws⟩ := mem_link.mp hsw
    simp only [mem_insert, mem_singleton, not_or] at hsuv hsvw
    have hp : ({s,v} : Finset V) ∈ CN H {u,w} := by
      apply pair_mem_CN hsuv.2 hsuv.1 hsvw.2 h.uv.symm h.vw
      · convert huvs using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
      · convert hvws using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
    rw [CN_uw h hcard] at hp
    simp only [mem_insert, mem_singleton] at hp ⊢
    rcases hp with he | he
    · have : s ∈ ({x,v} : Finset V) := he ▸ mem_insert_self s {v}
      simp only [mem_insert, mem_singleton] at this
      exact Or.inl (this.resolve_right hsuv.2)
    · have : s ∈ ({y,v} : Finset V) := he ▸ mem_insert_self s {v}
      simp only [mem_insert, mem_singleton] at this
      exact Or.inr (this.resolve_right hsuv.2)
  · intro hs
    simp only [mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact mem_inter.mpr ⟨mem_link.mpr ⟨by simp [h.xu,h.xv],h.xuv⟩,
        mem_link.mpr ⟨by simp [h.xv,h.xw],h.xvw⟩⟩
    · exact mem_inter.mpr ⟨mem_link.mpr ⟨by simp [h.yu,h.yv],h.yuv⟩,
        mem_link.mpr ⟨by simp [h.yv,h.yw],h.yvw⟩⟩

/-- S1(d): y is the only type-2 slot in the anchor group A. -/
theorem only_type2_A (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2) :
    tset H x u w = {y} := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzA, hb, hc⟩ := mem_filter.mp hz
    obtain ⟨s, hs, ht⟩ := lemma2 h.xuw h.uniform h.avoiding hzA (card_pos.mp hb) (card_pos.mp hc)
    have hsb : s ∈ nb H x u w z := by simp [hs]
    have hsc : s ∈ nc H x u w z := by simp [ht]
    obtain ⟨hsC, hsz, husz⟩ := mem_nb.mp hsb
    obtain ⟨hsB, hzs, hwzs⟩ := mem_nc.mp hsc
    have hsint : s ∈ link H {x,u} ∩ link H {x,w} := by
      apply mem_inter.mpr
      constructor
      · exact mem_of_mem_erase hsC
      · have hmem := mem_of_mem_erase hsB
        simpa [pair_comm w x] using hmem
    rw [heavy_link_inter h hcard] at hsint
    have hsv : s = v := mem_singleton.mp hsint
    subst s
    obtain ⟨hzx, hzu, hzw, -⟩ := mem_grp.mp hzA
    have hzint : z ∈ link H {u,v} ∩ link H {v,w} := by
      apply mem_inter.mpr
      constructor
      · apply mem_link.mpr
        refine ⟨by simp [hzu, hzs], ?_⟩
        convert husz using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
      · apply mem_link.mpr
        refine ⟨by simp [hzs, hzw], ?_⟩
        convert hwzs using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
    rw [base_link_inter h hcard] at hzint
    simp only [mem_insert, mem_singleton] at hzint
    exact mem_singleton.mpr (hzint.resolve_left hzx)
  · intro hz
    have hzy : z = y := mem_singleton.mp hz
    subst z
    apply mem_filter.mpr
    refine ⟨y_group h, ?_, ?_⟩ <;> simp [(y_neighbours h).1, (y_neighbours h).2]

/-- Reciprocal adjacency, directly in the existing host sets. -/
lemma nc_reciprocal {a b c z s : V} (hz : z ∈ grp H c a b)
    (hs : s ∈ nc H c a b z) : z ∈ nb H a b c s := by
  obtain ⟨hsA, hzs, hbsz⟩ := mem_nc.mp hs
  apply mem_nb.mpr
  refine ⟨hz, hzs, ?_⟩
  convert hbsz using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto

/-- The genuine set cap underlying S4: every R_u neighbour of a nondistinguished C slot
lies in A_u, after S1(a) has been supplied from G1. No numerical cap is assumed. -/
theorem Ru_neighbours_subset_Au (h : Host H x y u v w)
    (hcard : (CN H {u,w}).card = 2) {s : V} (hs : s ∈ grp H w x u) (hsv : s ≠ v) :
    nc H w x u s ⊆ gset H x u w := by
  intro z hz
  have hsz := nc_reciprocal hs hz
  have hzA := (mem_nc.mp hz).1
  have hb : 0 < (nb H x u w z).card := card_pos.mpr ⟨s,hsz⟩
  have hzy : z ≠ y := by
    intro he
    subst z
    rw [(y_neighbours h).1] at hsz
    exact hsv (mem_singleton.mp hsz)
  have hc : (nc H x u w z).card = 0 := by
    by_contra hn
    have hz2 : z ∈ tset H x u w := mem_filter.mpr ⟨hzA,hb,Nat.pos_of_ne_zero hn⟩
    rw [only_type2_A h hcard] at hz2
    exact hzy (mem_singleton.mp hz2)
  exact mem_filter.mpr ⟨hzA,hb,hc⟩

theorem Ru_degree_cap (h : Host H x y u v w)
    (hcard : (CN H {u,w}).card = 2) {s : V} (hs : s ∈ grp H w x u) (hsv : s ≠ v) :
    (nc H w x u s).card ≤ (gset H x u w).card :=
  card_le_card (Ru_neighbours_subset_Au h hcard hs hsv)

/-- A type-2 C slot has a unique partner in A_u and B, outside Xu.
This is the host content of S8(a) except the commonness over all type-2 slots. -/
theorem type2_C_partner (h : Host H x y u v w)
    (hcard : (CN H {u,w}).card = 2) {r : V} (hr : r ∈ tset H w x u) :
    ∃ p, nb H w x u r = {p} ∧ nc H w x u r = {p} ∧
      p ∈ gset H x u w ∧ p ∈ grp H u w x ∧ p ∉ link H {x,u} := by
  obtain ⟨hrC, hb, hc⟩ := mem_filter.mp hr
  have hrT : ({w,x,u} : Finset V) ∈ H := by
    convert h.xuw using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
  obtain ⟨p, hp, hq⟩ := lemma2 hrT h.uniform h.avoiding hrC (card_pos.mp hb) (card_pos.mp hc)
  have hprx : p ∈ nb H w x u r := by simp [hp]
  have hpru : p ∈ nc H w x u r := by simp [hq]
  have hpB := (mem_nb.mp hprx).1
  have hrv : r ≠ v := by
    intro he
    subst r
    rw [v_no_Rx_C h, card_empty] at hb
    omega
  have hpAu := Ru_neighbours_subset_Au h hcard hrC hrv hpru
  have hpnot : p ∉ link H {x,u} := by
    intro hpXu
    have hpXw : p ∈ link H {x,w} := by
      simpa [pair_comm w x] using mem_of_mem_erase hpB
    have hpv : p = v := by
      have hpint := mem_inter.mpr ⟨hpXu,hpXw⟩
      rw [heavy_link_inter h hcard] at hpint
      exact mem_singleton.mp hpint
    subst p
    have hrnb : r ∈ nc H u w x v := by
      apply mem_nc.mpr
      refine ⟨hrC, (mem_nb.mp hprx).2.1, ?_⟩
      convert (mem_nb.mp hprx).2.2 using 1 <;> ext t <;> simp only [mem_insert, mem_singleton] <;> tauto
    rw [v_no_Rx_B h] at hrnb
    exact notMem_empty r hrnb
  exact ⟨p,hp,hq,hpAu,hpB,hpnot⟩

/-- S8(a): one common partner for all type-2 slots in C, with its actual host location. -/
theorem shared_partner_C (h : Host H x y u v w)
    (hcard : (CN H {u,w}).card = 2) (hn : (tset H w x u).Nonempty) :
    ∃ p, p ∈ gset H x u w ∧ p ∈ grp H u w x ∧ p ∉ link H {x,u} ∧
      ∀ r ∈ tset H w x u, nb H w x u r = {p} ∧ nc H w x u r = {p} := by
  obtain ⟨r,hr⟩ := hn
  obtain ⟨p,hp,hq,hpAu,hpB,hpnot⟩ := type2_C_partner h hcard hr
  refine ⟨p,hpAu,hpB,hpnot,?_⟩
  intro s hs
  obtain ⟨q,hqs,hqt,hqAu,hqB,hqnot⟩ := type2_C_partner h hcard hs
  have hrC := (mem_filter.mp hr).1
  have hqA := (mem_filter.mp hqAu).1
  obtain ⟨hrw,hrx,hru,hrH⟩ := mem_grp.mp hrC
  obtain ⟨hqx,hqu,hqw,hquw⟩ := mem_grp.mp hqA
  obtain ⟨hqu',hqw',hqx',hqxw⟩ := mem_grp.mp hqB
  have hpRx : p ∈ nb H w x u r := by simp [hp]
  have hpRu : p ∈ nc H w x u r := by simp [hq]
  obtain ⟨-,hpr,hxpr⟩ := mem_nb.mp hpRx
  obtain ⟨-,hrp,hurp⟩ := mem_nc.mp hpRu
  obtain ⟨hpx,hpu,hpw,hpuw⟩ := mem_grp.mp (mem_filter.mp hpAu).1
  have hrpCN : ({r,p} : Finset V) ∈ CN H {x,u} := by
    apply pair_mem_CN hrp hrx hru hpx hpu
    · simpa only [insert_comm, pair_comm] using hxpr
    · exact hurp
  have hwqCN : ({w,q} : Finset V) ∈ CN H {x,u} := by
    apply pair_mem_CN hqw.symm h.xw.symm h.uw.symm hqx hqu
    · rw [show insert x ({w,q} : Finset V) = {q,w,x} from triple_perm (fun t => by tauto)]
      exact hqxw
    · rw [show insert u ({w,q} : Finset V) = {q,u,w} from triple_perm (fun t => by tauto)]
      exact hquw
  have hmeet := CN_intersecting h.uniform h.avoiding h.xu hrpCN hwqCN
  obtain ⟨z,hz1,hz2⟩ := not_disjoint_iff.mp hmeet
  simp only [mem_insert,mem_singleton] at hz1 hz2
  have hqp : q = p := by
    rcases hz1 with rfl | rfl
    · rcases hz2 with hrw' | hrq
      · exact False.elim (hrw hrw')
      · exact False.elim (hqnot (hrq ▸ mem_of_mem_erase hrC))
    · rcases hz2 with hpw' | hpq
      · exact False.elim (hpw hpw')
      · exact hpq.symm
  simpa [hqp] using And.intro hqs hqt

/-- R_U is the type-1 R_u class with the distinguished v slot removed. -/
def RU (H : Finset (Finset V)) (x u v w : V) : Finset V :=
  (fset H w x u).erase v

lemma nb_reciprocal {a b c z s : V} (hz : z ∈ grp H a b c)
    (hs : s ∈ nb H a b c z) : z ∈ nc H c a b s := by
  obtain ⟨-,hsz,hbsz⟩ := mem_nb.mp hs
  exact mem_nc.mpr ⟨hz,hsz,hbsz⟩

/-- Every R_u neighbour is v, type 1 in R_u, or type 2. -/
theorem Au_neighbours_classes {z : V} (hz : z ∈ grp H x u w) :
    nb H x u w z ⊆ insert v (RU H x u v w ∪ tset H w x u) := by
  intro s hs
  have hsC := (mem_nb.mp hs).1
  have hsz := nb_reciprocal hz hs
  have hc : 0 < (nc H w x u s).card := card_pos.mpr ⟨z,hsz⟩
  by_cases hsv : s = v
  · simp [hsv]
  · apply mem_insert_of_mem
    rcases Nat.eq_zero_or_pos (nb H w x u s).card with hb | hb
    · apply mem_union_left
      exact mem_erase.mpr ⟨hsv, mem_filter.mpr ⟨hsC,hc,hb⟩⟩
    · apply mem_union_right
      exact mem_filter.mpr ⟨hsC,hb,hc⟩

/-- The uniform exceptional cap in §7.7, derived from the host neighbour sets. -/
theorem Au_degree_cap {z : V} (hz : z ∈ gset H x u w) :
    (nb H x u w z).card + (nc H x u w z).card ≤
      1 + (RU H x u v w).card + (tset H w x u).card := by
  obtain ⟨hzA,-,hc⟩ := mem_filter.mp hz
  have hle := card_le_card (Au_neighbours_classes (v := v) hzA)
  have hi := card_insert_le v (RU H x u v w ∪ tset H w x u)
  have hu := card_union_le (RU H x u v w) (tset H w x u)
  omega

/-- The sharper ordinary cap: type-2 slots contribute only to their actual partner. -/
theorem Au_ordinary_cap {p z : V} (hz : z ∈ gset H x u w) (hzp : z ≠ p)
    (hp : ∀ r ∈ tset H w x u, nc H w x u r = {p}) :
    (nb H x u w z).card + (nc H x u w z).card ≤ 1 + (RU H x u v w).card := by
  obtain ⟨hzA,-,hc⟩ := mem_filter.mp hz
  have hsub : nb H x u w z ⊆ insert v (RU H x u v w) := by
    intro s hs
    have hclass := Au_neighbours_classes (v := v) hzA hs
    simp only [mem_insert,mem_union] at hclass ⊢
    rcases hclass with hsv | hsRU | hs2
    · exact Or.inl hsv
    · exact Or.inr hsRU
    · have hsz := nb_reciprocal hzA hs
      rw [hp s hs2] at hsz
      exact False.elim (hzp (mem_singleton.mp hsz))
  have hle := card_le_card hsub
  have hi := card_insert_le v (RU H x u v w)
  omega

/-- The only exceptional slot in the cardinality caps is derived, not supplied. -/
theorem host_Au_caps (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hn : (tset H w x u).Nonempty) :
    ∃ p ∈ gset H x u w, (∀ z ∈ gset H x u w, z ≠ p →
      (nb H x u w z).card + (nc H x u w z).card ≤ 1 + (RU H x u v w).card) ∧
      (nb H x u w p).card + (nc H x u w p).card ≤
        1 + (RU H x u v w).card + (tset H w x u).card := by
  obtain ⟨p,hp,-,-,hpartners⟩ := shared_partner_C h hcard hn
  refine ⟨p,hp,?_,Au_degree_cap hp⟩
  intro z hz hzp
  exact Au_ordinary_cap hz hzp (fun r hr => (hpartners r hr).2)

/-- Lemma N: the common partner lies in the type-1 cross class of B. -/
theorem partner_in_cross_class (h : Host H x y u v w)
    (hcard : (CN H {u,w}).card = 2) {r p : V} (hr : r ∈ tset H w x u)
    (hp : nb H w x u r = {p}) (hq : nc H w x u r = {p})
    (hpB : p ∈ grp H u w x) (hpnot : p ∉ link H {x,u}) :
    p ∈ fset H u w x := by
  have hrC := (mem_filter.mp hr).1
  have hpRx : p ∈ nb H w x u r := by simp [hp]
  have hpRu : p ∈ nc H w x u r := by simp [hq]
  obtain ⟨-,hpr,hxpr⟩ := mem_nb.mp hpRx
  obtain ⟨hpA,hrp,hurp⟩ := mem_nc.mp hpRu
  have hrnc : r ∈ nc H u w x p := mem_nc.mpr ⟨hrC,hpr,hxpr⟩
  have hnc : 0 < (nc H u w x p).card := card_pos.mpr ⟨r,hrnc⟩
  have hnb : (nb H u w x p).card = 0 := by
    by_contra hn
    have hT : ({u,w,x} : Finset V) ∈ H := by
      rw [show ({u,w,x} : Finset V) = {x,u,w} from triple_perm (fun t => by tauto)]
      exact h.xuw
    obtain ⟨s,hs,ht⟩ := lemma2 hT h.uniform h.avoiding hpB
      (card_pos.mp (Nat.pos_of_ne_zero hn)) ⟨r,hrnc⟩
    have hrs : r = s := by simpa [ht] using hrnc
    have hrnb : r ∈ nb H u w x p := by simp [hs,← hrs]
    obtain ⟨hrA,-,hwrp⟩ := mem_nb.mp hrnb
    obtain ⟨hrw,hrx,hru,-⟩ := mem_grp.mp hrC
    obtain ⟨hpx,hpu,hpw,-⟩ := mem_grp.mp hpA
    have hrCN : ({r,p} : Finset V) ∈ CN H {u,w} :=
      pair_mem_CN hrp hru hrw hpu hpw hurp hwrp
    have hrv : r ≠ v := by
      intro he
      have hb := (mem_filter.mp hr).2.1
      rw [he,v_no_Rx_C h,card_empty] at hb
      omega
    have hpv : p ≠ v := by
      intro he
      apply hpnot
      rw [he]
      exact mem_of_mem_erase (v_group_C h)
    rw [CN_uw h hcard] at hrCN
    simp only [mem_insert,mem_singleton] at hrCN
    rcases hrCN with he | he
    · have hv : v ∈ ({r,p} : Finset V) := by rw [he]; simp
      simp [hrv.symm,hpv.symm] at hv
    · have hv : v ∈ ({r,p} : Finset V) := by rw [he]; simp
      simp [hrv.symm,hpv.symm] at hv
  exact mem_filter.mpr ⟨hpB,hnc,hnb⟩

/-- A reciprocal R_x edge, with the source slot in B and target in C. -/
lemma cross_reciprocal {s r : V} (hs : s ∈ grp H u w x)
    (hr : r ∈ nc H u w x s) : s ∈ nb H w x u r := by
  obtain ⟨-,hsr,hxsr⟩ := mem_nc.mp hr
  exact mem_nb.mpr ⟨hs,hsr,hxsr⟩

/-- The actual R_x neighbour set lies in the ordinary cross class plus the type-2 class. -/
theorem cross_neighbours_classes {s : V} (hs : s ∈ grp H u w x) :
    nc H u w x s ⊆ gset H w x u ∪ tset H w x u := by
  intro r hr
  have hrC := (mem_nc.mp hr).1
  have hsr := cross_reciprocal hs hr
  have hb : 0 < (nb H w x u r).card := card_pos.mpr ⟨s,hsr⟩
  rcases Nat.eq_zero_or_pos (nc H w x u r).card with hc | hc
  · exact mem_union_left _ (mem_filter.mpr ⟨hrC,hb,hc⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨hrC,hb,hc⟩)

/-- Lemma W Step 2's uniform exceptional cap, from host edges. -/
theorem cross_degree_cap {s : V} (hs : s ∈ fset H u w x) :
    (nb H u w x s).card + (nc H u w x s).card ≤
      (gset H w x u).card + (tset H w x u).card := by
  obtain ⟨hsB,-,hb⟩ := mem_filter.mp hs
  have hle := card_le_card (cross_neighbours_classes hsB)
  have hu := card_union_le (gset H w x u) (tset H w x u)
  omega

/-- Lemma W Step 2's ordinary cap, with no contribution from type-2 slots. -/
theorem cross_ordinary_cap {p s : V} (hs : s ∈ fset H u w x) (hsp : s ≠ p)
    (hp : ∀ r ∈ tset H w x u, nb H w x u r = {p}) :
    (nb H u w x s).card + (nc H u w x s).card ≤ (gset H w x u).card := by
  obtain ⟨hsB,-,hb⟩ := mem_filter.mp hs
  have hsub : nc H u w x s ⊆ gset H w x u := by
    intro r hr
    have hc := cross_neighbours_classes hsB hr
    rcases mem_union.mp hc with hrX | hr2
    · exact hrX
    · have hsr := cross_reciprocal hsB hr
      rw [hp r hr2] at hsr
      exact False.elim (hsp (mem_singleton.mp hsr))
  have hle := card_le_card hsub
  omega

/-- All ordinary and exceptional R_x caps with their genuine exceptional vertex. -/
theorem host_cross_caps (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hn : (tset H w x u).Nonempty) :
    ∃ p ∈ fset H u w x, (∀ s ∈ fset H u w x, s ≠ p →
      (nb H u w x s).card + (nc H u w x s).card ≤ (gset H w x u).card) ∧
      (nb H u w x p).card + (nc H u w x p).card ≤
        (gset H w x u).card + (tset H w x u).card := by
  obtain ⟨p,hpAu,hpB,hpnot,hpartners⟩ := shared_partner_C h hcard hn
  obtain ⟨r,hr⟩ := hn
  have hpX := partner_in_cross_class h hcard hr (hpartners r hr).1 (hpartners r hr).2 hpB hpnot
  refine ⟨p,hpX,?_,cross_degree_cap hpX⟩
  intro s hs hsp
  exact cross_ordinary_cap hs hsp (fun r hr => (hpartners r hr).1)

/-- The host forces the admissibility implication m>0 => nB>0. -/
theorem type2_forces_cross (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hn : 0 < (tset H w x u).card) : 0 < (fset H u w x).card := by
  obtain ⟨p,hp,-,-⟩ := host_cross_caps h hcard (card_pos.mp hn)
  exact card_pos.mpr ⟨p,hp⟩

/-- With no ordinary opposite cross slot, every cross slot is the exceptional partner. -/
theorem zero_cross_card_cap (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hz : (gset H w x u).card = 0) : (fset H u w x).card ≤ 1 := by
  by_cases hn : (tset H w x u).Nonempty
  · obtain ⟨p,hp,hordinary,-⟩ := host_cross_caps h hcard hn
    have hsub : fset H u w x ⊆ {p} := by
      intro s hs
      by_contra hsn
      have hsp : s ≠ p := by simpa using hsn
      have hc := hordinary s hs hsp
      have hspos := (mem_filter.mp hs).2.1
      omega
    simpa using card_le_card hsub
  · have hm : (tset H w x u).card = 0 := by
      exact card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)
    have hf : fset H u w x = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro s hs
      have hc := cross_degree_cap hs
      have hspos := (mem_filter.mp hs).2.1
      omega
    simp [hf]

end Erdos643R3.AnchorCaps
