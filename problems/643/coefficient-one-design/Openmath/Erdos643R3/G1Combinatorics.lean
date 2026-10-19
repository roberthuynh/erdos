import Openmath.Erdos643R3.Lemma1g
import Openmath.Erdos643R3.G1Arith

set_option autoImplicit false

namespace Erdos643R3.G1Combinatorics
open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.WeightingBound
  Erdos643R3.SlotModel Erdos643R3.Lemma1g Erdos643R3.Pw2312 Erdos643R3.Lemma3

variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

/-- A unique type-2 slot in A leaves no type-2 slots in either other group. -/
theorem unique_type2 {a b c z : V} (hz : z ∈ tset H a b c)
    (ht : (tset H a b c).card + (tset H b c a).card + (tset H c a b).card = 1) :
    tset H a b c = {z} ∧ tset H b c a = ∅ ∧ tset H c a b = ∅ := by
  have hp := card_pos.mpr ⟨z, hz⟩
  have hA : (tset H a b c).card = 1 := by omega
  have hB : (tset H b c a).card = 0 := by omega
  have hC : (tset H c a b).card = 0 := by omega
  refine ⟨?_, card_eq_zero.mp hB, card_eq_zero.mp hC⟩
  obtain ⟨u, hu⟩ := card_eq_one.mp hA
  rw [hu] at hz ⊢
  rw [mem_singleton.mp hz]

/-- Lemma 1g(c): the two partner slots have exactly the indicated type-1 roles. -/
theorem partner_types {a b c z w : V} (hz : z ∈ tset H a b c)
    (ht : (tset H a b c).card + (tset H b c a).card + (tset H c a b).card = 1)
    (hb : nb H a b c z = {w}) (hc : nc H a b c z = {w}) :
    w ∈ gset H b c a ∧ w ∈ fset H c a b := by
  have hzA := (mem_filter.mp hz).1
  have hwC := mem_nb.mp (show w ∈ nb H a b c z by rw [hb]; simp)
  have hwB := mem_nc.mp (show w ∈ nc H a b c z by rw [hc]; simp)
  have hzB : z ∈ nb H b c a w := mem_nb.mpr ⟨hzA, hwB.2⟩
  have hzC : z ∈ nc H c a b w := mem_nc.mpr ⟨hzA, hwC.2⟩
  have hpB := card_pos.mpr ⟨z, hzB⟩
  have hpC := card_pos.mpr ⟨z, hzC⟩
  obtain ⟨-, htB, htC⟩ := unique_type2 hz ht
  have heB : (nc H b c a w).card = 0 := by
    by_contra he
    have hm : w ∈ tset H b c a := mem_filter.mpr ⟨hwB.1, hpB, Nat.pos_of_ne_zero he⟩
    rw [htB] at hm
    exact notMem_empty _ hm
  have heC : (nb H c a b w).card = 0 := by
    by_contra he
    have hm : w ∈ tset H c a b := mem_filter.mpr ⟨hwC.1, Nat.pos_of_ne_zero he, hpC⟩
    rw [htC] at hm
    exact notMem_empty _ hm
  exact ⟨mem_filter.mpr ⟨hwB.1, hpB, heB⟩, mem_filter.mpr ⟨hwC.1, hpC, heC⟩⟩

/-- In a singleton C group all positive R_b degrees point to its unique vertex. -/
theorem nb_nonempty_singleton {a b c v w : V} (hC : grp H c a b = {w}) :
    0 < (nb H a b c v).card ↔ w ∈ nb H a b c v := by
  rw [card_pos]
  constructor
  · rintro ⟨x, hx⟩
    have hxC := (mem_nb.mp hx).1
    rw [hC, mem_singleton] at hxC
    rwa [hxC] at hx
  · intro h; exact ⟨w, h⟩

/-- Lemma 1g(d), exact neighbour-set identity. -/
theorem singleton_partner_neighbors {a b c z w : V} (hz : z ∈ tset H a b c)
    (ht : (tset H a b c).card + (tset H b c a).card + (tset H c a b).card = 1)
    (hC : grp H c a b = {w}) :
    nc H c a b w = insert z (gset H a b c) := by
  obtain ⟨htA, -, -⟩ := unique_type2 hz ht
  ext v
  constructor
  · intro hv
    have hvA := (mem_nc.mp hv).1
    have hw : w ∈ nb H a b c v := mem_nb.mpr ⟨by rw [hC]; simp, (mem_nc.mp hv).2⟩
    have hp := card_pos.mpr ⟨w, hw⟩
    by_cases he : (nc H a b c v).card = 0
    · exact mem_insert_of_mem (mem_filter.mpr ⟨hvA, hp, he⟩)
    · have hm : v ∈ tset H a b c := mem_filter.mpr ⟨hvA, hp, Nat.pos_of_ne_zero he⟩
      rw [htA, mem_singleton] at hm
      exact mem_insert.mpr (Or.inl hm)
  · intro hv
    rcases mem_insert.mp hv with rfl | hv
    · have hw := (nb_nonempty_singleton hC).mp (mem_filter.mp hz).2.1
      exact mem_nc.mpr ⟨(mem_filter.mp hz).1, (mem_nb.mp hw).2⟩
    · have hvg := mem_filter.mp hv
      have hw := (nb_nonempty_singleton hC).mp hvg.2.1
      exact mem_nc.mpr ⟨hvg.1, (mem_nb.mp hw).2⟩

/-- Lemma 1g(d): if C is the singleton partner, s_cw = 2 + ab. -/
theorem card_CN_singleton_partner {a b c z w : V}
    (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hz : z ∈ tset H a b c)
    (ht : (tset H a b c).card + (tset H b c a).card + (tset H c a b).card = 1)
    (hb : nb H a b c z = {w}) (hc : nc H a b c z = {w})
    (hC : grp H c a b = {w}) :
    (CN H {c, w}).card = 2 + (gset H a b c).card := by
  have hw := (partner_types hz ht hb hc).2
  have hno : z ∉ gset H a b c := by
    intro h
    have hpos := (mem_filter.mp hz).2.2
    have he := (mem_filter.mp h).2.2
    omega
  rw [card_CN_slot (triple_rot (triple_rot hT)) hH hav (mem_filter.mp hw).1,
    (mem_filter.mp hw).2.2, singleton_partner_neighbors hz ht hC, card_insert_of_notMem hno]
  omega

/-- In a singleton B group all positive R_c degrees point to its unique vertex. -/
theorem nc_nonempty_singleton {a b c v w : V} (hB : grp H b c a = {w}) :
    0 < (nc H a b c v).card ↔ w ∈ nc H a b c v := by
  rw [card_pos]
  constructor
  · rintro ⟨x, hx⟩
    have hxB := (mem_nc.mp hx).1
    rw [hB, mem_singleton] at hxB
    rwa [hxB] at hx
  · intro h; exact ⟨w, h⟩

/-- Symmetric Lemma 1g(d), exact neighbour-set identity. -/
theorem singleton_partner_neighbors_B {a b c z w : V} (hz : z ∈ tset H a b c)
    (ht : (tset H a b c).card + (tset H b c a).card + (tset H c a b).card = 1)
    (hB : grp H b c a = {w}) :
    nb H b c a w = insert z (fset H a b c) := by
  obtain ⟨htA, -, -⟩ := unique_type2 hz ht
  ext v
  constructor
  · intro hv
    have hvA := (mem_nb.mp hv).1
    have hw : w ∈ nc H a b c v := mem_nc.mpr ⟨by rw [hB]; simp, (mem_nb.mp hv).2⟩
    have hp := card_pos.mpr ⟨w, hw⟩
    by_cases he : (nb H a b c v).card = 0
    · exact mem_insert_of_mem (mem_filter.mpr ⟨hvA, hp, he⟩)
    · have hm : v ∈ tset H a b c := mem_filter.mpr ⟨hvA, Nat.pos_of_ne_zero he, hp⟩
      rw [htA, mem_singleton] at hm
      exact mem_insert.mpr (Or.inl hm)
  · intro hv
    rcases mem_insert.mp hv with rfl | hv
    · have hw := (nc_nonempty_singleton hB).mp (mem_filter.mp hz).2.2
      exact mem_nb.mpr ⟨(mem_filter.mp hz).1, (mem_nc.mp hw).2⟩
    · have hvf := mem_filter.mp hv
      have hw := (nc_nonempty_singleton hB).mp hvf.2.1
      exact mem_nb.mpr ⟨hvf.1, (mem_nc.mp hw).2⟩

/-- Symmetric Lemma 1g(d): if B is the singleton partner, s_bw = 2 + ac. -/
theorem card_CN_singleton_partner_B {a b c z w : V}
    (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hz : z ∈ tset H a b c)
    (ht : (tset H a b c).card + (tset H b c a).card + (tset H c a b).card = 1)
    (hb : nb H a b c z = {w}) (hc : nc H a b c z = {w})
    (hB : grp H b c a = {w}) :
    (CN H {b, w}).card = 2 + (fset H a b c).card := by
  have hw := (partner_types hz ht hb hc).1
  have hno : z ∉ fset H a b c := by
    intro h
    have hpos := (mem_filter.mp hz).2.1
    have he := (mem_filter.mp h).2.2
    omega
  rw [card_CN_slot (triple_rot hT) hH hav (mem_filter.mp hw).1,
    (mem_filter.mp hw).2.2, singleton_partner_neighbors_B hz ht hB, card_insert_of_notMem hno]
  omega

/-- A feasible profile with a type-2 slot has a non-isolated slot in every group. -/
theorem profile_groups_pos (π : Profile) (hF : Feas π) (ht : 1 ≤ π.t0 + π.t1 + π.t2) :
    1 ≤ π.f0 + π.g0 + π.t0 ∧ 1 ≤ π.f1 + π.g1 + π.t1 ∧ 1 ≤ π.f2 + π.g2 + π.t2 := by
  obtain ⟨h0, h1, h2⟩ := hF
  omega

/-- Lemma 2g, at profile level with all three possible isolated-slot positions. -/
theorem isolated_profile_bound (π : Profile) (hF : Feas π) (ht : 1 ≤ π.t0 + π.t1 + π.t2)
    (i0 i1 i2 : ℕ) (hi : 1 ≤ i0 + i1 + i2) : 9 / 4 ≤ PhiPlus π i0 i1 i2 := by
  obtain ⟨hn0, hn1, hn2⟩ := profile_groups_pos π hF ht
  have hbase := Pw2312Main.theorem2 π hF
  have hd0 := Delta_nonneg π.f0 π.g0 π.t0 i0
  have hd1 := Delta_nonneg π.f1 π.g1 π.t1 i1
  have hd2 := Delta_nonneg π.f2 π.g2 π.t2 i2
  unfold PhiPlus
  by_cases h0 : 1 ≤ i0
  · have := G1Arith.Delta_ge_third hn0 h0
    linarith
  by_cases h1 : 1 ≤ i1
  · have := G1Arith.Delta_ge_third hn1 h1
    linarith
  have h2 : 1 ≤ i2 := by omega
  have := G1Arith.Delta_ge_third hn2 h2
  linarith

/-- Full Lemma 2g. This slightly stronger version requires at least one type-2 slot. -/
theorem lemma2g {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (ht : 1 ≤ (tset H a b c).card + (tset H b c a).card + (tset H c a b).card)
    (hi : 1 ≤ (iset H a b c).card + (iset H b c a).card + (iset H c a b).card) :
    9 / 4 ≤ sigmaW H {a, b, c} + tauW H {a, b, c} := by
  exact (isolated_profile_bound (profileOf H a b c) (lemma3 hT hH hav).2 ht
    (iset H a b c).card (iset H b c a).card (iset H c a b).card hi).trans
      (lemma3_plus hT hH hav)

/-- A deficient triple with any type-2 slot has no isolated slots. -/
theorem deficient_no_isolated {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (ht : 1 ≤ (tset H a b c).card + (tset H b c a).card + (tset H c a b).card)
    (hd : sigmaW H {a, b, c} + tauW H {a, b, c} < 2) :
    (iset H a b c).card = 0 ∧ (iset H b c a).card = 0 ∧ (iset H c a b).card = 0 := by
  by_contra hn
  have hi : 1 ≤ (iset H a b c).card + (iset H b c a).card + (iset H c a b).card := by omega
  have := lemma2g hT hH hav ht hi
  linarith

/-- Group sizes equal their profile counts when there are no isolated slots. -/
theorem group_card_no_isolated {a b c : V} (hi : (iset H a b c).card = 0) :
    (grp H a b c).card = (fset H a b c).card + (gset H a b c).card + (tset H a b c).card := by
  have h := card_grp_eq (H := H) a b c
  rw [hi] at h
  norm_num at h
  exact_mod_cast h

/-- Canonical G1-compliant profile, with its unique type-2 slot in A. -/
def Compliant0 (π : Profile) : Prop :=
  ((π.f1 + π.g1 + π.t1 = 1) ↔ ¬ (π.f2 + π.g2 + π.t2 = 1)) ∧
    (π.f2 + π.g2 + π.t2 = 1 → π.g0 = 0) ∧
    (π.f1 + π.g1 + π.t1 = 1 → π.f0 = 0)

/-- Geometric G1 conditions (ii) and (iii), in the view with triangle option {a,z}. -/
def GeometricG1 (a b c w : V) : Prop :=
  ((codeg H {a, c} = 2) ↔ ¬ (codeg H {a, b} = 2)) ∧
    (codeg H {a, b} = 2 → link H {a, b} = {c, w} ∧ (CN H {c, w}).card = 2) ∧
    (codeg H {a, c} = 2 → link H {a, c} = {b, w} ∧ (CN H {b, w}).card = 2)

/-- Corollary 1g: exact profile-to-geometric G1 translation. -/
theorem compliant_iff_geometric {a b c z w : V}
    (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hz : z ∈ tset H a b c)
    (ht : (tset H a b c).card + (tset H b c a).card + (tset H c a b).card = 1)
    (hb : nb H a b c z = {w}) (hc : nc H a b c z = {w})
    (hiB : (iset H b c a).card = 0) (hiC : (iset H c a b).card = 0) :
    Compliant0 (profileOf H a b c) ↔ GeometricG1 (H := H) a b c w := by
  have eB := group_card_no_isolated hiB
  have eC := group_card_no_isolated hiC
  have lB : codeg H {a, c} = 2 ↔
      (fset H b c a).card + (gset H b c a).card + (tset H b c a).card = 1 := by
    rw [codeg_ac hT hH, eB]; omega
  have lC : codeg H {a, b} = 2 ↔
      (fset H c a b).card + (gset H c a b).card + (tset H c a b).card = 1 := by
    rw [codeg_ab hT hH, eC]; omega
  have dC : codeg H {a, b} = 2 →
      (CN H {c, w}).card = 2 + (gset H a b c).card := by
    intro h
    exact card_CN_singleton_partner hT hH hav hz ht hb hc ((light_ab_iff hT hH hb).1.mp h)
  have dB : codeg H {a, c} = 2 →
      (CN H {b, w}).card = 2 + (fset H a b c).card := by
    intro h
    exact card_CN_singleton_partner_B hT hH hav hz ht hb hc ((light_ac_iff hT hH hc).1.mp h)
  simp only [Compliant0, profileOf, GeometricG1]
  constructor
  · rintro ⟨he, hg, hf⟩
    refine ⟨?_, ?_, ?_⟩
    · exact lB.trans (he.trans (not_congr lC).symm)
    · intro h
      refine ⟨(light_ab_iff hT hH hb).2 ((light_ab_iff hT hH hb).1.mp h), ?_⟩
      rw [dC h, hg (lC.mp h)]
    · intro h
      refine ⟨(light_ac_iff hT hH hc).2 ((light_ac_iff hT hH hc).1.mp h), ?_⟩
      rw [dB h, hf (lB.mp h)]
  · rintro ⟨he, hg, hf⟩
    refine ⟨lB.symm.trans (he.trans (not_congr lC)), ?_, ?_⟩
    · intro h
      have := (hg (lC.mpr h)).2
      rw [dC (lC.mpr h)] at this
      omega
    · intro h
      have := (hf (lB.mpr h)).2
      rw [dB (lB.mpr h)] at this
      omega

/-- A deficient triple has a type-2 slot, by the strict t=0 profile bound. -/
theorem deficient_type2_pos {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hd : sigmaW H {a, b, c} + tauW H {a, b, c} < 2) :
    1 ≤ (tset H a b c).card + (tset H b c a).card + (tset H c a b).card := by
  by_contra hn
  have h0 : (profileOf H a b c).t0 = 0 := by simp only [profileOf]; omega
  have h1 : (profileOf H a b c).t1 = 0 := by simp only [profileOf]; omega
  have h2 : (profileOf H a b c).t2 = 0 := by simp only [profileOf]; omega
  have hL := lemma3 hT hH hav
  have := G1Arith.lemma3g (profileOf H a b c) hL.2 h0 h1 h2
  linarith [hL.1]

/-- Every deficient triple has no isolated slots; this does not require Theorem 4g. -/
theorem deficient_isolated_zero {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hd : sigmaW H {a, b, c} + tauW H {a, b, c} < 2) :
    (iset H a b c).card = 0 ∧ (iset H b c a).card = 0 ∧ (iset H c a b).card = 0 :=
  deficient_no_isolated hT hH hav (deficient_type2_pos hT hH hav hd) hd

/-- Corollary 6g, exact profile of the singleton-C orientation of a compliant triple. -/
theorem compliant_shape {a b c z w : V} (hz : z ∈ tset H a b c)
    (ht : (tset H a b c).card + (tset H b c a).card + (tset H c a b).card = 1)
    (hb : nb H a b c z = {w}) (hc : nc H a b c z = {w})
    (hiA : (iset H a b c).card = 0) (hiB : (iset H b c a).card = 0)
    (hiC : (iset H c a b).card = 0) (hC : grp H c a b = {w})
    (hG : Compliant0 (profileOf H a b c)) :
    (tset H a b c).card = 1 ∧ (tset H b c a).card = 0 ∧ (tset H c a b).card = 0 ∧
    (gset H a b c).card = 0 ∧ (gset H c a b).card = 0 ∧ (fset H b c a).card = 0 ∧
    (fset H c a b).card = 1 ∧ (grp H a b c).card = 1 + (fset H a b c).card ∧
    (grp H b c a).card = (gset H b c a).card := by
  obtain ⟨htA, htB, htC⟩ := unique_type2 hz ht
  have tA : (tset H a b c).card = 1 := by rw [htA]; simp
  have tB : (tset H b c a).card = 0 := by rw [htB]; simp
  have tC : (tset H c a b).card = 0 := by rw [htC]; simp
  have cg : (grp H c a b).card = 1 := by rw [hC]; simp
  have cp := group_card_no_isolated hiC
  have hg0 : (gset H a b c).card = 0 := hG.2.1 (by
    change (fset H c a b).card + (gset H c a b).card + (tset H c a b).card = 1
    omega)
  have fp := card_pos.mpr ⟨w, (partner_types hz ht hb hc).2⟩
  have gf : (gset H c a b).card = 0 := by omega
  have ff : (fset H c a b).card = 1 := by omega
  have hF := feas_rel (H := H) (a := b) (b := c) (c := a)
  have bf : (fset H b c a).card = 0 := by omega
  have ca := group_card_no_isolated hiA
  have cb := group_card_no_isolated hiB
  exact ⟨tA, tB, tC, hg0, gf, bf, ff, by omega, by omega⟩

/-- The unique type-2 slot determines the unique triangle option, as an exact set identity. -/
theorem unique_triangle_option {a b c z : V}
    (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hz : z ∈ tset H a b c)
    (ht : (tset H a b c).card + (tset H b c a).card + (tset H c a b).card = 1) :
    (options H a b c).filter (L1Top.Triangular H) = {{a,z}} := by
  have hc : ((options H a b c).filter (L1Top.Triangular H)).card = 1 := by
    rw [card_triangle_options hT hH hav, ht]
  have hm : ({a,z} : Finset V) ∈ (options H a b c).filter (L1Top.Triangular H) := by
    refine mem_filter.mpr ⟨?_, (triangular_iff_type2 hT hH hav (mem_filter.mp hz).1).mpr
      (mem_filter.mp hz).2⟩
    unfold options
    exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨z, (mem_filter.mp hz).1, rfl⟩))
  obtain ⟨q, hq⟩ := card_eq_one.mp hc
  rw [hq] at hm ⊢
  rw [mem_singleton.mp hm]

end Erdos643R3.G1Combinatorics
