import Mathlib
import Openmath.Erdos643R3.SlotModel
import Openmath.Erdos643R3.L1Top



set_option autoImplicit false

namespace Erdos643R3
namespace Lemma1g

open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.WeightingBound Erdos643R3.SlotModel
  Erdos643R3.L1Top

variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

/-- (b) For a type-2 slot `z` of `A` whose neighbours are the slots of `w`: `CN(a,z) = {bc, bw, cw}`. -/
theorem CN_type2 {a b c z w : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hz : z ∈ grp H a b c)
    (hb : nb H a b c z = {w}) (hc : nc H a b c z = {w}) :
    CN H {a, z} = {{b, c}, {b, w}, {c, w}} := by
  rw [CN_slot_eq hT hH hav hz, hb, hc, image_singleton, image_singleton]
  rfl

omit [Fintype V] in
/-- In a triangle `{uv, vw, uw}` of three distinct vertices no vertex lies in all three pairs. -/
theorem triangle_no_center {u v w x : V} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h : ∀ P ∈ ({{u, v}, {v, w}, {u, w}} : Finset (Finset V)), x ∈ P) : False := by
  have h1 := h {u, v} (by simp)
  have h2 := h {v, w} (by simp)
  have h3 := h {u, w} (by simp)
  simp only [mem_insert, mem_singleton] at h1 h2 h3
  rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> simp_all

/-- (a) For a slot `z` of `A`: the option `{a,z}` is a triangle option iff `z` is type 2. -/
theorem triangular_iff_type2 {a b c z : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) (hz : z ∈ grp H a b c) :
    Triangular H {a, z} ↔ (0 < (nb H a b c z).card ∧ 0 < (nc H a b c z).card) := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  obtain ⟨hza, -, -, -⟩ := mem_grp.mp hz
  constructor
  · rintro ⟨-, u, v, w, huv, hvw, huw, hCN⟩
    by_contra hnot
    rcases Nat.eq_zero_or_pos (nb H a b c z).card with h0 | h0
    · -- every member of `CN(a,z)` contains `c`
      refine triangle_no_center huv hvw huw (x := c) (fun P hP => ?_)
      rw [← hCN] at hP
      rcases mem_CN_slot hT hH hav hz hP with rfl | ⟨x, hx, -⟩ | ⟨y, -, rfl⟩
      · exact mem_insert_of_mem (mem_singleton_self c)
      · rw [card_eq_zero] at h0; rw [h0] at hx; exact absurd hx (notMem_empty x)
      · exact mem_insert_self c {y}
    · have h1 : (nc H a b c z).card = 0 := by omega
      refine triangle_no_center huv hvw huw (x := b) (fun P hP => ?_)
      rw [← hCN] at hP
      rcases mem_CN_slot hT hH hav hz hP with rfl | ⟨x, -, rfl⟩ | ⟨y, hy, -⟩
      · exact mem_insert_self b {c}
      · exact mem_insert_self b {x}
      · rw [card_eq_zero] at h1; rw [h1] at hy; exact absurd hy (notMem_empty y)
  · rintro ⟨h1, h2⟩
    obtain ⟨w, hb, hc⟩ := lemma2 hT hH hav hz (card_pos.mp h1) (card_pos.mp h2)
    have hwC : w ∈ grp H c a b := (mem_nb.mp (show w ∈ nb H a b c z by rw [hb]; exact mem_singleton_self w)).1
    obtain ⟨hwc, -, hwb, -⟩ := mem_grp.mp hwC
    refine ⟨card_pair (Ne.symm hza), b, c, w, hbc, Ne.symm hwc, Ne.symm hwb, ?_⟩
    rw [CN_type2 hT hH hav hz hb hc]
    ext P; simp only [mem_insert, mem_singleton]; tauto

/-! ## (a) The options of `T` and the number of triangle options -/

variable (H) in
/-- The options of `T = {a,b,c}`: `{a,z}` (`z ∈ A`), `{b,y}` (`y ∈ B`), `{c,x}` (`x ∈ C`). -/
def options (a b c : V) : Finset (Finset V) :=
  (grp H a b c).image (fun z => ({a, z} : Finset V)) ∪ (grp H b c a).image (fun y => ({b, y} : Finset V)) ∪
    (grp H c a b).image (fun x => ({c, x} : Finset V))

/-- The option of a slot of the view `(a,b,c)` determines the slot (injectivity within a group). -/
theorem option_inj {a b c : V} : Set.InjOn (fun z => ({a, z} : Finset V)) (grp H a b c) := by
  intro z hz z' hz' he
  have hza := (mem_grp.mp hz).1
  have : z ∈ ({a, z'} : Finset V) := by
    rw [← show ({a, z} : Finset V) = {a, z'} from he]; exact mem_insert_of_mem (mem_singleton_self z)
  rw [mem_insert, mem_singleton] at this
  rcases this with h | h
  · exact absurd h hza
  · exact h

omit [Fintype V] in
/-- Options of slots of different groups are different (an option meets `T` only in its apex). -/
theorem options_ne {u v z y : V} (huv : u ≠ v) (hyu : y ≠ u) : ({u, z} : Finset V) ≠ {v, y} := by
  intro he
  have : u ∈ ({v, y} : Finset V) := by rw [← he]; exact mem_insert_self u {z}
  rw [mem_insert, mem_singleton] at this
  rcases this with h | h
  · exact huv h
  · exact hyu h.symm

theorem triangle_filter_eq {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    ((grp H a b c).image (fun z => ({a, z} : Finset V))).filter (Triangular H) =
      (tset H a b c).image (fun z => ({a, z} : Finset V)) := by
  rw [filter_image]
  congr 1
  unfold tset
  exact filter_congr (fun z hz => triangular_iff_type2 hT hH hav hz)

/-- (a) `T` has exactly `t = tA + tB + tC` triangle options. -/
theorem card_triangle_options {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    ((options H a b c).filter (Triangular H)).card =
      (tset H a b c).card + (tset H b c a).card + (tset H c a b).card := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  have hT1 := triple_rot hT
  have hT2 := triple_rot hT1
  unfold options
  rw [filter_union, filter_union, triangle_filter_eq hT hH hav, triangle_filter_eq hT1 hH hav,
    triangle_filter_eq hT2 hH hav]
  have d1 : Disjoint ((tset H a b c).image (fun z => ({a, z} : Finset V)))
      ((tset H b c a).image (fun y => ({b, y} : Finset V))) := by
    rw [disjoint_left]; simp only [mem_image]
    rintro P ⟨z, -, rfl⟩ ⟨y, hy, he⟩
    exact options_ne hab (mem_grp.mp (mem_filter.mp hy).1).2.2.1 he.symm
  have d2 : Disjoint ((tset H a b c).image (fun z => ({a, z} : Finset V)) ∪
      (tset H b c a).image (fun y => ({b, y} : Finset V)))
      ((tset H c a b).image (fun x => ({c, x} : Finset V))) := by
    rw [disjoint_left]; simp only [mem_union, mem_image]
    rintro P (⟨z, -, rfl⟩ | ⟨y, -, rfl⟩) ⟨x, hx, he⟩
    · exact options_ne hac (mem_grp.mp (mem_filter.mp hx).1).2.1 he.symm
    · exact options_ne hbc (mem_grp.mp (mem_filter.mp hx).1).2.2.1 he.symm
  have i1 : Set.InjOn (fun z => ({a, z} : Finset V)) (tset H a b c) :=
    option_inj.mono (fun z hz => (mem_filter.mp hz).1)
  have i2 : Set.InjOn (fun y => ({b, y} : Finset V)) (tset H b c a) :=
    option_inj.mono (fun z hz => (mem_filter.mp hz).1)
  have i3 : Set.InjOn (fun x => ({c, x} : Finset V)) (tset H c a b) :=
    option_inj.mono (fun z hz => (mem_filter.mp hz).1)
  rw [card_union_of_disjoint d2, card_union_of_disjoint d1, card_image_of_injOn i1,
    card_image_of_injOn i2, card_image_of_injOn i3]

/-! ## (b) Light pairs -/

/-- `k_ab = 1 + |C|` (in `ℕ`). -/
theorem codeg_ab {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H) :
    codeg H {a, b} = 1 + (grp H c a b).card := by
  have h := codeg_eq_one_add_card_grp (triple_rot (triple_rot hT)) hH
  exact_mod_cast h

/-- `k_ac = 1 + |B|` (in `ℕ`). -/
theorem codeg_ac {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H) :
    codeg H {a, c} = 1 + (grp H b c a).card := by
  have h := codeg_eq_one_add_card_grp (triple_rot hT) hH
  rw [pair_comm c a] at h
  exact_mod_cast h

/-- (b) For a type-2 slot `z` of `A` with `R_b`-neighbour `w`: `ab` is light iff `C = {w}`, and then
`L(ab) = {c, w}`. -/
theorem light_ab_iff {a b c z w : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hb : nb H a b c z = {w}) :
    (codeg H {a, b} = 2 ↔ grp H c a b = {w}) ∧ (grp H c a b = {w} → link H {a, b} = {c, w}) := by
  have hwC : w ∈ grp H c a b := (mem_nb.mp (show w ∈ nb H a b c z by rw [hb]; exact mem_singleton_self w)).1
  have hc := (apex_mem hH hT).1
  refine ⟨?_, fun hC => ?_⟩
  · rw [codeg_ab hT hH]
    constructor
    · intro h
      have h1 : (grp H c a b).card = 1 := by omega
      obtain ⟨x, hx⟩ := card_eq_one.mp h1
      rw [hx] at hwC ⊢; rw [mem_singleton.mp hwC]
    · intro h; rw [h, card_singleton]
  · rw [← insert_erase hc]
    show insert c (grp H c a b) = {c, w}
    rw [hC]

/-- (b) For a type-2 slot `z` of `A` with `R_c`-neighbour `w`: `ac` is light iff `B = {w}`, and then
`L(ac) = {b, w}`. -/
theorem light_ac_iff {a b c z w : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hc : nc H a b c z = {w}) :
    (codeg H {a, c} = 2 ↔ grp H b c a = {w}) ∧ (grp H b c a = {w} → link H {a, c} = {b, w}) := by
  have hwB : w ∈ grp H b c a := (mem_nc.mp (show w ∈ nc H a b c z by rw [hc]; exact mem_singleton_self w)).1
  have hb := (apex_mem hH hT).2.2
  refine ⟨?_, fun hB => ?_⟩
  · rw [codeg_ac hT hH]
    constructor
    · intro h
      have h1 : (grp H b c a).card = 1 := by omega
      obtain ⟨x, hx⟩ := card_eq_one.mp h1
      rw [hx] at hwB ⊢; rw [mem_singleton.mp hwB]
    · intro h; rw [h, card_singleton]
  · rw [pair_comm a c] at hb ⊢
    rw [← insert_erase hb]
    show insert b (grp H b c a) = {b, w}
    rw [hB]

end Lemma1g
end Erdos643R3
