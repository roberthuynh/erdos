import Openmath.Erdos643R3.Lemma1g
import Openmath.Erdos643R3.RedistArith

/-! Lemma Q(iii) in the existing labelled slot model. -/
set_option autoImplicit false
namespace Erdos643R3.BothLight
open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.SlotModel Erdos643R3.L1Top
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

/-- Reciprocity for the two descriptions of a relation edge. -/
theorem nb_nc_iff {a b c z d : V} (hz : z ∈ grp H a b c) (hd : d ∈ grp H c a b) :
    d ∈ nb H a b c z ↔ z ∈ nc H c a b d := by
  rw [mem_nb, mem_nc]
  simp only [hz, hd, true_and]

/-- The relation between the two identical singleton groups has no edge. -/
theorem singleton_cross_empty {a b c d : V}
    (hB : grp H b c a = {d}) (hC : grp H c a b = {d}) :
    nc H b c a d = ∅ ∧ nb H c a b d = ∅ := by
  constructor
  · ext z
    simp only [nc, hC, mem_filter, mem_singleton, rel, notMem_empty, iff_false]
    rintro ⟨rfl, hne, _⟩
    exact hne rfl
  · ext z
    simp only [nb, hB, mem_filter, mem_singleton, rel, notMem_empty, iff_false]
    rintro ⟨rfl, hne, _⟩
    exact hne rfl

/-- If a singleton group's option has common-link size two, its only neighbour
is the specified type-2 slot. This is the combinatorial use of `a = 2` in Q. -/
theorem one_neighbor {a b c d y : V} (hT : ({a,b,c} : Finset V) ∈ H)
    (hH : Uniform H) (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hB : grp H b c a = {d}) (hC : grp H c a b = {d})
    (hy : y ∈ grp H a b c) (hyb : nb H a b c y = {d})
    (hs : (CN H {c,d}).card = 2) : nc H c a b d = {y} := by
  have hd : d ∈ grp H c a b := by rw [hC]; simp
  have hz := card_CN_slot (triple_rot (triple_rot hT)) hH hav hd
  have hcross := (singleton_cross_empty hB hC).2
  rw [hs, hcross, card_empty] at hz
  have hcard : (nc H c a b d).card = 1 := by omega
  have hymem : y ∈ nc H c a b d := (nb_nc_iff hy hd).mp (by rw [hyb]; simp)
  obtain ⟨z, he⟩ := card_eq_one.mp hcard
  rw [he] at hymem
  rw [he, mem_singleton.mp hymem]

/-- All reverse neighbours disappear away from the distinguished slot. -/
theorem nb_shape {a b c d y : V} (hC : grp H c a b = {d})
    (hCy : nc H c a b d = {y}) {z : V} (hz : z ∈ grp H a b c) :
    nb H a b c z = if z = y then {d} else ∅ := by
  have hd : d ∈ grp H c a b := by rw [hC]; simp
  ext w
  by_cases hzy : z = y
  · subst z
    simp only [ite_true, mem_singleton]
    constructor
    · intro hw
      have := (mem_nb.mp hw).1
      simpa [hC] using this
    · rintro rfl
      exact (nb_nc_iff hz hd).mpr (by rw [hCy]; simp)
  · rw [if_neg hzy]
    simp only [notMem_empty, iff_false]
    intro hw
    have hwd : w = d := by simpa [hC] using (mem_nb.mp hw).1
    subst w
    have hh := (nb_nc_iff hz hd).mp hw
    rw [hCy, mem_singleton] at hh
    exact hzy hh

/-- Q(iii), reduced only to its concrete slot data. The distinguished slot has
both neighbours, and the opposite singleton option has size two. -/
theorem charge_and_options {a b c d y : V} (hT : ({a,b,c} : Finset V) ∈ H)
    (hH : Uniform H) (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hB : grp H b c a = {d}) (hC : grp H c a b = {d})
    (hy : y ∈ grp H a b c) (hyb : nb H a b c y = {d})
    (hyc : nc H a b c y = {d}) (hs : (CN H {c,d}).card = 2) :
    (1/6 : ℚ) ≤ charge H {a,b,c} ∧
      ((Lemma1g.options H a b c).filter (Triangular H)).card = 1 := by
  have hCy := one_neighbor hT hH hav hB hC hy hyb hs
  have hbshape := fun z hz => nb_shape hC hCy (z := z) hz
  obtain ⟨hBnc, hCnb⟩ := singleton_cross_empty hB hC
  have hnc_sub : ∀ z, nc H a b c z ⊆ {d} := by
    intro z w hw
    simpa [hB] using (mem_nc.mp hw).1
  have ht : tset H a b c = {y} := by
    ext z
    simp only [tset, mem_filter, mem_singleton]
    constructor
    · rintro ⟨hz, hzb, hzc⟩
      by_contra hzy
      rw [hbshape z hz, if_neg hzy, card_empty] at hzb
      omega
    · rintro rfl
      exact ⟨hy, by simp [hyb, hyc]⟩
  have hg : gset H a b c = ∅ := by
    ext z
    simp only [gset, mem_filter, notMem_empty, iff_false]
    rintro ⟨hz, hzb, hzc⟩
    by_cases hzy : z = y
    · subst z; rw [hyc, card_singleton] at hzc; omega
    · rw [hbshape z hz, if_neg hzy, card_empty] at hzb; omega
  have hyf : y ∉ fset H a b c := by
    intro hh
    have hh' := (mem_filter.mp hh).2.2
    rw [hyb, card_singleton] at hh'
    omega
  have hfcost : ∑ z ∈ fset H a b c, 1 / (2 * (1 + ((nc H a b c z).card : ℚ))) =
      ((fset H a b c).card : ℚ) / 4 := by
    rw [div_eq_mul_one_div, ← nsmul_eq_mul, ← sum_const]
    apply sum_congr rfl
    intro z hz
    have hp := (mem_filter.mp hz).2.1
    have hc : (nc H a b c z).card = 1 := by
      have hh := card_le_card (hnc_sub z)
      simp only [card_singleton] at hh
      omega
    rw [hc]; norm_num
  have hBnbeq : nb H b c a d = insert y (fset H a b c) := by
    ext z
    simp only [mem_insert]
    constructor
    · intro hz
      have hzA := (mem_nb.mp hz).1
      have hdB : d ∈ grp H b c a := by rw [hB]; simp
      have hzcn : d ∈ nc H a b c z := by
        rw [mem_nc]
        obtain ⟨_, hzd, hzc⟩ := mem_nb.mp hz
        exact ⟨hdB, hzd, hzc⟩
      by_cases hzy : z = y
      · exact Or.inl hzy
      · exact Or.inr (mem_filter.mpr ⟨hzA, card_pos.mpr ⟨d, hzcn⟩,
          by rw [hbshape z hzA, if_neg hzy, card_empty]⟩)
    · rintro (hzy | hz)
      · subst z
        obtain ⟨hdB, hyd, hcy⟩ := mem_nc.mp (show d ∈ nc H a b c y by rw [hyc]; simp)
        exact mem_nb.mpr ⟨hy, hyd, hcy⟩
      · have hzA := (mem_filter.mp hz).1
        have hp := (mem_filter.mp hz).2.1
        obtain ⟨w, hw⟩ := card_pos.mp hp
        have hwd : w = d := mem_singleton.mp (hnc_sub z hw)
        subst w
        obtain ⟨_, hzd, hcz⟩ := mem_nc.mp hw
        exact mem_nb.mpr ⟨hzA, hzd, hcz⟩
  have hBnbcard : (nb H b c a d).card = 1 + (fset H a b c).card := by
    rw [hBnbeq, card_insert_of_notMem hyf]
    omega
  have htB : tset H b c a = ∅ := by
    ext z
    simp only [tset, mem_filter, notMem_empty, iff_false]
    rintro ⟨hz, _, hzc⟩
    have hzd : z = d := by simpa [hB] using hz
    subst z
    rw [hBnc, card_empty] at hzc
    omega
  have htC : tset H c a b = ∅ := by
    ext z
    simp only [tset, mem_filter, notMem_empty, iff_false]
    rintro ⟨hz, hzb, _⟩
    have hzd : z = d := by simpa [hC] using hz
    subst z
    rw [hCnb, card_empty] at hzb
    omega
  have heA := group_exact hT hH hav
  rw [ht, hg, card_singleton, card_empty, hfcost, sum_empty] at heA
  have heB : groupSigma H b c a + ∑ z ∈ grp H b c a, slotCost H b c a z =
      1/2 + 1/(2 * (2 + ((fset H a b c).card : ℚ))) := by
    rw [groupSigma, hB, card_singleton, sum_singleton, slotCost, hBnbcard, hBnc, card_empty]
    push_cast
    ring
  have heC : groupSigma H c a b + ∑ z ∈ grp H c a b, slotCost H c a b z = 1/2 + 1/4 := by
    rw [groupSigma, hC, card_singleton, sum_singleton, slotCost, hCnb, hCy, card_empty, card_singleton]
    norm_num
  have hc : charge H {a,b,c} =
      RedistArith.F (iset H a b c).card (fset H a b c).card + 1/6 := by
    unfold charge
    rw [sigmaW_slots hT hH, tauW_slots hT hH hav]
    unfold RedistArith.F
    ring_nf at heA heB heC ⊢
    linarith [heA, heB, heC]
  constructor
  · rw [hc]
    linarith [RedistArith.F_nonneg (iset H a b c).card (fset H a b c).card]
  · rw [Lemma1g.card_triangle_options hT hH hav, ht, htB, htC]
    simp

/-- The same Lemma Q conclusion from the actual light links and the two other
base edges of the bicone. The singleton slot hypotheses are derived here. -/
theorem charge_and_options_from_links {a b c d y : V}
    (hT : ({a,b,c} : Finset V) ∈ H)
    (hH : Uniform H) (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hLab : link H {a,b} = {c,d}) (hLac : link H {a,c} = {b,d})
    (hy : y ∈ grp H a b c)
    (hby : ({b,d,y} : Finset V) ∈ H) (hcy : ({c,d,y} : Finset V) ∈ H)
    (hs : (CN H {c,d}).card = 2) :
    (1/6 : ℚ) ≤ charge H {a,b,c} ∧
      ((Lemma1g.options H a b c).filter (Triangular H)).card = 1 := by
  obtain ⟨hbd, _, hdy⟩ := triple_ne (hH _ hby)
  obtain ⟨hcd, _, _⟩ := triple_ne (hH _ hcy)
  have hB : grp H b c a = {d} := by
    simp [grp, pair_comm c a, hLac, hbd]
  have hC : grp H c a b = {d} := by
    simp [grp, hLab, hcd]
  have hyb : nb H a b c y = {d} := by
    apply eq_singleton_iff_unique_mem.mpr
    constructor
    · exact mem_nb.mpr ⟨by rw [hC]; simp, hdy, hby⟩
    · intro z hz
      simpa [hC] using (mem_nb.mp hz).1
  have hyc : nc H a b c y = {d} := by
    apply eq_singleton_iff_unique_mem.mpr
    constructor
    · refine mem_nc.mpr ⟨by rw [hB]; simp, hdy.symm, ?_⟩
      rw [show ({c,y,d} : Finset V) = {c,d,y} from triple_perm (fun t => by tauto)]
      exact hcy
    · intro z hz
      simpa [hB] using (mem_nc.mp hz).1
  exact charge_and_options hT hH hav hB hC hy hyb hyc hs

/-- The both-light branch of Lemma Q, directly from a labelled bicone. This is
the `s_{vw} = 2` orientation; swapping `u,w` gives the other orientation. -/
theorem bicone_both_light {x y u v w : V}
    (hH : Uniform H) (hav : ¬ Erdos643.HypergraphBasics.Forbidden H)
    (hxy : x ≠ y)
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V)))
    (hLxu : link H {x,u} = {v,w}) (hLxw : link H {x,w} = {u,v})
    (hs : (CN H {v,w}).card = 2) :
    (1/6 : ℚ) ≤ charge H {x,u,w} ∧
      ((Lemma1g.options H x u w).filter (Triangular H)).card = 1 := by
  have huv : ({u,v} : Finset V) ∈ CN H {x,y} := by rw [hCN]; simp
  have hvw : ({v,w} : Finset V) ∈ CN H {x,y} := by rw [hCN]; simp
  have huw : ({u,w} : Finset V) ∈ CN H {x,y} := by rw [hCN]; simp
  have hT : ({x,u,w} : Finset V) ∈ H := (mem_CN.mp huw).2.2 x (by simp)
  have hy : y ∈ grp H x u w := by
    rw [grp, mem_erase]
    exact ⟨hxy.symm, (mem_CN_iff_subset_link.mp huw).2 (by simp)⟩
  have hby : ({u,v,y} : Finset V) ∈ H := by
    have hh := (mem_CN.mp huv).2.2 y (by simp)
    rw [show insert y ({u,v} : Finset V) = {u,v,y} from triple_perm (fun t => by tauto)] at hh
    exact hh
  have hcy : ({w,v,y} : Finset V) ∈ H := by
    have hh := (mem_CN.mp hvw).2.2 y (by simp)
    rw [show insert y ({v,w} : Finset V) = {w,v,y} from triple_perm (fun t => by tauto)] at hh
    exact hh
  apply charge_and_options_from_links hT hH hav
    (show link H {x,u} = {w,v} by rw [hLxu, pair_comm v w]) hLxw hy hby hcy
  rw [pair_comm w v]
  exact hs

end Erdos643R3.BothLight
