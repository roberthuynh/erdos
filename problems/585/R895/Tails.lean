import R854.ProfileFree
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Finset
namespace Erdos585.QB7S0000R895
open QB4 QB7SmallLobeR643 QB7Selector0012R751 QB7ProfileFreeR854
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

/-- An original scarred tight tail, allowing degree-four and degree-five markers. -/
structure ScarTail (G : SimpleGraph V) [DecidableRel G.Adj]
    (U P L : Finset V) (u0 : V) where
  X : Finset V
  B : Finset V
  left : X ⊆ P
  right : B ⊆ L
  balance : (#X : ℤ)-#B = 2
  potential : gv G X B = 16
  scar : u0 ∈ X
  marker : ∃ z ∈ B, dg G U z < 6

omit [DecidableEq V] in
lemma ScarTail.mass {U P L : Finset V} {u0 : V} (t : ScarTail G U P L u0) :
    df G t.X t.B = 2 := by
  have hh := gv_eq_left (G := G) t.X t.B
  rw [t.potential] at hh
  have hb := t.balance
  omega

lemma ScarTail.large {U W S P P' L L' : Finset V} {u0 : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (t : ScarTail G U P L u0) : 4 ≤ #t.X ∧ 1 ≤ #t.B := by
  obtain ⟨z,hz,hdz⟩ := t.marker
  have hs := df_le_of_subset (G := G) (singleton_subset_iff.mpr hz)
    (fun y hy => (dg_mono (G := G) (t.left.trans h.subsets.1) y).trans
      (hi.capW y (h.subsets.2.2.1 (t.right hy))))
  simp only [df,sum_singleton] at hs
  change 6-(dg G t.X z : ℤ) ≤ df G t.X t.B at hs
  rw [t.mass] at hs
  have hc := dg_le_card (G := G) t.X z
  exact ⟨by omega,card_pos.mpr ⟨z,hz⟩⟩

lemma ScarTail.scar_neighbors {U W S P P' L L' : Finset V} {u0 : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (t : ScarTail G U P L u0) : 3 ≤ dg G t.B u0 := by
  obtain ⟨hx,hb⟩ := t.large h hi
  have hc := card_erase_add_one t.scar
  have hf := h.local_floor hi ((erase_subset u0 t.X).trans t.left)
    (t.right.trans subset_union_left) (by omega)
  have he := gv_erase_left (G := G) t.scar t.B
  rw [t.potential] at he
  omega

lemma ScarTail.intersection_large {U W S P P' L L' : Finset V} {u0 : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hdu : dg G W u0 = 5) (t t' : ScarTail G U P L u0) :
    4 ≤ #(t.X ∩ t'.X)+#(t.B ∩ t'.B) := by
  have hxn : 1 ≤ #(t.X ∩ t'.X) := card_pos.mpr ⟨u0,mem_inter.mpr ⟨t.scar,t'.scar⟩⟩
  have hbn : 1 ≤ #(t.B ∩ t'.B) := by
    have ht := t.scar_neighbors h hi
    have ht' := t'.scar_neighbors h hi
    have he := dg_union_add_dg_inter (G := G) t.B t'.B u0
    have hm := dg_mono (G := G)
      ((union_subset t.right t'.right).trans h.subsets.2.2.1) u0
    rw [hdu] at hm
    have hc := dg_le_card (G := G) (t.B ∩ t'.B) u0
    omega
  have hsub := gv_union_add_gv_inter_le (G := G) t.X t'.X t.B t'.B
  rw [t.potential,t'.potential] at hsub
  have hiid := gv_eq_left (G := G) (t.X ∩ t'.X) (t.B ∩ t'.B)
  have hjid := gv_eq_left (G := G) (t.X ∪ t'.X) (t.B ∪ t'.B)
  have hxc := card_union_add_card_inter t.X t'.X
  have hbc := card_union_add_card_inter t.B t'.B
  have hbal := t.balance
  have hbal' := t'.balance
  have hmass : df G (t.X ∩ t'.X) (t.B ∩ t'.B) +
      df G (t.X ∪ t'.X) (t.B ∪ t'.B) ≤ 4 := by omega
  have hmassj : 1 ≤ df G (t.X ∪ t'.X) (t.B ∪ t'.B) := by
    obtain ⟨z,hz,hdz⟩ := t.marker
    have hm := dg_mono (G := G)
      ((union_subset t.left t'.left).trans h.subsets.1) z
    have hs := df_le_of_subset (G := G)
      (singleton_subset_iff.mpr (mem_union_left t'.B hz))
      (fun y hy => (dg_mono (G := G)
        ((union_subset t.left t'.left).trans h.subsets.1) y).trans
        (hi.capW y (h.subsets.2.2.1 ((union_subset t.right t'.right) hy))))
    simp only [df,sum_singleton] at hs
    change 6-(dg G (t.X ∪ t'.X) z : ℤ) ≤ df G (t.X ∪ t'.X) (t.B ∪ t'.B) at hs
    omega
  by_contra hn
  have hc := ec_product_bound (G := G) (t.X ∩ t'.X) (t.B ∩ t'.B)
  have hid := df_eq (G := G) (t.X ∩ t'.X) (t.B ∩ t'.B)
  rw [ec_comm] at hid
  have hcases : (#(t.X ∩ t'.X) = 1 ∧ #(t.B ∩ t'.B) = 1) ∨
      (#(t.X ∩ t'.X) = 1 ∧ #(t.B ∩ t'.B) = 2) ∨
      (#(t.X ∩ t'.X) = 2 ∧ #(t.B ∩ t'.B) = 1) := by omega
  rcases hcases with ⟨hx,hb⟩|⟨hx,hb⟩|⟨hx,hb⟩ <;>
    rw [hx,hb] at hc <;> rw [hb] at hid <;> norm_num at hc hid <;> omega

lemma ScarTail.union {U W S P P' L L' : Finset V} {u0 : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W)
    (hdu : dg G W u0 = 5) (t t' : ScarTail G U P L u0) :
    ∃ j : ScarTail G U P L u0, j.X = t.X ∪ t'.X ∧ j.B = t.B ∪ t'.B := by
  have hju := union_subset t.left t'.left
  have hjb := union_subset t.right t'.right
  have hiu : t.X ∩ t'.X ⊆ P := inter_subset_left.trans t.left
  have hib : t.B ∩ t'.B ⊆ L := inter_subset_left.trans t.right
  have hlarge := t.intersection_large h hi hdu t'
  have hcx := card_le_card (show t.X ∩ t'.X ⊆ t.X ∪ t'.X from inter_subset_left.trans subset_union_left)
  have hcb := card_le_card (show t.B ∩ t'.B ⊆ t.B ∪ t'.B from inter_subset_left.trans subset_union_left)
  have hfj := h.local_floor hi hju (hjb.trans subset_union_left) (by omega)
  have hfi := h.local_floor hi hiu (hib.trans subset_union_left) hlarge
  have hsub := gv_union_add_gv_inter_le (G := G) t.X t'.X t.B t'.B
  rw [t.potential,t'.potential] at hsub
  have hj : gv G (t.X ∪ t'.X) (t.B ∪ t'.B) = 16 := by omega
  have hi' : gv G (t.X ∩ t'.X) (t.B ∩ t'.B) = 16 := by omega
  have hbj := tight_balance_le_two hi (hju.trans h.subsets.1) (hjb.trans h.subsets.2.2.1) hj
  have hbi := tight_balance_le_two hi (hiu.trans h.subsets.1) (hib.trans h.subsets.2.2.1) hi'
  have hxc := card_union_add_card_inter t.X t'.X
  have hbc := card_union_add_card_inter t.B t'.B
  have hbal := t.balance
  have hbal' := t'.balance
  have hb : (#(t.X ∪ t'.X) : ℤ)-#(t.B ∪ t'.B) = 2 := by omega
  obtain ⟨z,hz,hdz⟩ := t.marker
  exact ⟨⟨t.X ∪ t'.X,t.B ∪ t'.B,hju,hjb,hb,hj,mem_union_left _ t.scar,
    z,mem_union_left _ hz,hdz⟩,rfl,rfl⟩

noncomputable def tailMarkers (G : SimpleGraph V) [DecidableRel G.Adj]
    (U P L : Finset V) (u0 : V) : Finset V :=
  (deficientMarkers G U L).filter fun z => ∃ t : ScarTail G U P L u0, z ∈ t.B

lemma finite_tail_cover {U W S P P' L L' A : Finset V} {u0 : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W) (hdu : dg G W u0 = 5)
    (ha : ∀ z ∈ A, ∃ t : ScarTail G U P L u0, z ∈ t.B)
    (hne : A.Nonempty) : ∃ t : ScarTail G U P L u0, A ⊆ t.B := by
  induction A using Finset.induction_on with
  | empty => simp at hne
  | @insert a A haA ih =>
    obtain ⟨ta,hza⟩ := ha a (mem_insert_self a A)
    rcases A.eq_empty_or_nonempty with rfl|hA
    · exact ⟨ta,by simpa using (singleton_subset_iff.mpr hza)⟩
    · obtain ⟨tb,hzb⟩ := ih (fun z hz => ha z (mem_insert_of_mem hz)) hA
      obtain ⟨t,_,htB⟩ := ta.union h hi hdu tb
      refine ⟨t,?_⟩
      rw [htB]
      exact insert_subset (mem_union_left _ hza) (hzb.trans subset_union_right)

omit [DecidableEq V] in
lemma tailMarkers_subset (U P L : Finset V) (u0 : V) :
    tailMarkers G U P L u0 ⊆ deficientMarkers G U L := filter_subset _ _

lemma tailMarkers_deficiency {U W S P P' L L' : Finset V} {u0 : V}
    (h : Split G U W S P P' L L') (hi : U2Input G U W) (hdu : dg G W u0 = 5) :
    df G U (tailMarkers G U P L u0) ≤ 2 := by
  rcases (tailMarkers G U P L u0).eq_empty_or_nonempty with he|hne
  · simp [he,df]
  · obtain ⟨t,ht⟩ := finite_tail_cover h hi hdu (fun z hz => (mem_filter.mp hz).2) hne
    have hm := df_le_of_subset (G := G) ht
      (fun y hy => hi.capW y (h.subsets.2.2.1 (t.right hy)))
    have hdeg : df G U t.B ≤ df G t.X t.B := by
      unfold df
      apply sum_le_sum
      intro y hy
      have hh := dg_mono (G := G) (t.left.trans h.subsets.1) y
      omega
    rw [t.mass] at hdeg
    exact hm.trans hdeg

#print axioms ScarTail.intersection_large
#print axioms ScarTail.union
#print axioms tailMarkers_deficiency
end Erdos585.QB7S0000R895
