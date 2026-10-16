/- R869 S0002 formalization.  -/
import R854.ProfileFree
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Finset
namespace Erdos585.QB7S0002R869
open QB4 QB7SmallLobeR643 QB7TwoDegreeFourR676 QB7MixedOmissionR700
  QB7Separator0111R721 QB7Selector0012R751 QB7ProfileFreeR854
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

/-- Original anchored tight tail on either deficiency-five lobe. -/
structure ThreeTail (G : SimpleGraph V) [DecidableRel G.Adj]
    (U P K S : Finset V) where
  Q : Finset V
  subset : Q ⊆ S.filter (fun s => dg G U s = 6)
  card : #Q = 2
  tail : QB7ProfileFreeR854.PortTail G U P K Q

lemma ThreeTail.union {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ = 5) (hs6 : #{s ∈ S | dg G U s = 6} = 3)
    (t t' : ThreeTail G U U₁ W₁ S) :
    ∃ j : ThreeTail G U U₁ W₁ S,
      j.tail.X = t.tail.X ∪ t'.tail.X ∧ j.tail.B = t.tail.B ∪ t'.tail.B := by
  have hQ : t.Q ⊆ S := t.subset.trans (filter_subset _ _)
  have hQ' : t'.Q ⊆ S := t'.subset.trans (filter_subset _ _)
  have hcap : ∀ s ∈ S, dg G U₁ s ≤ 3 := fun s hs => original_lobe_port_cap h hi hdf hs
  have hju : t.tail.X ∪ t'.tail.X ⊆ U₁ := union_subset t.tail.left t'.tail.left
  have hji : t.tail.B ∪ t'.tail.B ⊆ W₁ := union_subset t.tail.right t'.tail.right
  have hiu : t.tail.X ∩ t'.tail.X ⊆ U₁ := inter_subset_left.trans t.tail.left
  have hii : t.tail.B ∩ t'.tail.B ⊆ W₁ := inter_subset_left.trans t.tail.right
  have hinter : (t.Q ∩ t'.Q).Nonempty := by
    by_contra hn
    have hzero : t.Q ∩ t'.Q = ∅ := not_nonempty_iff_eq_empty.mp hn
    have hc := card_union_add_card_inter t.Q t'.Q
    have hb := card_le_card (union_subset t.subset t'.subset)
    rw [hzero,card_empty,t.card,t'.card,hs6] at *
    omega
  obtain ⟨s,hs⟩ := hinter
  have hs₁ := (mem_inter.mp hs).1
  have hs₂ := (mem_inter.mp hs).2
  have hdeg : ∀ (a : ThreeTail G U U₁ W₁ S), ∀ s ∈ a.Q, dg G a.tail.X s = 3 := by
    intro a s hsa
    have hQa : a.Q ⊆ S := a.subset.trans (filter_subset _ _)
    have hm : ∀ q ∈ a.Q, dg G a.tail.X q ≤ 3 :=
      fun q hq => (dg_mono (G := G) a.tail.left q).trans (hcap q (hQa hq))
    have he : ∑ q ∈ a.Q, dg G a.tail.X q = 6 := by
      rw [← ec,ec_comm]; exact a.tail.ports
    have herase := sum_erase_add a.Q (fun q => dg G a.tail.X q) hsa
    have hbound : ∑ q ∈ a.Q.erase s, dg G a.tail.X q ≤ 3 := by
      calc _ ≤ ∑ _q ∈ a.Q.erase s, 3 := sum_le_sum fun q hq => hm q (mem_erase.mp hq).2
        _ = 3 := by have hc := card_erase_add_one hsa; rw [a.card] at hc; simp; omega
    have := hm s hsa
    omega
  have hds := hdeg t s hs₁
  have hds' := hdeg t' s hs₂
  have hsum := dg_union_add_dg_inter (G := G) t.tail.X t'.tail.X s
  have hjcap := (dg_mono (G := G) hju s).trans (hcap s (hQ hs₁))
  have hicard := dg_le_card (G := G) (t.tail.X ∩ t'.tail.X) s
  have hxi : 3 ≤ #(t.tail.X ∩ t'.tail.X) := by omega
  have hxt := card_le_card (inter_subset_left : t.tail.X ∩ t'.tail.X ⊆ t.tail.X)
  have hxj := card_le_card (subset_union_left : t.tail.X ⊆ t.tail.X ∪ t'.tail.X)
  have hbj := card_le_card (subset_union_left : t.tail.B ⊆ t.tail.B ∪ t'.tail.B)
  have hbal := t.tail.balance
  have hfj := h.local_floor hi hju (hji.trans subset_union_left) (by omega)
  have hsub := gv_union_add_gv_inter_le (G := G) t.tail.X t'.tail.X t.tail.B t'.tail.B
  rw [t.tail.potential,t'.tail.potential] at hsub
  have hni : 4 ≤ #(t.tail.X ∩ t'.tail.X)+#(t.tail.B ∩ t'.tail.B) := by
    by_contra hn
    have hz : #(t.tail.B ∩ t'.tail.B) = 0 := by omega
    have hx : #(t.tail.X ∩ t'.tail.X) = 3 := by omega
    have hempty := card_eq_zero.mp hz
    have h18 : gv G (t.tail.X ∩ t'.tail.X) (t.tail.B ∩ t'.tail.B) = 18 := by
      simp [gv,hempty,ec,dg,hx]
    omega
  have hfi := h.local_floor hi hiu (hii.trans subset_union_left) hni
  have htj : gv G (t.tail.X ∪ t'.tail.X) (t.tail.B ∪ t'.tail.B) = 16 := by omega
  have hti : gv G (t.tail.X ∩ t'.tail.X) (t.tail.B ∩ t'.tail.B) = 16 := by omega
  have hbj2 := tight_balance_le_two hi (hju.trans h.subsets.1) (hji.trans h.subsets.2.2.1) htj
  have hbi2 := tight_balance_le_two hi (hiu.trans h.subsets.1) (hii.trans h.subsets.2.2.1) hti
  have hxcard := card_union_add_card_inter t.tail.X t'.tail.X
  have hbcard := card_union_add_card_inter t.tail.B t'.tail.B
  have hbal' := t'.tail.balance
  have hbalance : (#(t.tail.X ∪ t'.tail.X) : ℤ)-#(t.tail.B ∪ t'.tail.B) = 2 := by omega
  have hpj : ec G (t.tail.X ∪ t'.tail.X) t.Q = 6 := by
    have hl := ec_mono_left (G := G) (subset_union_left : t.tail.X ⊆ t.tail.X ∪ t'.tail.X) t.Q
    have hu := (ec_mono_left (G := G) hju t.Q).trans (lobe_pair_cap h hi hdf hQ t.card)
    rw [t.tail.ports] at hl
    omega
  exact ⟨⟨t.Q,t.subset,t.card,⟨t.tail.X ∪ t'.tail.X,t.tail.B ∪ t'.tail.B,
    hju,hji,hbalance,htj,hpj⟩⟩,rfl,rfl⟩


noncomputable def tailMarkers (G : SimpleGraph V) [DecidableRel G.Adj]
    (U P K S : Finset V) : Finset V :=
  (deficientMarkers G U K).filter fun z => ∃ t : ThreeTail G U P K S, z ∈ t.tail.B

lemma finite_tail_cover {U W S U₁ U₂ W₁ W₂ A : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ = 5) (hs6 : #{s ∈ S | dg G U s = 6} = 3)
    (ha : ∀ z ∈ A, ∃ t : ThreeTail G U U₁ W₁ S, z ∈ t.tail.B)
    (hne : A.Nonempty) : ∃ t : ThreeTail G U U₁ W₁ S, A ⊆ t.tail.B := by
  induction A using Finset.induction_on with
  | empty => simp at hne
  | @insert a A haA ih =>
    obtain ⟨ta,hza⟩ := ha a (mem_insert_self a A)
    rcases A.eq_empty_or_nonempty with rfl|hA
    · exact ⟨ta,by simpa using (singleton_subset_iff.mpr hza)⟩
    · obtain ⟨tb,hzb⟩ := ih (fun z hz => ha z (mem_insert_of_mem hz)) hA
      obtain ⟨t,_,htB⟩ := ta.union h hi hdf hs6 tb
      refine ⟨t,?_⟩
      rw [htB]
      exact insert_subset (mem_union_left _ hza) (hzb.trans subset_union_right)

lemma tailMarkers_deficiency {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ = 5) (hs6 : #{s ∈ S | dg G U s = 6} = 3) :
    df G U (tailMarkers G U U₁ W₁ S) ≤ 2 := by
  rcases (tailMarkers G U U₁ W₁ S).eq_empty_or_nonempty with he|hne
  · simp [he,df]
  · obtain ⟨t,ht⟩ := finite_tail_cover h hi hdf hs6
      (fun z hz => (mem_filter.mp hz).2) hne
    exact (df_le_of_subset (G := G) ht
      (fun y hy => hi.capW y (h.subsets.2.2.1 (t.tail.right hy)))).trans
      (t.tail.deficiency_bound h)

lemma exists_outside_tailMarkers {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ = 5) (hs6 : #{s ∈ S | dg G U s = 6} = 3) :
    ∃ z ∈ W₁, dg G U z < 6 ∧ z ∉ tailMarkers G U U₁ W₁ S := by
  have hbound := tailMarkers_deficiency h hi hdf hs6
  by_contra hn
  push Not at hn
  have hsub : deficientMarkers G U W₁ ⊆ tailMarkers G U U₁ W₁ S := by
    intro z hz
    exact hn z (mem_filter.mp hz).1 (mem_filter.mp hz).2
  have hd := df_le_of_subset (G := G) hsub
    (fun z hz => hi.capW z (h.subsets.2.2.1 (mem_filter.mp (mem_filter.mp hz).1).1))
  rw [markers_deficiency (fun z hz => hi.capW z (h.subsets.2.2.1 hz)),hdf] at hd
  omega

#print axioms ThreeTail.union
#print axioms exists_outside_tailMarkers
end Erdos585.QB7S0002R869
