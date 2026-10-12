/- R883 literal S0001 physical tails.  -/
import R869.Tails
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Finset
namespace Erdos585.QB7S0001R883
open QB4 QB7SmallLobeR643 QB7TwoDegreeFourR676 QB7MixedOmissionR700
  QB7Separator0111R721 QB7Selector0012R751 QB7ProfileFreeR854
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
attribute [local instance] Classical.propDecidable

/-- The equality captures every original lobe neighbor of the saturated pair. -/
structure ThreeTail (G : SimpleGraph V) [DecidableRel G.Adj]
    (U P K S : Finset V) where
  Q : Finset V
  subset : Q ⊆ S.filter (fun s => dg G U s = 6)
  card : #Q = 2
  tail : QB7ProfileFreeR854.PortTail G U P K Q
  captured : ∀ q ∈ Q, dg G tail.X q = dg G P q

omit [DecidableEq V] in
lemma captured_of_saturated {U P K Q : Finset V}
    (t : PortTail G U P K Q) (hsat : ec G P Q = 6) :
    ∀ q ∈ Q, dg G t.X q = dg G P q := by
  have he : ∑ q ∈ Q, dg G t.X q = ∑ q ∈ Q, dg G P q := by
    rw [← ec, ← ec, ec_comm Q t.X, ec_comm Q P, t.ports, hsat]
  have hm : ∀ q ∈ Q, dg G t.X q ≤ dg G P q :=
    fun q _ => dg_mono (G := G) t.left q
  exact (sum_eq_sum_iff_of_le hm).mp he

omit [DecidableEq V] in
lemma ThreeTail.saturated {U P K S : Finset V} (t : ThreeTail G U P K S) :
    ec G P t.Q = 6 := by
  rw [ec_comm]
  unfold ec
  calc (∑ q ∈ t.Q, dg G P q) = ∑ q ∈ t.Q, dg G t.tail.X q :=
        sum_congr rfl fun q hq => (t.captured q hq).symm
    _ = 6 := by rw [← ec, ec_comm]; exact t.tail.ports

lemma ThreeTail.intersection_large {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ ≤ 6) (hs6 : #{s ∈ S | dg G U s = 6} = 3)
    (t t' : ThreeTail G U U₁ W₁ S) : 3 ≤ #(t.tail.X ∩ t'.tail.X) := by
  have hju : t.tail.X ∪ t'.tail.X ⊆ U₁ := union_subset t.tail.left t'.tail.left
  have hQ : t.Q ⊆ S := t.subset.trans (filter_subset _ _)
  have hQ' : t'.Q ⊆ S := t'.subset.trans (filter_subset _ _)
  by_cases heq : t.Q = t'.Q
  · have he : ec G (t.tail.X ∩ t'.tail.X) t.Q = 6 := by
      have hm := ec_left_union_inter (G := G) t.tail.X t'.tail.X t.Q
      have hu := ec_mono_left (G := G) hju t.Q
      have he' : ec G t'.tail.X t.Q = 6 := by
        calc ec G t'.tail.X t.Q = ec G t'.tail.X t'.Q := congrArg (ec G t'.tail.X) heq
             _ = 6 := t'.tail.ports
      rw [t.tail.ports, he'] at hm
      have hi := ec_mono_left (G := G)
        (show t.tail.X ∩ t'.tail.X ⊆ U₁ from inter_subset_left.trans t.tail.left) t.Q
      rw [t.saturated] at hu hi
      omega
    have hp := ec_product_bound (G := G) (t.tail.X ∩ t'.tail.X) t.Q
    rw [t.card, he] at hp
    omega
  have hinter : (t.Q ∩ t'.Q).Nonempty := by
    by_contra hn
    have hz := not_nonempty_iff_eq_empty.mp hn
    have hc := card_union_add_card_inter t.Q t'.Q
    have hb := card_le_card (union_subset t.subset t'.subset)
    rw [hz,card_empty,t.card,t'.card,hs6] at *
    omega
  obtain ⟨s,hs⟩ := hinter
  obtain ⟨hst,hst'⟩ := mem_inter.mp hs
  have hca : #(t.Q.erase s) = 1 := by have := card_erase_add_one hst; rw [t.card] at this; omega
  have hcb : #(t'.Q.erase s) = 1 := by have := card_erase_add_one hst'; rw [t'.card] at this; omega
  obtain ⟨a,ha⟩ := card_eq_one.mp hca
  obtain ⟨b,hb⟩ := card_eq_one.mp hcb
  have hQa : t.Q = insert s {a} := by rw [← ha]; exact (insert_erase hst).symm
  have hQb : t'.Q = insert s {b} := by rw [← hb]; exact (insert_erase hst').symm
  have has : a ≠ s := (mem_erase.mp (ha.symm ▸ mem_singleton_self a)).1
  have hbs : b ≠ s := (mem_erase.mp (hb.symm ▸ mem_singleton_self b)).1
  have hab : a ≠ b := by intro hh; apply heq; rw [hQa,hQb,hh]
  have hsa : a ∈ t.Q := hQa.symm ▸ mem_insert_of_mem (mem_singleton_self a)
  have hsb : b ∈ t'.Q := hQb.symm ▸ mem_insert_of_mem (mem_singleton_self b)
  have hp := lobe_pair_cap_seven h hi hdf
    (show ({a,b} : Finset V) ⊆ S by intro x hx; simp only [mem_insert,mem_singleton] at hx; rcases hx with rfl|rfl; exact hQ hsa; exact hQ' hsb)
    (by simp [hab])
  have hsat := t.saturated
  have hsat' := t'.saturated
  rw [ec_comm] at hp hsat hsat'
  rw [hQa] at hsat
  rw [hQb] at hsat'
  simp [ec, has.symm, hbs.symm, hab] at hp hsat hsat'
  have hdeg : 3 ≤ dg G U₁ s := by omega
  have hsum := dg_union_add_dg_inter (G := G) t.tail.X t'.tail.X s
  have hjcap := dg_mono (G := G) hju s
  have hicard := dg_le_card (G := G) (t.tail.X ∩ t'.tail.X) s
  rw [t.captured s hst,t'.captured s hst'] at hsum
  omega

lemma ThreeTail.union {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ ≤ 6) (hs6 : #{s ∈ S | dg G U s = 6} = 3)
    (t t' : ThreeTail G U U₁ W₁ S) :
    ∃ j : ThreeTail G U U₁ W₁ S,
      j.tail.X = t.tail.X ∪ t'.tail.X ∧ j.tail.B = t.tail.B ∪ t'.tail.B := by
  have hju : t.tail.X ∪ t'.tail.X ⊆ U₁ := union_subset t.tail.left t'.tail.left
  have hji : t.tail.B ∪ t'.tail.B ⊆ W₁ := union_subset t.tail.right t'.tail.right
  have hiu : t.tail.X ∩ t'.tail.X ⊆ U₁ := inter_subset_left.trans t.tail.left
  have hii : t.tail.B ∩ t'.tail.B ⊆ W₁ := inter_subset_left.trans t.tail.right
  have hxi := t.intersection_large h hi hdf hs6 t'
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
    have hu := ec_mono_left (G := G) hju t.Q
    rw [t.tail.ports] at hl
    rw [t.saturated] at hu
    omega
  have hcaptured : ∀ q ∈ t.Q, dg G (t.tail.X ∪ t'.tail.X) q = dg G U₁ q := by
    intro q hq
    have hl := dg_mono (G := G) (subset_union_left : t.tail.X ⊆ t.tail.X ∪ t'.tail.X) q
    have hu := dg_mono (G := G) hju q
    rw [t.captured q hq] at hl
    omega
  exact ⟨⟨t.Q,t.subset,t.card,⟨t.tail.X ∪ t'.tail.X,t.tail.B ∪ t'.tail.B,
    hju,hji,hbalance,htj,hpj⟩,hcaptured⟩,rfl,rfl⟩

noncomputable def tailMarkers (G : SimpleGraph V) [DecidableRel G.Adj]
    (U P K S : Finset V) : Finset V :=
  (deficientMarkers G U K).filter fun z => ∃ t : ThreeTail G U P K S, z ∈ t.tail.B

lemma finite_tail_cover {U W S U₁ U₂ W₁ W₂ A : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ ≤ 6) (hs6 : #{s ∈ S | dg G U s = 6} = 3)
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
    (hdf : df G U W₁ ≤ 6) (hs6 : #{s ∈ S | dg G U s = 6} = 3) :
    df G U (tailMarkers G U U₁ W₁ S) ≤ 2 := by
  rcases (tailMarkers G U U₁ W₁ S).eq_empty_or_nonempty with he|hne
  · simp [he,df]
  · obtain ⟨t,ht⟩ := finite_tail_cover h hi hdf hs6
      (fun z hz => (mem_filter.mp hz).2) hne
    exact (df_le_of_subset (G := G) ht
      (fun y hy => hi.capW y (h.subsets.2.2.1 (t.tail.right hy)))).trans
      (t.tail.deficiency_bound h)

lemma exists_outside_tailMarkers_union {U W S U₁ U₂ W₁ W₂ C : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ ≤ 6) (hs6 : #{s ∈ S | dg G U s = 6} = 3)
    (hC : C ⊆ W₁) (hdC : df G U C ≤ 2) (hlarge : 4 < df G U W₁) :
    ∃ z ∈ W₁, dg G U z < 6 ∧ z ∉ tailMarkers G U U₁ W₁ S ∪ C := by
  let A := tailMarkers G U U₁ W₁ S
  have hA : A ⊆ W₁ := (filter_subset _ _).trans (filter_subset _ _)
  have hbound : df G U A ≤ 2 := tailMarkers_deficiency h hi hdf hs6
  have hnonneg : 0 ≤ df G U (A ∩ C) := df_nonneg fun z hz =>
    hi.capW z (h.subsets.2.2.1 (hC (mem_inter.mp hz).2))
  have hunion : df G U (A ∪ C) ≤ 4 := by
    have he := sum_union_inter (s₁ := A) (s₂ := C) (f := fun z => 6-(dg G U z : ℤ))
    change df G U (A ∪ C) + df G U (A ∩ C) = df G U A + df G U C at he
    omega
  by_contra hn
  push Not at hn
  have hsub : deficientMarkers G U W₁ ⊆ A ∪ C := by
    intro z hz
    exact hn z (mem_filter.mp hz).1 (mem_filter.mp hz).2
  have hd := df_le_of_subset (G := G) hsub (fun z hz =>
    hi.capW z (h.subsets.2.2.1 ((union_subset hA hC) hz)))
  rw [markers_deficiency (fun z hz => hi.capW z (h.subsets.2.2.1 hz))] at hd
  omega

lemma exists_outside_tailMarkers {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hdf : df G U W₁ ≤ 6) (hs6 : #{s ∈ S | dg G U s = 6} = 3)
    (hlarge : 2 < df G U W₁) :
    ∃ z ∈ W₁, dg G U z < 6 ∧ z ∉ tailMarkers G U U₁ W₁ S := by
  have hbound := tailMarkers_deficiency h hi hdf hs6
  by_contra hn
  push Not at hn
  have hsub : deficientMarkers G U W₁ ⊆ tailMarkers G U U₁ W₁ S := by
    intro z hz
    exact hn z (mem_filter.mp hz).1 (mem_filter.mp hz).2
  have hd := df_le_of_subset (G := G) hsub
    (fun z hz => hi.capW z (h.subsets.2.2.1 (mem_filter.mp (mem_filter.mp hz).1).1))
  rw [markers_deficiency (fun z hz => hi.capW z (h.subsets.2.2.1 hz))] at hd
  omega

#print axioms captured_of_saturated
#print axioms ThreeTail.intersection_large
#print axioms ThreeTail.union
#print axioms tailMarkers_deficiency
#print axioms exists_outside_tailMarkers_union
#print axioms exists_outside_tailMarkers
end Erdos585.QB7S0001R883
