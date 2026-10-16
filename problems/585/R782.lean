import R751
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.QB7Weighted0012R782
open QB4 QB7SmallLobeR643 QB7TwoDegreeFourR676 QB7MixedOmissionR700 QB7Separator0111R721 QB7Selector0012R751
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The original right deficiency of a tight imbalance-two tail is at most two.
The difference from two is precisely the original inward leakage. -/
lemma PortTail.original_deficiency_le_two {U W S U₁ U₂ W₁ W₂ Q : Finset V} {u0 : V}
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (t : PortTail G U U₁ W₁ Q u0) : df G U t.B ≤ 2 := by
  have hm := ec_mono_left (G := G) (t.left.trans h.subsets.1) t.B
  have he := df_eq (G := G) U t.B
  rw [ec_comm t.B U] at he
  have hp := t.potential
  have hb := t.balance
  unfold gv at hp
  omega

/-- Weighted exclusion is local: an original degree-five marker inside a tight
mass-two tail excludes every original degree-four vertex from that tail. -/
lemma PortTail.local_min_five {U W S U₁ U₂ W₁ W₂ Q : Finset V} {u0 z : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (t : PortTail G U U₁ W₁ Q u0) (hz : z ∈ t.B) (hdz : dg G U z = 5) :
    ∀ y ∈ t.B, 5 ≤ dg G U y := by
  have hb := PortTail.original_deficiency_le_two h t
  have he : df G U (t.B.erase z)+(6-(dg G U z : ℤ)) = df G U t.B :=
    sum_erase_add t.B (fun y => 6-(dg G U y : ℤ)) hz
  rw [hdz] at he
  have herase : df G U (t.B.erase z) ≤ 1 := by omega
  intro y hy
  by_cases hyz : y = z
  · simp [hyz,hdz]
  have hye : y ∈ t.B.erase z := mem_erase.mpr ⟨hyz,hy⟩
  have hl := df_le_of_subset (G := G) (singleton_subset_iff.mpr hye)
    (fun x hx => hi.capW x (h.subsets.2.2.1 (t.right (mem_erase.mp hx).2)))
  simp only [df,sum_singleton] at hl
  change (6-(dg G U y : ℤ)) ≤ df G U (t.B.erase z) at hl
  omega

lemma PortTail.weighted_marker_bound {U W S U₁ U₂ W₁ W₂ Q : Finset V} {u0 : V}
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hw : ∀ y ∈ W₁, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (t : PortTail G U U₁ W₁ Q u0) : #{y ∈ t.B | dg G U y = 5} ≤ 2 := by
  have hd := df_four_five_six (fun y hy => hw y (t.right hy))
  have hb := PortTail.original_deficiency_le_two h t
  omega

attribute [local instance] Classical.propDecidable

/-- No host minimum-five premise: both original interior deficiencies are five. -/
theorem original_weighted0012_at_most_two
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₂ : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hdf₁ : df G U W₁ = 5) (hdf₂ : df G U W₂ = 5)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hz₂ : z₂ ∈ W₂) (hd₂ : dg G U z₂ = 4) :
    #{z ∈ W₁ | dg G U z = 5 ∧ ¬ FixedOmissionFactor G U W z z₂} ≤ 2 := by
  classical
  have hi' := U2Input.of_original hi
  by_contra hn
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := two_lt_card_iff.mp (by omega :
    2 < #{z ∈ W₁ | dg G U z = 5 ∧ ¬ FixedOmissionFactor G U W z z₂})
  rcases mem_filter.mp ha with ⟨haW,haD,haF⟩
  rcases mem_filter.mp hb with ⟨hbW,hbD,hbF⟩
  rcases mem_filter.mp hc with ⟨hcW,hcD,hcF⟩
  obtain ⟨ta,hta⟩ := failed_pair_port_tail h hi' hu hdu hdf₁ hdf₂ hs6 haW hz₂ haD hd₂ haF
  obtain ⟨tb,htb⟩ := failed_pair_port_tail h hi' hu hdu hdf₁ hdf₂ hs6 hbW hz₂ hbD hd₂ hbF
  obtain ⟨tc,htc⟩ := failed_pair_port_tail h hi' hu hdu hdf₁ hdf₂ hs6 hcW hz₂ hcD hd₂ hcF
  -- The weighted exclusion applies separately to every actual failed tail.
  have _hmina := PortTail.local_min_five h hi' ta hta haD
  have _hminb := PortTail.local_min_five h hi' tb htb hbD
  have _hminc := PortTail.local_min_five h hi' tc htc hcD
  obtain ⟨tab,_,htab⟩ := ta.union h hi' hdf₁ (filter_subset _ _) hs6 tb
  obtain ⟨tabc,_,htabc⟩ := tab.union h hi' hdf₁ (filter_subset _ _) hs6 tc
  have hbound := PortTail.weighted_marker_bound h hw₁ tabc
  have hsub : {a,b,c} ⊆ tabc.B.filter (fun z => dg G U z = 5) := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl|rfl
    · exact mem_filter.mpr ⟨by rw [htabc,htab]; exact mem_union_left _ (mem_union_left _ hta),haD⟩
    · exact mem_filter.mpr ⟨by rw [htabc,htab]; exact mem_union_left _ (mem_union_right _ htb),hbD⟩
    · exact mem_filter.mpr ⟨by rw [htabc]; exact mem_union_right _ htc,hcD⟩
  have hthree : #({a,b,c} : Finset V) = 3 := by simp [hab,hac,hbc]
  have hh := card_le_card hsub
  omega

/-- The same fixed omission works across all cuts. -/
theorem original_weighted0012_count
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₂ : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hdf₁ : df G U W₁ = 5) (hdf₂ : df G U W₂ = 5)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hz₂ : z₂ ∈ W₂) (hd₂ : dg G U z₂ = 4) :
    #{z ∈ W₁ | dg G U z = 5 ∧ ¬ FixedOmissionFactor G U W z z₂} ≤ 2 ∧
    #{z ∈ W₁ | dg G U z = 5}-2 ≤
      #{z ∈ W₁ | dg G U z = 5 ∧ FixedOmissionFactor G U W z z₂} := by
  have hb := original_weighted0012_at_most_two hi h hu hdu hs6 hdf₁ hdf₂ hw₁ hz₂ hd₂
  have he := card_filter_add_card_filter_not
    (s := W₁.filter fun z => dg G U z = 5) (fun z => FixedOmissionFactor G U W z z₂)
  simp only [filter_filter] at he
  exact ⟨hb,by omega⟩

/-- Literal original profile caller for all four broad cells. -/
theorem original_weighted0012_broad
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₂ : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (_hn₁ : 6 ≤ #U₁) (_hn₂ : 6 ≤ #U₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (_hs : ∀ s ∈ S, dg G U s = 4 ∨ dg G U s = 5 ∨ dg G U s = 6)
    (_hs4 : #{s ∈ S | dg G U s = 4} = 1)
    (_hs5 : #{s ∈ S | dg G U s = 5} = 1)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c : (#{y ∈ W₁ | dg G U y = 4} = 0 ∧ #{y ∈ W₁ | dg G U y = 5} = 5) ∨
      (#{y ∈ W₁ | dg G U y = 4} = 1 ∧ #{y ∈ W₁ | dg G U y = 5} = 3))
    (hw₂ : ∀ y ∈ W₂, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c : (#{y ∈ W₂ | dg G U y = 4} = 1 ∧ #{y ∈ W₂ | dg G U y = 5} = 3) ∨
      (#{y ∈ W₂ | dg G U y = 4} = 2 ∧ #{y ∈ W₂ | dg G U y = 5} = 1))
    (hz₂ : z₂ ∈ W₂) (hd₂ : dg G U z₂ = 4) :
    #{z ∈ W₁ | dg G U z = 5 ∧ ¬ FixedOmissionFactor G U W z z₂} ≤ 2 ∧
    #{z ∈ W₁ | dg G U z = 5}-2 ≤
      #{z ∈ W₁ | dg G U z = 5 ∧ FixedOmissionFactor G U W z z₂} ∧
    ∃ z ∈ W₁, dg G U z = 5 ∧ FixedOmissionFactor G U W z z₂ := by
  have hdf₁ : df G U W₁ = 5 := by
    rw [df_four_five_six hw₁]
    rcases hw₁c with ⟨h4,h5⟩|⟨h4,h5⟩ <;> rw [h4,h5] <;> norm_num
  have hdf₂ : df G U W₂ = 5 := by
    rw [df_four_five_six hw₂]
    rcases hw₂c with ⟨h4,h5⟩|⟨h4,h5⟩ <;> rw [h4,h5] <;> norm_num
  have hh := original_weighted0012_count hi h hu hdu hs6 hdf₁ hdf₂ hw₁ hz₂ hd₂
  have hm : 3 ≤ #{y ∈ W₁ | dg G U y = 5} := by
    rcases hw₁c with ⟨_,h5⟩|⟨_,h5⟩ <;> omega
  have hn : 0 < #{z ∈ W₁ | dg G U z = 5 ∧ FixedOmissionFactor G U W z z₂} := by omega
  obtain ⟨z,hz⟩ := card_pos.mp hn
  exact ⟨hh.1,hh.2,z,(mem_filter.mp hz).1,(mem_filter.mp hz).2⟩

/-- The narrow unique-four / three-five cell, against its fixed degree-four z2. -/
theorem original_weighted0012_narrow
    {U W S U₁ U₂ W₁ W₂ : Finset V} {u0 z₂ : V}
    (hi : QB7Conditional.U2Input G U W)
    (h : Split G U W S U₁ U₂ W₁ W₂)
    (hn₁ : 6 ≤ #U₁) (hn₂ : 6 ≤ #U₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hs : ∀ s ∈ S, dg G U s = 4 ∨ dg G U s = 5 ∨ dg G U s = 6)
    (hs4 : #{s ∈ S | dg G U s = 4} = 1)
    (hs5 : #{s ∈ S | dg G U s = 5} = 1)
    (hs6 : #{s ∈ S | dg G U s = 6} = 2)
    (hw₁ : ∀ y ∈ W₁, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hw₁c₄ : #{y ∈ W₁ | dg G U y = 4} = 1)
    (hw₁c₅ : #{y ∈ W₁ | dg G U y = 5} = 3)
    (hw₂ : ∀ y ∈ W₂, dg G U y = 4 ∨ dg G U y = 5 ∨ dg G U y = 6)
    (hw₂c₄ : #{y ∈ W₂ | dg G U y = 4} = 1)
    (hw₂c₅ : #{y ∈ W₂ | dg G U y = 5} = 3)
    (hz₂ : z₂ ∈ W₂) (hd₂ : dg G U z₂ = 4) :
    #{z ∈ W₁ | dg G U z = 5 ∧ ¬ FixedOmissionFactor G U W z z₂} ≤ 2 ∧
    1 ≤ #{z ∈ W₁ | dg G U z = 5 ∧ FixedOmissionFactor G U W z z₂} ∧
    ∃ z ∈ W₁, dg G U z = 5 ∧ FixedOmissionFactor G U W z z₂ := by
  have hh := original_weighted0012_broad hi h hn₁ hn₂ hu hdu hs hs4 hs5 hs6
    hw₁ (Or.inr ⟨hw₁c₄,hw₁c₅⟩) hw₂ (Or.inl ⟨hw₂c₄,hw₂c₅⟩) hz₂ hd₂
  rw [hw₁c₅] at hh
  exact ⟨hh.1,by omega,hh.2.2⟩

#print axioms PortTail.original_deficiency_le_two
#print axioms PortTail.local_min_five
#print axioms PortTail.weighted_marker_bound
#print axioms original_weighted0012_at_most_two
#print axioms original_weighted0012_count
#print axioms original_weighted0012_broad
#print axioms original_weighted0012_narrow
end Erdos585.QB7Weighted0012R782
