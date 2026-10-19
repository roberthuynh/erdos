import Openmath.Erdos643R3.Lemma1g

set_option autoImplicit false
namespace Erdos643R3.G1Bicone
open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.WeightingBound
  Erdos643R3.SlotModel Erdos643R3.Lemma1g Erdos643R3.L1Top
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

/-- A slot option contains the original triple in its witness set. -/
theorem mem_bicone_of_slot {a b c z : V}
    (hT : ({a,b,c} : Finset V) ∈ H) (hH : Uniform H) (hz : z ∈ grp H a b c) :
    ({a,b,c} : Finset V) ∈ bicone H {a,z} := by
  exact mem_bicone.mpr ⟨{b,c}, base_mem_CN hT hH hz, a, by simp, rfl⟩

/-- Recover a slot from a witness triple with a fixed apex. -/
theorem slot_of_witness {a b c z : V} (hab : a ≠ b) (hac : a ≠ c) (hza : z ≠ a)
    {P : Finset V} (hP : P ∈ CN H {a,z}) (he : insert a P = ({a,b,c} : Finset V)) :
    z ∈ grp H a b c := by
  obtain ⟨-, hd, -, hz⟩ := mem_CN_pair.mp hP
  have haP : a ∉ P := fun ha => not_mem_of_inter_empty hd ha (by simp)
  have ep : P = ({b,c} : Finset V) := by
    have e := congrArg (fun s : Finset V => s.erase a) he
    simpa [haP, hab, hac] using e
  rw [ep] at hd hz
  refine mem_grp.mpr ⟨hza, ?_, ?_, hz⟩
  · intro h; exact not_mem_of_inter_empty (t := z) hd (by simp [h]) (by simp)
  · intro h; exact not_mem_of_inter_empty (t := z) hd (by simp [h]) (by simp)

/-- For any pair q, T is in its witness set exactly when q is an option of T. -/
theorem mem_bicone_iff_option {a b c : V} {q : Finset V}
    (hT : ({a,b,c} : Finset V) ∈ H) (hH : Uniform H) (hq : q.card = 2) :
    ({a,b,c} : Finset V) ∈ bicone H q ↔ q ∈ options H a b c := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  constructor
  · intro h
    obtain ⟨P, hP, x, hx, he⟩ := mem_bicone.mp h
    have hxT : x ∈ ({a,b,c} : Finset V) := by rw [← he]; simp
    obtain ⟨z, hzx, rfl⟩ := exists_eq_pair_of_mem hq hx
    simp only [mem_insert, mem_singleton] at hxT
    unfold options
    rcases hxT with hxa | hxb | hxc
    · subst x
      exact mem_union_left _ (mem_union_left _
        (mem_image.mpr ⟨z, slot_of_witness hab hac hzx hP he, rfl⟩))
    · subst x
      have he' : insert b P = ({b,c,a} : Finset V) := by
        rw [he]; exact triple_perm (fun t => by tauto)
      exact mem_union_left _ (mem_union_right _
        (mem_image.mpr ⟨z, slot_of_witness hbc hab.symm hzx hP he', rfl⟩))
    · subst x
      have he' : insert c P = ({c,a,b} : Finset V) := by
        rw [he]; exact triple_perm (fun t => by tauto)
      exact mem_union_right _
        (mem_image.mpr ⟨z, slot_of_witness hac.symm hbc.symm hzx hP he', rfl⟩)
  · intro h
    simp only [options, mem_union, mem_image] at h
    rcases h with (⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩) | ⟨z,hz,rfl⟩
    · exact mem_bicone_of_slot hT hH hz
    · have := mem_bicone_of_slot (triple_rot hT) hH hz
      rwa [show ({b,c,a} : Finset V) = {a,b,c} from triple_perm (fun t => by tauto)] at this
    · have := mem_bicone_of_slot (triple_rot (triple_rot hT)) hH hz
      rwa [show ({c,a,b} : Finset V) = {a,b,c} from triple_perm (fun t => by tauto)] at this

/-- Active bicones containing a triple are among its triangular options. -/
theorem act_le_triangle_options {a b c : V}
    (hT : ({a,b,c} : Finset V) ∈ H) (hH : Uniform H) :
    act H {a,b,c} ≤ ((options H a b c).filter (Triangular H)).card := by
  apply card_le_card
  intro q hq
  obtain ⟨ha, ht⟩ := mem_filter.mp hq
  have haq : Active H q := (mem_filter.mp ha).2
  exact mem_filter.mpr ⟨(mem_bicone_iff_option hT hH haq.1.1).mp ht, haq.1⟩

/-- Membership in an active bicone supplies a positive activity count. -/
theorem act_pos_of_active_member {T q : Finset V} (hq : Active H q) (hT : T ∈ bicone H q) :
    0 < act H T := by
  exact card_pos.mpr ⟨q, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_pairs.mpr hq.1.1, hq⟩, hT⟩⟩

/-- A triple with one triangular option in an active bicone has activity exactly one. -/
theorem act_eq_one {a b c : V} {q : Finset V}
    (hT : ({a,b,c} : Finset V) ∈ H) (hH : Uniform H)
    (hopt : ((options H a b c).filter (Triangular H)).card = 1)
    (hq : Active H q) (hmem : ({a,b,c} : Finset V) ∈ bicone H q) :
    act H {a,b,c} = 1 := by
  have hle := act_le_triangle_options hT hH
  have hpos := act_pos_of_active_member hq hmem
  omega

/-- For deficient triples, active bicone count is precisely triangular-option count. -/
theorem deficient_act_eq_triangle_options {a b c : V}
    (hT : ({a,b,c} : Finset V) ∈ H) (hH : Uniform H)
    (hd : Deficient H {a,b,c}) :
    act H {a,b,c} = ((options H a b c).filter (Triangular H)).card := by
  unfold act
  apply congrArg Finset.card
  ext q
  constructor
  · intro hq
    obtain ⟨ha, ht⟩ := mem_filter.mp hq
    have haq : Active H q := (mem_filter.mp ha).2
    exact mem_filter.mpr ⟨(mem_bicone_iff_option hT hH haq.1.1).mp ht, haq.1⟩
  · intro hq
    obtain ⟨ho, ht⟩ := mem_filter.mp hq
    have hm := (mem_bicone_iff_option hT hH ht.1).mpr ho
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_pairs.mpr ht.1, ht, {a,b,c}, hm, hd⟩, hm⟩

end Erdos643R3.G1Bicone
