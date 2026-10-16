import Openmath.Erdos643.PrivatePairs
namespace Erdos643
namespace K5Local
open Finset HypergraphBasics PrivatePairs
variable {V : Type*} [DecidableEq V]

/-- Published PV Lemma8 on the exact noninduced eight-edge pattern. -/
theorem pattern_commonPair {H : TripleSystem V} {a b c d e x y : V}
    (hnd : [a,b,c,d,e].Nodup)
    (hpresent : ∀ S ⊆ ({a,b,c,d,e} : Finset V), S.card = 3 →
      S ≠ {a,b,c} → S ≠ {c,d,e} → S ∈ H)
    (hxy : x ≠ y) (hx : x ∈ ({a,b,c,d,e} : Finset V))
    (hy : y ∈ ({a,b,c,d,e} : Finset V)) :
    ∃ Q ⊆ ({a,b,c,d,e} : Finset V), CommonPair H x y Q := by
  simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,List.nodup_nil,not_or,and_true] at hnd
  have hab : a ≠ b := by tauto
  have hac : a ≠ c := by tauto
  have had : a ≠ d := by tauto
  have hae : a ≠ e := by tauto
  have hbc : b ≠ c := by tauto
  have hbd : b ≠ d := by tauto
  have hbe : b ≠ e := by tauto
  have hcd : c ≠ d := by tauto
  have hce : c ≠ e := by tauto
  have hde : d ≠ e := by tauto
  have habd : ({a,b,d} : Finset V) ∈ H := by
    apply hpresent
    · simp [Finset.insert_subset_iff]
    · simp [hab,had,hbd]
    · intro he
      have hm := congrArg (fun S : Finset V => d ∈ S) he
      simp [(Ne.symm had),(Ne.symm hbd),(Ne.symm hcd)] at hm
    · intro he
      have hm := congrArg (fun S : Finset V => a ∈ S) he
      simp [hac,had,hae] at hm
  have habe : ({a,b,e} : Finset V) ∈ H := by
    apply hpresent
    · simp [Finset.insert_subset_iff]
    · simp [hab,hae,hbe]
    · intro he
      have hm := congrArg (fun S : Finset V => e ∈ S) he
      simp [(Ne.symm hae),(Ne.symm hbe),(Ne.symm hce)] at hm
    · intro he
      have hm := congrArg (fun S : Finset V => a ∈ S) he
      simp [hac,had,hae] at hm
  have hacd : ({a,c,d} : Finset V) ∈ H := by
    apply hpresent
    · simp [Finset.insert_subset_iff]
    · simp [hac,had,hcd]
    · intro he
      have hm := congrArg (fun S : Finset V => d ∈ S) he
      simp [(Ne.symm had),(Ne.symm hbd),(Ne.symm hcd)] at hm
    · intro he
      have hm := congrArg (fun S : Finset V => a ∈ S) he
      simp [hac,had,hae] at hm
  have hace : ({a,c,e} : Finset V) ∈ H := by
    apply hpresent
    · simp [Finset.insert_subset_iff]
    · simp [hac,hae,hce]
    · intro he
      have hm := congrArg (fun S : Finset V => e ∈ S) he
      simp [(Ne.symm hae),(Ne.symm hbe),(Ne.symm hce)] at hm
    · intro he
      have hm := congrArg (fun S : Finset V => a ∈ S) he
      simp [hac,had,hae] at hm
  have hade : ({a,d,e} : Finset V) ∈ H := by
    apply hpresent
    · simp [Finset.insert_subset_iff]
    · simp [had,hae,hde]
    · intro he
      have hm := congrArg (fun S : Finset V => d ∈ S) he
      simp [(Ne.symm had),(Ne.symm hbd),(Ne.symm hcd)] at hm
    · intro he
      have hm := congrArg (fun S : Finset V => a ∈ S) he
      simp [hac,had,hae] at hm
  have hbcd : ({b,c,d} : Finset V) ∈ H := by
    apply hpresent
    · simp [Finset.insert_subset_iff]
    · simp [hbc,hbd,hcd]
    · intro he
      have hm := congrArg (fun S : Finset V => d ∈ S) he
      simp [(Ne.symm had),(Ne.symm hbd),(Ne.symm hcd)] at hm
    · intro he
      have hm := congrArg (fun S : Finset V => b ∈ S) he
      simp [hbc,hbd,hbe] at hm
  have hbce : ({b,c,e} : Finset V) ∈ H := by
    apply hpresent
    · simp [Finset.insert_subset_iff]
    · simp [hbc,hbe,hce]
    · intro he
      have hm := congrArg (fun S : Finset V => e ∈ S) he
      simp [(Ne.symm hae),(Ne.symm hbe),(Ne.symm hce)] at hm
    · intro he
      have hm := congrArg (fun S : Finset V => b ∈ S) he
      simp [hbc,hbd,hbe] at hm
  have hbde : ({b,d,e} : Finset V) ∈ H := by
    apply hpresent
    · simp [Finset.insert_subset_iff]
    · simp [hbd,hbe,hde]
    · intro he
      have hm := congrArg (fun S : Finset V => d ∈ S) he
      simp [(Ne.symm had),(Ne.symm hbd),(Ne.symm hcd)] at hm
    · intro he
      have hm := congrArg (fun S : Finset V => b ∈ S) he
      simp [hbc,hbd,hbe] at hm
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with hx | hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy | hy
  all_goals subst x; subst y
  · exact False.elim (hxy rfl)
  · refine ⟨{d,e}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [hde], by simp [had,hae], by simp [hbd,hbe], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hade
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hbde
  · refine ⟨{b,d}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [hbd], by simp [hab,had], by simp [(Ne.symm hbc),hcd], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habd
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hbcd
  · refine ⟨{b,e}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [hbe], by simp [hab,hae], by simp [(Ne.symm hbd),hde], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habe
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hbde
  · refine ⟨{b,d}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [hbd], by simp [hab,had], by simp [(Ne.symm hbe),(Ne.symm hde)], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habd
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hbde
  · refine ⟨{d,e}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [hde], by simp [hbd,hbe], by simp [had,hae], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hbde
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hade
  · exact False.elim (hxy rfl)
  · refine ⟨{a,d}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [had], by simp [(Ne.symm hab),hbd], by simp [(Ne.symm hac),hcd], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habd
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hacd
  · refine ⟨{a,e}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [hae], by simp [(Ne.symm hab),hbe], by simp [(Ne.symm had),hde], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habe
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hade
  · refine ⟨{a,d}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [had], by simp [(Ne.symm hab),hbd], by simp [(Ne.symm hae),(Ne.symm hde)], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habd
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hade
  · refine ⟨{b,d}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [hbd], by simp [(Ne.symm hbc),hcd], by simp [hab,had], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hbcd
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habd
  · refine ⟨{a,d}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [had], by simp [(Ne.symm hac),hcd], by simp [(Ne.symm hab),hbd], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hacd
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habd
  · exact False.elim (hxy rfl)
  · refine ⟨{b,e}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [hbe], by simp [(Ne.symm hbc),hce], by simp [(Ne.symm hbd),hde], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hbce
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hbde
  · refine ⟨{a,d}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [had], by simp [(Ne.symm hac),hcd], by simp [(Ne.symm hae),(Ne.symm hde)], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hacd
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hade
  · refine ⟨{b,e}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [hbe], by simp [(Ne.symm hbd),hde], by simp [hab,hae], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hbde
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habe
  · refine ⟨{a,e}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [hae], by simp [(Ne.symm had),hde], by simp [(Ne.symm hab),hbe], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hade
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habe
  · refine ⟨{b,e}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [hbe], by simp [(Ne.symm hbd),hde], by simp [(Ne.symm hbc),hce], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hbde
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hbce
  · exact False.elim (hxy rfl)
  · refine ⟨{a,b}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [hab], by simp [(Ne.symm had),(Ne.symm hbd)], by simp [(Ne.symm hae),(Ne.symm hbe)], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habd
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habe
  · refine ⟨{b,d}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [hbd], by simp [(Ne.symm hbe),(Ne.symm hde)], by simp [hab,had], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hbde
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habd
  · refine ⟨{a,d}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [had], by simp [(Ne.symm hae),(Ne.symm hde)], by simp [(Ne.symm hab),hbd], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hade
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habd
  · refine ⟨{a,d}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [had], by simp [(Ne.symm hae),(Ne.symm hde)], by simp [(Ne.symm hac),hcd], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hade
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hacd
  · refine ⟨{a,b}, by simp [Finset.insert_subset_iff], ?_⟩
    refine ⟨by simp [hab], by simp [(Ne.symm hae),(Ne.symm hbe)], by simp [(Ne.symm had),(Ne.symm hbd)], ?_, ?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habe
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using habd
  · exact False.elim (hxy rfl)

end K5Local
end Erdos643
