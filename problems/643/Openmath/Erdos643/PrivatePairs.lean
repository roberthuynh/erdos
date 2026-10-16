import Openmath.Erdos643.HypergraphBasics

namespace Erdos643
namespace PrivatePairs

open Finset HypergraphBasics

variable {V : Type*} [DecidableEq V]

/-- PV's P(T,P) configuration, without assuming the root triple itself is present. -/
structure Pi (H : TripleSystem V) (T P : Finset V) : Prop where
  root_card : T.card = 3
  kernel_card : 2 ≤ P.card
  disjoint : Disjoint T P
  present : ∀ S ⊆ T, S.card = 2 → ∀ a ∈ P, insert a S ∈ H

/-- Actual unordered pairs, each counted once. -/
def privatePairs (T P : Finset V) : Finset (Finset V) :=
  T.powersetCard 2 ∪ P.powersetCard 2

/-- The exact noninduced eight-edge PV K5-minus pattern. The only triples not
required present are abc and cde, which meet in precisely c. -/
def HasK5Minus (H : TripleSystem V) : Prop :=
  ∃ a b c d e : V, [a,b,c,d,e].Nodup ∧
    ∀ S ⊆ ({a,b,c,d,e} : Finset V), S.card = 3 →
      S ≠ {a,b,c} → S ≠ {c,d,e} → S ∈ H

lemma Pi.commonPair {H : TripleSystem V} {T P S : Finset V} (h : Pi H T P)
    {a b : V} (ha : a ∈ P) (hb : b ∈ P) (hST : S ⊆ T) (hS : S.card = 2) :
    CommonPair H a b S := by
  refine ⟨hS, ?_, ?_, h.present S hST hS a ha, h.present S hST hS b hb⟩
  · exact fun haS => disjoint_left.mp h.disjoint (hST haS) ha
  · exact fun hbS => disjoint_left.mp h.disjoint (hST hbS) hb

/-- Literal avoidance forces every two common-link pairs to intersect. -/
lemma commonPairs_intersect {H : TripleSystem V} (havoid : LiteralAvoids H)
    {a b : V} (hab : a ≠ b) {S Q : Finset V}
    (hS : CommonPair H a b S) (hQ : CommonPair H a b Q) : ¬ Disjoint S Q := by
  intro hd
  exact literalAvoids_not_commonMatching havoid ⟨a,b,hab,S,Q,hS,hQ,hd⟩

/-- A prescribed pair inside a triple leaves exactly one third root. -/
lemma triple_of_pair_subset {T : Finset V} (hc : T.card = 3) {a b : V}
    (hab : a ≠ b) (ha : a ∈ T) (hb : b ∈ T) :
    ∃ c, c ≠ a ∧ c ≠ b ∧ T = {a,b,c} := by
  have hsub : ({a,b} : Finset V) ⊆ T := by simp only [insert_subset_iff,singleton_subset_iff]; exact ⟨ha,hb⟩
  have hpair : ({a,b} : Finset V).card = 2 := by simp [hab]
  have hrem : (T \ {a,b}).card = 1 := by
    have he := card_sdiff_add_card_eq_card hsub
    omega
  obtain ⟨c, he⟩ := card_eq_one.mp hrem
  have hcT : c ∈ T ∧ c ∉ ({a,b} : Finset V) := mem_sdiff.mp (by rw [he]; simp)
  refine ⟨c, ?_, ?_, ?_⟩
  · exact (not_or.mp (by simpa using hcT.2)).1
  · exact (not_or.mp (by simpa using hcT.2)).2
  · apply (eq_of_subset_of_card_le (show ({a,b,c} : Finset V) ⊆ T by simp only [insert_subset_iff,singleton_subset_iff]; exact ⟨ha,hb,hcT.1⟩) ?_).symm
    simp only [mem_insert, mem_singleton, not_or] at hcT
    simp [hc, hab, Ne.symm hcT.2.1, Ne.symm hcT.2.2]

lemma Pi.kernel_ne_root {H : TripleSystem V} {T P : Finset V} (h : Pi H T P)
    {p a : V} (hp : p ∈ P) (ha : a ∈ T) : p ≠ a := by
  rintro rfl
  exact disjoint_left.mp h.disjoint ha hp

lemma Pi.rootCommonPair {H : TripleSystem V} {T P : Finset V} (h : Pi H T P)
    {a b c p : V} (hT : T = {a,b,c}) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hp : p ∈ P) : CommonPair H a b {p,c} := by
  have hpa := h.kernel_ne_root hp (show a ∈ T by simp [hT])
  have hpb := h.kernel_ne_root hp (show b ∈ T by simp [hT])
  have hpc := h.kernel_ne_root hp (show c ∈ T by simp [hT])
  refine ⟨by simp [hpc], by simp [hpa.symm,hac], by simp [hpb.symm,hbc], ?_, ?_⟩
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using h.present {a,c} (by simp [hT]) (by simp [hac]) p hp
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using h.present {b,c} (by simp [hT]) (by simp [hbc]) p hp

lemma exists_mem_ne_of_two_le {P : Finset V} (hP : 2 ≤ P.card) (d : V) :
    ∃ p ∈ P, p ≠ d := by
  obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.mp (show 1 < P.card by omega)
  by_cases hpd : p = d
  · exact ⟨q,hq,fun hqd => hpq (hpd.trans hqd.symm)⟩
  · exact ⟨p,hp,hpd⟩

set_option maxHeartbeats 2000000 in
/-- Eight actual triples give the exact PV noninduced pattern. -/
lemma k5minus_of_eight {H : TripleSystem V} {a b c d e : V}
    (hnd : [a,b,c,d,e].Nodup)
    (h1 : ({a,b,d} : Finset V) ∈ H) (h2 : ({a,b,e} : Finset V) ∈ H)
    (h3 : ({a,c,d} : Finset V) ∈ H) (h4 : ({a,c,e} : Finset V) ∈ H)
    (h5 : ({a,d,e} : Finset V) ∈ H) (h6 : ({b,c,d} : Finset V) ∈ H)
    (h7 : ({b,c,e} : Finset V) ∈ H) (h8 : ({b,d,e} : Finset V) ∈ H) :
    HasK5Minus H := by
  refine ⟨a,b,c,d,e,hnd,?_⟩
  intro S hS hc hna hnb
  obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := card_eq_three.mp hc
  have hx : x ∈ ({a,b,c,d,e} : Finset V) := hS (by simp)
  have hy : y ∈ ({a,b,c,d,e} : Finset V) := hS (by simp)
  have hz : z ∈ ({a,b,c,d,e} : Finset V) := hS (by simp)
  simp only [mem_insert,mem_singleton] at hx hy hz
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl | rfl <;>
    simp_all only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc]
  all_goals simp_all

/-- Distinct root triples cannot have a pair common to their kernels. -/
lemma kernel_pairs_separate {H : TripleSystem V} (havoid : LiteralAvoids H)
    {T P U Q S : Finset V} (h : Pi H T P) (k : Pi H U Q)
    (hTU : T ≠ U) (hSP : S ⊆ P) (hSQ : S ⊆ Q) (hS : S.card = 2) : False := by
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hS
  have haP : a ∈ P := hSP (by simp)
  have hbP : b ∈ P := hSP (by simp)
  have haQ : a ∈ Q := hSQ (by simp)
  have hbQ : b ∈ Q := hSQ (by simp)
  have hUT : U ⊆ T := by
    intro x hx
    obtain ⟨u,v,w,huv,huw,hvw,hU⟩ := card_eq_three.mp k.root_card
    have hface : ∀ A ⊆ U, A.card = 2 → A ⊆ T := by
      intro A hAU hA
      exact common_triangle_rigidity havoid hab h.root_card
        (fun B hBT hB => h.commonPair haP hbP hBT hB) (k.commonPair haQ hbQ hAU hA)
    have huvT := hface {u,v} (by simp [hU]) (by simp [huv])
    have huwT := hface {u,w} (by simp [hU]) (by simp [huw])
    simp only [hU,mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact huvT (by simp)
    · exact huvT (by simp)
    · exact huwT (by simp)
  exact hTU (eq_of_subset_of_card_le hUT (by rw [h.root_card,k.root_card])).symm

lemma cross_condition {H : TripleSystem V} (havoid : LiteralAvoids H)
    {T P U Q : Finset V} (h : Pi H T P) (k : Pi H U Q)
    {a b c d p q : V} (hT : T = {a,b,c}) (hU : U = {a,b,d})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hp : p ∈ P) (hq : q ∈ Q) : p = q ∨ p = d ∨ q = c := by
  have hi := commonPairs_intersect havoid hab (h.rootCommonPair hT hab hac hbc hp)
    (k.rootCommonPair hU hab had hbd hq)
  by_contra hn
  apply hi
  apply disjoint_left.mpr
  intro z hz hz'
  simp only [mem_insert,mem_singleton] at hz hz'
  rcases hz with rfl | rfl <;> rcases hz' with hz' | hz' <;> grind

/-- Source Lemma 7 Case 1: a common root pair creates a K5-minus. -/
lemma shared_root_pair {H : TripleSystem V} (havoid : LiteralAvoids H)
    {T P U Q : Finset V} (h : Pi H T P) (k : Pi H U Q)
    {a b c d : V} (hT : T = {a,b,c}) (hU : U = {a,b,d})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d) : HasK5Minus H := by
  obtain ⟨p,hp,hpd⟩ := exists_mem_ne_of_two_le h.kernel_card d
  have hpa := h.kernel_ne_root hp (show a ∈ T by simp [hT])
  have hpb := h.kernel_ne_root hp (show b ∈ T by simp [hT])
  have hpc := h.kernel_ne_root hp (show c ∈ T by simp [hT])
  have hQsub : Q ⊆ ({p,c} : Finset V) := by
    intro q hq
    rcases cross_condition havoid h k hT hU hab hac hbc had hbd hcd hp hq with he | he | he
    · simp [he]
    · exact False.elim (hpd he)
    · simp [he]
  have hQeq : Q = {p,c} := eq_of_subset_of_card_le hQsub
    (by rw [Finset.card_pair hpc]; exact k.kernel_card)
  have hpQ : p ∈ Q := by simp [hQeq]
  have hcQ : c ∈ Q := by simp [hQeq]
  have hPsub : P ⊆ ({p,d} : Finset V) := by
    intro r hr
    rcases cross_condition havoid h k hT hU hab hac hbc had hbd hcd hr hpQ with he | he | he
    · simp [he]
    · simp [he]
    · exact False.elim (hpc he)
  have hPeq : P = {p,d} := eq_of_subset_of_card_le hPsub
    (by rw [Finset.card_pair hpd]; exact h.kernel_card)
  have hdP : d ∈ P := by simp [hPeq]
  apply k5minus_of_eight (a:=c) (b:=d) (c:=p) (d:=a) (e:=b)
  · simp [List.nodup_cons, hcd,hpc.symm,hac.symm,hbc.symm,hpd.symm,had.symm,hbd.symm,hpa,hpb,hab]
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using h.present {a,c} (by simp [hT]) (by simp [hac]) d hdP
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using h.present {b,c} (by simp [hT]) (by simp [hbc]) d hdP
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using h.present {a,c} (by simp [hT]) (by simp [hac]) p hp
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using h.present {b,c} (by simp [hT]) (by simp [hbc]) p hp
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using k.present {a,b} (by simp [hU]) (by simp [hab]) c hcQ
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using k.present {a,d} (by simp [hU]) (by simp [had]) p hpQ
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using k.present {b,d} (by simp [hU]) (by simp [hbd]) p hpQ
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using h.present {a,b} (by simp [hT]) (by simp [hab]) d hdP

/-- Source Lemma 7 Case 2: a root/kernel shared pair creates a K5-minus. -/
lemma shared_root_kernel_pair {H : TripleSystem V} (havoid : LiteralAvoids H)
    {T P U Q : Finset V} (h : Pi H T P) (k : Pi H U Q)
    {a b c : V} (hT : T = {a,b,c}) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haQ : a ∈ Q) (hbQ : b ∈ Q) : HasK5Minus H := by
  obtain ⟨p,hp,q,hq,hpq⟩ := one_lt_card.mp (show 1 < P.card by have := h.kernel_card; omega)
  have hpa := h.kernel_ne_root hp (show a ∈ T by simp [hT])
  have hpb := h.kernel_ne_root hp (show b ∈ T by simp [hT])
  have hpc := h.kernel_ne_root hp (show c ∈ T by simp [hT])
  have hqa := h.kernel_ne_root hq (show a ∈ T by simp [hT])
  have hqb := h.kernel_ne_root hq (show b ∈ T by simp [hT])
  have hqc := h.kernel_ne_root hq (show c ∈ T by simp [hT])
  have hpcU : ({p,c} : Finset V) ⊆ U := common_triangle_rigidity havoid hab k.root_card
    (fun S hSU hS => k.commonPair haQ hbQ hSU hS) (h.rootCommonPair hT hab hac hbc hp)
  have hqcU : ({q,c} : Finset V) ⊆ U := common_triangle_rigidity havoid hab k.root_card
    (fun S hSU hS => k.commonPair haQ hbQ hSU hS) (h.rootCommonPair hT hab hac hbc hq)
  have hU : U = {p,q,c} := (eq_of_subset_of_card_le
    (show ({p,q,c} : Finset V) ⊆ U by
      simp only [insert_subset_iff,singleton_subset_iff]
      exact ⟨hpcU (by simp), hqcU (by simp), hpcU (by simp)⟩)
    (by simp [k.root_card,hpq,hpc,hqc])).symm
  apply k5minus_of_eight (a:=a) (b:=b) (c:=c) (d:=p) (e:=q)
  · simp [List.nodup_cons,hab,hac,hpa.symm,hqa.symm,hbc,hpb.symm,hqb.symm,hpc.symm,hqc.symm,hpq]
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using h.present {a,b} (by simp [hT]) (by simp [hab]) p hp
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using h.present {a,b} (by simp [hT]) (by simp [hab]) q hq
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using h.present {a,c} (by simp [hT]) (by simp [hac]) p hp
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using h.present {a,c} (by simp [hT]) (by simp [hac]) q hq
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using k.present {p,q} (by simp [hU]) (by simp [hpq]) a haQ
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using h.present {b,c} (by simp [hT]) (by simp [hbc]) p hp
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using h.present {b,c} (by simp [hT]) (by simp [hbc]) q hq
  · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using k.present {p,q} (by simp [hU]) (by simp [hpq]) b hbQ

/-- PV2009 Lemma 7's exact private-pair separation consequence in a host
avoiding both the literal four-edge target and the exact K5-minus pattern. -/
theorem pv2009_private_pairs_disjoint {H : TripleSystem V} (_hH : Uniform H)
    (havoid : LiteralAvoids H) (hK : ¬ HasK5Minus H)
    {T P U Q : Finset V} (h : Pi H T P) (k : Pi H U Q) (hTU : T ≠ U) :
    Disjoint (privatePairs T P) (privatePairs U Q) := by
  apply disjoint_left.mpr
  intro S hS hS'
  simp only [privatePairs,mem_union,mem_powersetCard] at hS hS'
  rcases hS with ⟨hST,hSc⟩ | ⟨hSP,hSc⟩
  · obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hSc
    have haT : a ∈ T := hST (by simp)
    have hbT : b ∈ T := hST (by simp)
    obtain ⟨c,hca,hcb,hT⟩ := triple_of_pair_subset h.root_card hab haT hbT
    rcases hS' with ⟨hSU,hSc⟩ | ⟨hSQ,hSc⟩
    · have haU : a ∈ U := hSU (by simp)
      have hbU : b ∈ U := hSU (by simp)
      obtain ⟨d,hda,hdb,hU⟩ := triple_of_pair_subset k.root_card hab haU hbU
      have hcd : c ≠ d := by
        intro he
        exact hTU (by rw [hT,hU,he])
      exact hK (shared_root_pair havoid h k hT hU hab hca.symm hcb.symm hda.symm hdb.symm hcd)
    · exact hK (shared_root_kernel_pair havoid h k hT hab hca.symm hcb.symm
        (hSQ (by simp)) (hSQ (by simp)))
  · rcases hS' with ⟨hSU,hSc'⟩ | ⟨hSQ,hSc'⟩
    · obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hSc'
      have haU : a ∈ U := hSU (by simp)
      have hbU : b ∈ U := hSU (by simp)
      obtain ⟨c,hca,hcb,hU⟩ := triple_of_pair_subset k.root_card hab haU hbU
      exact hK (shared_root_kernel_pair havoid k h hU hab hca.symm hcb.symm
        (hSP (by simp)) (hSP (by simp)))
    · exact kernel_pairs_separate havoid h k hTU hSP hSQ hSc

end PrivatePairs
end Erdos643
