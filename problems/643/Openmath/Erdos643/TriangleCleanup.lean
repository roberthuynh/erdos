import Openmath.Erdos643.PrivatePairs
import Openmath.Erdos643.K5Cleaning
import Openmath.Erdos643.GraphDeletion

namespace Erdos643
namespace TriangleCleanup

open Finset HypergraphBasics PrivatePairs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual full kernel of a root set, in the original host. -/
noncomputable def fullKernel (H : TripleSystem V) (T : Finset V) : Finset V := by
  classical
  exact univ.filter (fun a => a ∉ T ∧ ∀ S ⊆ T, S.card = 2 → insert a S ∈ H)

lemma mem_fullKernel {H : TripleSystem V} {T : Finset V} {a : V} :
    a ∈ fullKernel H T ↔ a ∉ T ∧ ∀ S ⊆ T, S.card = 2 → insert a S ∈ H := by
  classical
  simp [fullKernel]

noncomputable def roots (H : TripleSystem V) : Finset (Finset V) := by
  classical
  exact (univ.powersetCard 3).filter (fun T => 2 ≤ (fullKernel H T).card)

lemma mem_roots {H : TripleSystem V} {T : Finset V} :
    T ∈ roots H ↔ T.card = 3 ∧ 2 ≤ (fullKernel H T).card := by
  classical
  simp [roots]

lemma fullKernel_pi {H : TripleSystem V} {T : Finset V} (hT : T ∈ roots H) :
    Pi H T (fullKernel H T) := by
  obtain ⟨hc, hk⟩ := mem_roots.mp hT
  refine ⟨hc, hk, ?_, ?_⟩
  · exact disjoint_left.mpr (fun a ha hp => (mem_fullKernel.mp hp).1 ha)
  · intro S hST hS a ha
    exact (mem_fullKernel.mp ha).2 S hST hS

/-- Unordered distinct original diagonals, expressed using actual common-link pairs. -/
noncomputable def Dpairs (H : TripleSystem V) : Finset (Finset V) := by
  classical
  exact (univ.powersetCard 2).filter (fun S => ∃ a b, a ≠ b ∧ S = {a,b} ∧
    ∃ v u w, u ≠ w ∧ CommonPair H a b {v,u} ∧ CommonPair H a b {v,w})

lemma mem_Dpairs {H : TripleSystem V} {S : Finset V} :
    S ∈ Dpairs H ↔ S.card = 2 ∧ ∃ a b, a ≠ b ∧ S = {a,b} ∧
      ∃ v u w, u ≠ w ∧ CommonPair H a b {v,u} ∧ CommonPair H a b {v,w} := by
  classical
  simp [Dpairs]

lemma Dpairs_mono {H G : TripleSystem V} (hHG : H ⊆ G) : Dpairs H ⊆ Dpairs G := by
  intro S hS
  obtain ⟨hc,a,b,hab,he,v,u,w,huw,hP,hQ⟩ := mem_Dpairs.mp hS
  exact mem_Dpairs.mpr ⟨hc,a,b,hab,he,v,u,w,huw,
    K5Cleaning.commonPair_mono hHG hP,K5Cleaning.commonPair_mono hHG hQ⟩

lemma Dpairs_subset_Bpairs (H : TripleSystem V) : Dpairs H ⊆ K5Cleaning.Bpairs H := by
  intro S hS
  obtain ⟨hc,a,b,hab,rfl,v,u,w,huw,hP,hQ⟩ := mem_Dpairs.mp hS
  exact K5Cleaning.mem_Bpairs.mpr ⟨hc,a,b,hab,rfl,{v,u},hP⟩

lemma fixed_commonPair_link {H : TripleSystem V} {a b v u : V} :
    CommonPair H a b {v,u} ↔
      (K5Cleaning.linkGraph H v).Adj a u ∧ (K5Cleaning.linkGraph H v).Adj b u := by
  constructor
  · intro hP
    have hvu : v ≠ u := by
      intro he
      have hc := hP.1
      simp [he] at hc
    have hav : a ≠ v := by intro he; exact hP.2.1 (by simp [he])
    have hau : a ≠ u := by intro he; exact hP.2.1 (by simp [he])
    have hbv : b ≠ v := by intro he; exact hP.2.2.1 (by simp [he])
    have hbu : b ≠ u := by intro he; exact hP.2.2.1 (by simp [he])
    refine ⟨⟨hav.symm,hvu,hau,?_⟩,⟨hbv.symm,hvu,hbu,?_⟩⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hP.2.2.2.1
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hP.2.2.2.2
  · rintro ⟨ha,hb⟩
    refine ⟨by simp [ha.2.1],by simp [ha.1.symm,ha.2.2.1],
      by simp [hb.1.symm,hb.2.2.1],?_,?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using ha.2.2.2
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hb.2.2.2

/-- Exact identification with original link diagonals, using the shared actual link graph. -/
lemma Dpairs_iff_link_diagonal {H : TripleSystem V} {S : Finset V} :
    S ∈ Dpairs H ↔ S.card = 2 ∧ ∃ a b v, S = {a,b} ∧
      GraphDeletion.IsDiagonal (K5Cleaning.linkGraph H v) a b := by
  constructor
  · rintro hS
    obtain ⟨hc,a,b,hab,he,v,u,w,huw,hP,hQ⟩ := mem_Dpairs.mp hS
    obtain ⟨hau,hbu⟩ := fixed_commonPair_link.mp hP
    obtain ⟨haw,hbw⟩ := fixed_commonPair_link.mp hQ
    exact ⟨hc,a,b,v,he,hab,u,w,huw,hau,hbu,haw,hbw⟩
  · rintro ⟨hc,a,b,v,he,hab,u,w,huw,hau,hbu,haw,hbw⟩
    exact mem_Dpairs.mpr ⟨hc,a,b,hab,he,v,u,w,huw,
      fixed_commonPair_link.mpr ⟨hau,hbu⟩,fixed_commonPair_link.mpr ⟨haw,hbw⟩⟩

lemma privatePairs_subset_Dpairs {H : TripleSystem V} {T P : Finset V}
    (h : Pi H T P) : privatePairs T P ⊆ Dpairs H := by
  classical
  intro S hS
  rcases (show S ⊆ T ∧ S.card = 2 ∨ S ⊆ P ∧ S.card = 2 by
    simpa [privatePairs] using hS) with ⟨hST,hSc⟩ | ⟨hSP,hSc⟩
  · obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hSc
    obtain ⟨c,hca,hcb,hT⟩ := triple_of_pair_subset h.root_card hab
      (hST (by simp)) (hST (by simp))
    obtain ⟨p,hp,q,hq,hpq⟩ := one_lt_card.mp (show 1 < P.card by have := h.kernel_card; omega)
    refine mem_Dpairs.mpr ⟨by simp [hab],a,b,hab,rfl,c,p,q,hpq,?_,?_⟩
    · simpa only [pair_comm] using h.rootCommonPair hT hab hca.symm hcb.symm hp
    · simpa only [pair_comm] using h.rootCommonPair hT hab hca.symm hcb.symm hq
  · obtain ⟨p,q,hpq,rfl⟩ := card_eq_two.mp hSc
    have hp : p ∈ P := hSP (by simp)
    have hq : q ∈ P := hSP (by simp)
    obtain ⟨a,b,c,hab,hac,hbc,hT⟩ := card_eq_three.mp h.root_card
    refine mem_Dpairs.mpr ⟨by simp [hpq],p,q,hpq,rfl,a,b,c,hbc,?_,?_⟩
    · exact h.commonPair hp hq (by simp [hT]) (by simp [hab])
    · exact h.commonPair hp hq (by simp [hT]) (by simp [hac])

lemma root_privatePairs_disjoint {H : TripleSystem V} (hH : Uniform H)
    (havoid : LiteralAvoids H) (hK : ¬ HasK5Minus H)
    {T U : Finset V} (hT : T ∈ roots H) (hU : U ∈ roots H) (hne : T ≠ U) :
    Disjoint (privatePairs T (fullKernel H T)) (privatePairs U (fullKernel H U)) :=
  pv2009_private_pairs_disjoint hH havoid hK (fullKernel_pi hT) (fullKernel_pi hU) hne

/-- A chosen actual two-subset; only roots of cardinality three use it. -/
noncomputable def rootPair (T : Finset V) : Finset V :=
  if h : 2 ≤ T.card then Classical.choose (exists_subset_card_eq h) else ∅

lemma rootPair_spec {T : Finset V} (hT : T.card = 3) :
    rootPair T ⊆ T ∧ (rootPair T).card = 2 := by
  have h : 2 ≤ T.card := by omega
  simp only [rootPair, dif_pos h]
  exact Classical.choose_spec (exists_subset_card_eq h)

/-- Retain exactly one original kernel vertex when the kernel is nonempty. -/
noncomputable def retained (P : Finset V) : Finset V :=
  if h : P.Nonempty then {Classical.choose h} else ∅

lemma retained_spec {P : Finset V} (hP : P.Nonempty) :
    retained P ⊆ P ∧ (retained P).card = 1 := by
  classical
  simp only [retained, dif_pos hP]
  exact ⟨singleton_subset_iff.mpr (Classical.choose_spec hP), card_singleton _⟩

noncomputable def deletedAt (H : TripleSystem V) (T : Finset V) : TripleSystem V := by
  classical
  exact (fullKernel H T \ retained (fullKernel H T)).image (fun a => insert a (rootPair T))

noncomputable def deleted (H : TripleSystem V) : TripleSystem V := by
  classical
  exact (roots H).biUnion (deletedAt H)

lemma deletedAt_subset {H : TripleSystem V} {T : Finset V} (hT : T ∈ roots H) :
    deletedAt H T ⊆ H := by
  classical
  intro E hE
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hE
  have hp := (mem_sdiff.mp ha).1
  exact (mem_fullKernel.mp hp).2 _ (rootPair_spec (mem_roots.mp hT).1).1
    (rootPair_spec (mem_roots.mp hT).1).2

lemma deleted_subset (H : TripleSystem V) : deleted H ⊆ H := by
  classical
  intro E hE
  obtain ⟨T,hT,hE⟩ := mem_biUnion.mp hE
  exact deletedAt_subset hT hE

/-- Every original full triangle loses the selected root-pair edge at all but one center. -/
lemma no_surviving_full_triangle {H : TripleSystem V} {a b : V} (hab : a ≠ b)
    {T : Finset V} (hT : T.card = 3)
    (hfaces : ∀ S ⊆ T, S.card = 2 → CommonPair (H \ deleted H) a b S) : False := by
  classical
  have ha : a ∈ fullKernel H T := by
    apply mem_fullKernel.mpr
    constructor
    · intro haT
      obtain ⟨c,d,e,hcd,hce,hde,hTeq⟩ := card_eq_three.mp hT
      have haCases : a = c ∨ a = d ∨ a = e := by simpa [hTeq] using haT
      rcases haCases with haC | haD | haE
      · exact (hfaces {c,d} (by simp [hTeq]) (by simp [hcd])).2.1 (by simp [haC])
      · exact (hfaces {c,d} (by simp [hTeq]) (by simp [hcd])).2.1 (by simp [haD])
      · exact (hfaces {c,e} (by simp [hTeq]) (by simp [hce])).2.1 (by simp [haE])
    · intro S hST hS
      exact (mem_sdiff.mp (hfaces S hST hS).2.2.2.1).1
  have hb : b ∈ fullKernel H T := by
    apply mem_fullKernel.mpr
    constructor
    · intro hbT
      obtain ⟨c,d,e,hcd,hce,hde,hTeq⟩ := card_eq_three.mp hT
      have hbCases : b = c ∨ b = d ∨ b = e := by simpa [hTeq] using hbT
      rcases hbCases with hbC | hbD | hbE
      · exact (hfaces {c,d} (by simp [hTeq]) (by simp [hcd])).2.2.1 (by simp [hbC])
      · exact (hfaces {c,d} (by simp [hTeq]) (by simp [hcd])).2.2.1 (by simp [hbD])
      · exact (hfaces {c,e} (by simp [hTeq]) (by simp [hce])).2.2.1 (by simp [hbE])
    · intro S hST hS
      exact (mem_sdiff.mp (hfaces S hST hS).2.2.2.2).1
  have hkc : 2 ≤ (fullKernel H T).card := by
    have := one_lt_card.mpr ⟨a,ha,b,hb,hab⟩
    omega
  have hTr : T ∈ roots H := mem_roots.mpr ⟨hT,hkc⟩
  have hret := retained_spec (show (fullKernel H T).Nonempty from ⟨a,ha⟩)
  have hnot : a ∉ retained (fullKernel H T) ∨ b ∉ retained (fullKernel H T) := by
    by_contra hn
    push_neg at hn
    have htwo := one_lt_card.mpr ⟨a,hn.1,b,hn.2,hab⟩
    omega
  have hS := rootPair_spec hT
  rcases hnot with hna | hnb
  · have hdel : insert a (rootPair T) ∈ deleted H :=
      mem_biUnion.mpr ⟨T,hTr,mem_image.mpr ⟨a,mem_sdiff.mpr ⟨ha,hna⟩,rfl⟩⟩
    exact (mem_sdiff.mp (hfaces _ hS.1 hS.2).2.2.2.1).2 hdel
  · have hdel : insert b (rootPair T) ∈ deleted H :=
      mem_biUnion.mpr ⟨T,hTr,mem_image.mpr ⟨b,mem_sdiff.mpr ⟨hb,hnb⟩,rfl⟩⟩
    exact (mem_sdiff.mp (hfaces _ hS.1 hS.2).2.2.2.2).2 hdel

lemma privatePairs_card {H : TripleSystem V} {T P : Finset V} (h : Pi H T P) :
    (privatePairs T P).card = 3 + P.card.choose 2 := by
  classical
  have hd : Disjoint (T.powersetCard 2) (P.powersetCard 2) := by
    apply disjoint_left.mpr
    intro S hST hSP
    obtain ⟨hST,hSc⟩ := mem_powersetCard.mp hST
    obtain ⟨hSP,_⟩ := mem_powersetCard.mp hSP
    obtain ⟨a,ha⟩ := card_pos.mp (show 0 < S.card by omega)
    exact disjoint_left.mp h.disjoint (hST ha) (hSP ha)
  rw [privatePairs,card_union_of_disjoint hd,card_powersetCard,card_powersetCard,h.root_card]
  norm_num

lemma triple_kernel_cost (i : ℕ) (hi : 2 ≤ i) : 3 * (i - 1) ≤ 3 + i.choose 2 := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hsmall : i < 5
    · interval_cases i <;> norm_num [Nat.choose] at *
    · have hij : i - 1 < i := by omega
      have hprev := ih (i-1) hij (by omega)
      have hc : i.choose 2 = (i-1) + (i-1).choose 2 := by
        have heq : i = (i-1)+1 := by omega
        rw [heq, Nat.choose_succ_succ']
        simp
      omega

lemma deletedAt_card_le {H : TripleSystem V} {T : Finset V} (hT : T ∈ roots H) :
    (deletedAt H T).card ≤ (fullKernel H T).card - 1 := by
  classical
  have hc := (mem_roots.mp hT).2
  have hn : (fullKernel H T).Nonempty := card_pos.mp (by omega)
  have hr := retained_spec hn
  have he := card_sdiff_add_card_eq_card hr.1
  have him : (deletedAt H T).card ≤ (fullKernel H T \ retained (fullKernel H T)).card :=
    card_image_le
  omega

/-- Exact original-private-pair charge bound, with all roots simultaneously enumerated. -/
theorem deleted_card_charge {H : TripleSystem V} (hH : Uniform H)
    (havoid : LiteralAvoids H) (hK : ¬ HasK5Minus H) :
    3 * (deleted H).card ≤ (Dpairs H).card := by
  classical
  have hdis : (roots H : Set (Finset V)).Pairwise
      (fun T U => Disjoint (privatePairs T (fullKernel H T)) (privatePairs U (fullKernel H U))) := by
    intro T hT U hU hne
    exact root_privatePairs_disjoint hH havoid hK hT hU hne
  have hsub : (roots H).biUnion (fun T => privatePairs T (fullKernel H T)) ⊆ Dpairs H := by
    intro S hS
    obtain ⟨T,hT,hS⟩ := mem_biUnion.mp hS
    exact privatePairs_subset_Dpairs (fullKernel_pi hT) hS
  calc
    3 * (deleted H).card ≤ 3 * ∑ T ∈ roots H, (deletedAt H T).card :=
      Nat.mul_le_mul_left 3 card_biUnion_le
    _ = ∑ T ∈ roots H, 3 * (deletedAt H T).card := by rw [mul_sum]
    _ ≤ ∑ T ∈ roots H, (privatePairs T (fullKernel H T)).card := by
      apply sum_le_sum
      intro T hT
      calc
        3 * (deletedAt H T).card ≤ 3 * ((fullKernel H T).card - 1) :=
          Nat.mul_le_mul_left 3 (deletedAt_card_le hT)
        _ ≤ 3 + (fullKernel H T).card.choose 2 := triple_kernel_cost _ (mem_roots.mp hT).2
        _ = _ := (privatePairs_card (fullKernel_pi hT)).symm
    _ = ((roots H).biUnion (fun T => privatePairs T (fullKernel H T))).card :=
      (card_biUnion hdis).symm
    _ ≤ (Dpairs H).card := card_le_card hsub

/-- All common-link pair families have an actual common vertex (empty families allowed). -/
def AllStars (H : TripleSystem V) : Prop :=
  ∀ a b, a ≠ b → ∃ c, ∀ P, CommonPair H a b P → c ∈ P

lemma pair_eq_of_mem {P : Finset V} (hc : P.card = 2) {v : V} (hv : v ∈ P) :
    ∃ w, w ≠ v ∧ P = {v,w} := by
  obtain ⟨p,q,hpq,hP⟩ := card_eq_two.mp hc
  have hv' : v = p ∨ v = q := by simpa [hP] using hv
  rcases hv' with rfl | rfl
  · exact ⟨q,hpq.symm,hP⟩
  · exact ⟨p,hpq,by simpa [pair_comm] using hP⟩

lemma pair_mem_of_intersect {P : Finset V} {u v : V}
    (hi : ¬ Disjoint ({u,v} : Finset V) P) (hu : u ∉ P) : v ∈ P := by
  by_contra hv
  apply hi
  apply disjoint_left.mpr
  intro z hz hzP
  simp only [mem_insert,mem_singleton] at hz
  exact hz.elim (fun he => hu (he ▸ hzP)) (fun he => hv (he ▸ hzP))

/-- The elementary intersecting-pair classification used in the accepted written proof. -/
theorem cleanup_allStars {H : TripleSystem V} (havoid : LiteralAvoids H) :
    AllStars (H \ deleted H) := by
  classical
  let J := H \ deleted H
  have hmono : ∀ {a b P}, CommonPair J a b P → CommonPair H a b P := by
    intro a b P hp
    exact ⟨hp.1,hp.2.1,hp.2.2.1,(mem_sdiff.mp hp.2.2.2.1).1,(mem_sdiff.mp hp.2.2.2.2).1⟩
  intro a b hab
  have hi : ∀ {P Q}, CommonPair J a b P → CommonPair J a b Q → ¬ Disjoint P Q := by
    intro P Q hp hq
    exact commonPairs_intersect havoid hab (hmono hp) (hmono hq)
  by_cases hn : ∃ P, CommonPair J a b P
  · obtain ⟨P,hP⟩ := hn
    obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hP.1
    by_cases hu : ∀ Q, CommonPair J a b Q → u ∈ Q
    · exact ⟨u,hu⟩
    push_neg at hu
    obtain ⟨Q,hQ,huQ⟩ := hu
    have hvQ : v ∈ Q := pair_mem_of_intersect (hi hP hQ) huQ
    obtain ⟨w,hwv,hQeq⟩ := pair_eq_of_mem hQ.1 hvQ
    have huw : u ≠ w := by intro he; exact huQ (by simp [hQeq,he])
    by_cases hv : ∀ R, CommonPair J a b R → v ∈ R
    · exact ⟨v,hv⟩
    push_neg at hv
    obtain ⟨R,hR,hvR⟩ := hv
    have huR : u ∈ R := pair_mem_of_intersect (by simpa only [pair_comm] using hi hP hR) hvR
    have hwR : w ∈ R := pair_mem_of_intersect (by simpa only [hQeq] using hi hQ hR) hvR
    have hReq : R = {u,w} := (eq_of_subset_of_card_le
      (show ({u,w} : Finset V) ⊆ R by simp only [insert_subset_iff,singleton_subset_iff]; exact ⟨huR,hwR⟩)
      (by simp [hR.1,huw])).symm
    have hfaces : ∀ S ⊆ ({u,v,w} : Finset V), S.card = 2 → CommonPair J a b S := by
      intro S hST hSc
      obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hSc
      have hx : x = u ∨ x = v ∨ x = w := by simpa using hST (by simp : x ∈ ({x,y} : Finset V))
      have hy : y = u ∨ y = v ∨ y = w := by simpa using hST (by simp : y ∈ ({x,y} : Finset V))
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      all_goals first
        | exact False.elim (hxy rfl)
        | simpa only [hQeq,pair_comm] using hQ
        | simpa only [hReq,pair_comm] using hR
        | simpa only [pair_comm] using hP
    exact False.elim (no_surviving_full_triangle hab (by simp [huv,huw,hwv.symm]) hfaces)
  · exact ⟨a,fun P hp => False.elim (hn ⟨P,hp⟩)⟩

/-- Section 4 of the accepted exact 4/3 proof: actual deletion and original charge. -/
theorem triangle_cleanup {H : TripleSystem V} (hH : Uniform H)
    (havoid : LiteralAvoids H) (hK : ¬ HasK5Minus H) :
    ∃ Z : TripleSystem V, Z ⊆ H ∧ 3 * Z.card ≤ (Dpairs H).card ∧ AllStars (H \ Z) :=
  ⟨deleted H,deleted_subset H,deleted_card_charge hH havoid hK,cleanup_allStars havoid⟩

end TriangleCleanup
end Erdos643
