import Openmath.Erdos643.PrivatePairs
import Openmath.Erdos643.K5Local
import Openmath.Erdos643.DegreeCharge

namespace Erdos643
namespace K5Cleaning

open Finset HypergraphBasics PrivatePairs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual unordered distinct vertex pairs with a common-link edge. This is
exactly the source's D(H) ∪ E(H), without requiring either set separately. -/
noncomputable def Bpairs (H : TripleSystem V) : Finset (Finset V) := by
  classical
  exact (Finset.univ.powersetCard 2).filter (fun S =>
    ∃ a b, a ≠ b ∧ S = {a,b} ∧ ∃ Q, CommonPair H a b Q)

lemma mem_Bpairs {H : TripleSystem V} {S : Finset V} :
    S ∈ Bpairs H ↔ S.card = 2 ∧ ∃ a b, a ≠ b ∧ S = {a,b} ∧ ∃ Q, CommonPair H a b Q := by
  classical
  simp [Bpairs]

lemma commonPair_mono {H G : TripleSystem V} (hHG : H ⊆ G)
    {a b : V} {Q : Finset V} (hQ : CommonPair H a b Q) : CommonPair G a b Q :=
  ⟨hQ.1,hQ.2.1,hQ.2.2.1,hHG hQ.2.2.2.1,hHG hQ.2.2.2.2⟩

lemma Bpairs_mono {H G : TripleSystem V} (hHG : H ⊆ G) : Bpairs H ⊆ Bpairs G := by
  intro S hS
  obtain ⟨hc,a,b,hab,rfl,Q,hQ⟩ := mem_Bpairs.mp hS
  exact mem_Bpairs.mpr ⟨hc,a,b,hab,rfl,Q,commonPair_mono hHG hQ⟩

lemma Bpairs_card_le (H : TripleSystem V) :
    (Bpairs H).card ≤ (Fintype.card V).choose 2 := by
  classical
  calc
    (Bpairs H).card ≤ (Finset.univ.powersetCard 2 : Finset (Finset V)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = _ := by simp

/-- Labelled support of the exact noninduced PV K5-minus pattern. -/
def K5Support (H : TripleSystem V) (A : Finset V) : Prop :=
  ∃ a b c d e : V, [a,b,c,d,e].Nodup ∧ A = {a,b,c,d,e} ∧
    ∀ S ⊆ A, S.card = 3 → S ≠ {a,b,c} → S ≠ {c,d,e} → S ∈ H

lemma hasK5Minus_iff_support (H : TripleSystem V) :
    HasK5Minus H ↔ ∃ A, K5Support H A := by
  constructor
  · rintro ⟨a,b,c,d,e,hnd,hpresent⟩
    exact ⟨{a,b,c,d,e},a,b,c,d,e,hnd,rfl,hpresent⟩
  · rintro ⟨A,a,b,c,d,e,hnd,rfl,hpresent⟩
    exact ⟨a,b,c,d,e,hnd,hpresent⟩

lemma K5Support.card {H : TripleSystem V} {A : Finset V} (hA : K5Support H A) : A.card = 5 := by
  obtain ⟨a,b,c,d,e,hnd,rfl,_⟩ := hA
  simpa using (List.toFinset_card_of_nodup hnd)

noncomputable def supports (H : TripleSystem V) : Finset (Finset V) := by
  classical
  exact (Finset.univ.powersetCard 5).filter (K5Support H)

lemma mem_supports {H : TripleSystem V} {A : Finset V} :
    A ∈ supports H ↔ K5Support H A := by
  classical
  simp only [supports,mem_filter,mem_powersetCard,subset_univ,true_and]
  exact ⟨And.right,fun h => ⟨h.card,h⟩⟩

/-- All actual edges intersecting an original exceptional support in at least
 two vertices: this is the union of PV's main and secondary triples. -/
noncomputable def removed (H : TripleSystem V) : TripleSystem V := by
  classical
  exact H.filter (fun E => ∃ A ∈ supports H, 2 ≤ (E ∩ A).card)

lemma removed_subset (H : TripleSystem V) : removed H ⊆ H := by
  classical
  exact filter_subset _ _

lemma mem_removed {H : TripleSystem V} {E : Finset V} :
    E ∈ removed H ↔ E ∈ H ∧ ∃ A ∈ supports H, 2 ≤ (E ∩ A).card := by
  classical
  simp [removed]

lemma remains_intersection_lt_two {H : TripleSystem V} {E A : Finset V}
    (hE : E ∈ H \ removed H) (hA : A ∈ supports H) : (E ∩ A).card < 2 := by
  obtain ⟨hEH,hER⟩ := mem_sdiff.mp hE
  by_contra hn
  exact hER (mem_removed.mpr ⟨hEH,A,hA,by omega⟩)

lemma K5Support.mono {H G : TripleSystem V} {A : Finset V}
    (hHG : H ⊆ G) (hA : K5Support H A) : K5Support G A := by
  obtain ⟨a,b,c,d,e,hnd,hA,hpresent⟩ := hA
  exact ⟨a,b,c,d,e,hnd,hA,fun S hSA hS h1 h2 => hHG (hpresent S hSA hS h1 h2)⟩

lemma K5Support.some_edge {H : TripleSystem V} {A : Finset V} (hA : K5Support H A) :
    ∃ E ∈ H, E ⊆ A ∧ E.card = 3 := by
  obtain ⟨a,b,c,d,e,hnd,rfl,hpresent⟩ := hA
  have hab : a ≠ b := by grind [List.nodup_cons]
  have had : a ≠ d := by grind [List.nodup_cons]
  have hbd : b ≠ d := by grind [List.nodup_cons]
  have hdc : d ≠ c := by grind [List.nodup_cons]
  have hac : a ≠ c := by grind [List.nodup_cons]
  have hae : a ≠ e := by grind [List.nodup_cons]
  have hEsub : ({a,b,d} : Finset V) ⊆ {a,b,c,d,e} := by simp
  have hEcard : ({a,b,d} : Finset V).card = 3 := by simp [hab,had,hbd]
  have h1 : ({a,b,d} : Finset V) ≠ {a,b,c} := by
    intro he
    have hm : d ∈ ({a,b,c} : Finset V) := by rw [←he]; simp
    simp [Ne.symm had,Ne.symm hbd,hdc] at hm
  have h2 : ({a,b,d} : Finset V) ≠ {c,d,e} := by
    intro he
    have hm : a ∈ ({c,d,e} : Finset V) := by rw [←he]; simp
    simp [hac,had,hae] at hm
  exact ⟨{a,b,d},hpresent _ hEsub hEcard h1 h2,hEsub,hEcard⟩

/-- The proposed actual edge deletion unconditionally removes every K5-minus
 pattern. The quantitative cost bound is a separate obligation. -/
theorem removed_cleans (H : TripleSystem V) : ¬ HasK5Minus (H \ removed H) := by
  intro hk
  obtain ⟨A,hA⟩ := (hasK5Minus_iff_support _).mp hk
  have hAH := hA.mono Finset.sdiff_subset
  have hAmem : A ∈ supports H := mem_supports.mpr hAH
  obtain ⟨E,hE,hEA,hEc⟩ := hA.some_edge
  have hsmall := remains_intersection_lt_two hE hAmem
  rw [Finset.inter_eq_left.mpr hEA,hEc] at hsmall
  omega

lemma commonPair_symm {H : TripleSystem V} {a b : V} {Q : Finset V}
    (hQ : CommonPair H a b Q) : CommonPair H b a Q :=
  ⟨hQ.1,hQ.2.2.1,hQ.2.1,hQ.2.2.2.2,hQ.2.2.2.1⟩

lemma mem_Bpairs_pair {H : TripleSystem V} {x y : V} :
    ({x,y} : Finset V) ∈ Bpairs H ↔ x ≠ y ∧ ∃ Q, CommonPair H x y Q := by
  constructor
  · intro hm
    obtain ⟨hc,a,b,hab,he,Q,hQ⟩ := mem_Bpairs.mp hm
    have hxy : x ≠ y := by intro h; subst y; simp at hc
    have hx : x = a ∨ x = b := by
      have hx : x ∈ ({a,b} : Finset V) := by rw [←he]; simp
      simpa using hx
    have hy : y = a ∨ y = b := by
      have hy : y ∈ ({a,b} : Finset V) := by rw [←he]; simp
      simpa using hy
    refine ⟨hxy,?_⟩
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (hxy rfl)
    · exact ⟨Q,hQ⟩
    · exact ⟨Q,commonPair_symm hQ⟩
    · exact False.elim (hxy rfl)
  · rintro ⟨hxy,Q,hQ⟩
    exact mem_Bpairs.mpr ⟨by simp [hxy],x,y,hxy,rfl,Q,hQ⟩

/-- A surviving common-link pair whose center is in an exceptional support
 must be entirely outside that support. This uses actual removed triples. -/
lemma surviving_commonPair_outside {H : TripleSystem V} {A Q : Finset V} {x y : V}
    (hA : A ∈ supports H) (hy : y ∈ A) (hQ : CommonPair (H \ removed H) x y Q) :
    Disjoint Q A := by
  apply disjoint_left.mpr
  intro z hz hzA
  have hsmall := remains_intersection_lt_two hQ.2.2.2.2 hA
  have hyz : y ≠ z := fun he => hQ.2.2.1 (he ▸ hz)
  have hp : ({y,z} : Finset V) ⊆ insert y Q ∩ A := by
    simp only [insert_subset_iff,singleton_subset_iff,mem_inter]
    exact ⟨⟨by simp,hy⟩,⟨by simp [hz],hzA⟩⟩
  have hc := card_le_card hp
  rw [card_pair hyz] at hc
  omega

/-- PV's logical predicate L(x,y,uv,A), with all supports retained. -/
def SecondaryWitness (H : TripleSystem V) (x y : V) (Q A : Finset V) : Prop :=
  A ∈ supports H ∧ x ∉ A ∧ y ∈ A ∧ Q ⊆ A ∧ CommonPair H x y Q

noncomputable def secondaryPairs (H : TripleSystem V) : Finset (Finset V) := by
  classical
  exact (Bpairs H).filter (fun S => ∃ x y, S = {x,y} ∧ ∃ Q A, SecondaryWitness H x y Q A)

lemma mem_secondaryPairs {H : TripleSystem V} {S : Finset V} :
    S ∈ secondaryPairs H ↔ S ∈ Bpairs H ∧ ∃ x y, S = {x,y} ∧ ∃ Q A, SecondaryWitness H x y Q A := by
  classical
  simp [secondaryPairs]

/-- Secondary charged pairs have zero common-link edges after the actual
 deletion, including half-diagonal remnants. -/
theorem secondaryPairs_disjoint_Bpairs {H : TripleSystem V} (havoid : LiteralAvoids H) :
    Disjoint (secondaryPairs H) (Bpairs (H \ removed H)) := by
  apply disjoint_left.mpr
  intro S hS hB
  obtain ⟨_,x,y,rfl,Q,A,hA,hx,hy,hQA,hQ⟩ := mem_secondaryPairs.mp hS
  obtain ⟨hxy,P,hP⟩ := mem_Bpairs_pair.mp hB
  have hPA := surviving_commonPair_outside hA hy hP
  have hPQ : Disjoint P Q := disjoint_of_subset_right hQA hPA
  exact literalAvoids_not_commonMatching havoid
    ⟨x,y,hxy,P,Q,commonPair_mono Finset.sdiff_subset hP,hQ,hPQ⟩

/-- An actual vertex-link graph, retaining all three distinct support vertices. -/
def linkGraph (H : TripleSystem V) (v : V) : SimpleGraph V where
  Adj x z := v ≠ x ∧ v ≠ z ∧ x ≠ z ∧ insert v ({x,z} : Finset V) ∈ H
  symm := ⟨by
    intro x z h
    refine ⟨h.2.1,h.1,h.2.2.1.symm,?_⟩
    simpa only [Finset.pair_comm] using h.2.2.2⟩
  loopless := ⟨fun x h => h.2.2.1 rfl⟩

/-- Literal bridge between common-link edges and a two-path in an actual
 original vertex-link graph. No hypergraph support is dropped. -/
lemma commonPair_iff_link_two_path (H : TripleSystem V) (x y : V) :
    (∃ Q, CommonPair H x y Q) ↔
      ∃ v z, (linkGraph H v).Adj x z ∧ (linkGraph H v).Adj y z := by
  constructor
  · rintro ⟨Q,hQ⟩
    obtain ⟨v,z,hvz,rfl⟩ := Finset.card_eq_two.mp hQ.1
    have hxv : x ≠ v := by exact (not_or.mp (by simpa only [mem_insert,mem_singleton] using hQ.2.1)).1
    have hxz : x ≠ z := by exact (not_or.mp (by simpa only [mem_insert,mem_singleton] using hQ.2.1)).2
    have hyv : y ≠ v := by exact (not_or.mp (by simpa only [mem_insert,mem_singleton] using hQ.2.2.1)).1
    have hyz : y ≠ z := by exact (not_or.mp (by simpa only [mem_insert,mem_singleton] using hQ.2.2.1)).2
    refine ⟨v,z,⟨hxv.symm,hvz,hxz,?_⟩,⟨hyv.symm,hvz,hyz,?_⟩⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hQ.2.2.2.1
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hQ.2.2.2.2
  · rintro ⟨v,z,hx,hy⟩
    refine ⟨{v,z},by simp [hx.2.1],by simp [hx.1.symm,hx.2.2.1],
      by simp [hy.1.symm,hy.2.2.1],?_,?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hx.2.2.2
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hy.2.2.2

lemma mem_Bpairs_pair_iff_link_two_path (H : TripleSystem V) (x y : V) :
    ({x,y} : Finset V) ∈ Bpairs H ↔ x ≠ y ∧
      ∃ v z, (linkGraph H v).Adj x z ∧ (linkGraph H v).Adj y z := by
  rw [mem_Bpairs_pair,commonPair_iff_link_two_path]

/-- Inside an exact K5-minus support every pair has at least two actual
 completing vertices. This is the degree lower bound in PV11's proof. -/
theorem K5Support.two_extensions {H : TripleSystem V} {A Q : Finset V}
    (hA : K5Support H A) (hQA : Q ⊆ A) (hQ : Q.card = 2) :
    2 ≤ ((A \ Q).filter (fun y => insert y Q ∈ H)).card := by
  classical
  obtain ⟨a,b,c,d,e,hnd,hAeq,hpresent⟩ := hA
  have hmissing_inter : (({a,b,c} : Finset V) ∩ {c,d,e}).card = 1 := by
    have he : ({a,b,c} : Finset V) ∩ {c,d,e} = {c} := by
      ext z
      simp only [mem_inter,mem_insert,mem_singleton]
      grind [List.nodup_cons]
    rw [he]
    simp
  let Y := (A \ Q).filter (fun y => insert y Q ∈ H)
  have hYsub : Y ⊆ A \ Q := Finset.filter_subset _ _
  have hbad : ((A \ Q) \ Y).card ≤ 1 := by
    by_contra hn
    obtain ⟨y,hy,z,hz,hyz⟩ := Finset.one_lt_card.mp (show 1 < ((A \ Q) \ Y).card by omega)
    obtain ⟨hyAQ,hyY⟩ := mem_sdiff.mp hy
    obtain ⟨hzAQ,hzY⟩ := mem_sdiff.mp hz
    obtain ⟨hyA,hyQ⟩ := mem_sdiff.mp hyAQ
    obtain ⟨hzA,hzQ⟩ := mem_sdiff.mp hzAQ
    have hyH : insert y Q ∉ H := by
      intro he
      exact hyY (Finset.mem_filter.mpr ⟨hyAQ,he⟩)
    have hzH : insert z Q ∉ H := by
      intro he
      exact hzY (Finset.mem_filter.mpr ⟨hzAQ,he⟩)
    have hyc : (insert y Q).card = 3 := by simp [hyQ,hQ]
    have hzc : (insert z Q).card = 3 := by simp [hzQ,hQ]
    have hyS : insert y Q ⊆ A := Finset.insert_subset_iff.mpr ⟨hyA,hQA⟩
    have hzS : insert z Q ⊆ A := Finset.insert_subset_iff.mpr ⟨hzA,hQA⟩
    have hyM : insert y Q = {a,b,c} ∨ insert y Q = {c,d,e} := by
      by_contra hm
      push_neg at hm
      exact hyH (hpresent _ hyS hyc hm.1 hm.2)
    have hzM : insert z Q = {a,b,c} ∨ insert z Q = {c,d,e} := by
      by_contra hm
      push_neg at hm
      exact hzH (hpresent _ hzS hzc hm.1 hm.2)
    have hne : insert y Q ≠ insert z Q := by
      intro he
      have hm : y ∈ insert z Q := by rw [←he]; simp
      simp only [mem_insert] at hm
      exact hm.elim hyz hyQ
    have hQc : Q.card ≤ (({a,b,c} : Finset V) ∩ {c,d,e}).card := by
      apply Finset.card_le_card
      intro w hw
      have hyw : w ∈ insert y Q := Finset.mem_insert_of_mem hw
      have hzw : w ∈ insert z Q := Finset.mem_insert_of_mem hw
      rcases hyM with hyM | hyM <;> rcases hzM with hzM | hzM
      · exact False.elim (hne (hyM.trans hzM.symm))
      · exact Finset.mem_inter.mpr ⟨by simpa [hyM] using hyw,by simpa [hzM] using hzw⟩
      · exact Finset.mem_inter.mpr ⟨by simpa [hzM] using hzw,by simpa [hyM] using hyw⟩
      · exact False.elim (hne (hyM.trans hzM.symm))
    rw [hQ,hmissing_inter] at hQc
    omega
  have hsum := Finset.card_sdiff_add_card_eq_card hYsub
  have hAQ : (A \ Q).card = 3 := by
    have he := Finset.card_sdiff_add_card_eq_card hQA
    have hAc : A.card = 5 := K5Support.card ⟨a,b,c,d,e,hnd,hAeq,hpresent⟩
    omega
  change 2 ≤ Y.card
  omega

/-- Published PV8 on an actual exceptional support. -/
lemma K5Support.commonPair {H : TripleSystem V} {A : Finset V} (hA : K5Support H A)
    {x y : V} (hxy : x ≠ y) (hx : x ∈ A) (hy : y ∈ A) :
    ∃ Q ⊆ A, CommonPair H x y Q := by
  obtain ⟨a,b,c,d,e,hnd,rfl,hpresent⟩ := hA
  exact Erdos643.K5Local.pattern_commonPair hnd hpresent hxy hx hy

noncomputable def mainPairs (H : TripleSystem V) : Finset (Finset V) := by
  classical
  exact (supports H).biUnion (fun A => A.powersetCard 2)

lemma mem_mainPairs {H : TripleSystem V} {S : Finset V} :
    S ∈ mainPairs H ↔ ∃ A ∈ supports H, S ⊆ A ∧ S.card = 2 := by
  classical
  simp [mainPairs]

/-- Main charged pairs also have no common-link edge after actual deletion. -/
theorem mainPairs_disjoint_Bpairs {H : TripleSystem V} (havoid : LiteralAvoids H) :
    Disjoint (mainPairs H) (Bpairs (H \ removed H)) := by
  apply disjoint_left.mpr
  intro S hS hB
  obtain ⟨A,hA,hSA,hSc⟩ := mem_mainPairs.mp hS
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hSc
  obtain ⟨_,P,hP⟩ := mem_Bpairs_pair.mp hB
  have hxA : x ∈ A := hSA (by simp)
  have hyA : y ∈ A := hSA (by simp)
  obtain ⟨Q,hQA,hQ⟩ := (mem_supports.mp hA).commonPair hxy hxA hyA
  have hPA := surviving_commonPair_outside hA hyA hP
  exact literalAvoids_not_commonMatching havoid
    ⟨x,y,hxy,P,Q,commonPair_mono Finset.sdiff_subset hP,hQ,disjoint_of_subset_right hQA hPA⟩

/-- PV11 support-intersection case two, proved using actual PV8 witnesses. -/
theorem support_intersection_ne_two {H : TripleSystem V} (havoid : LiteralAvoids H)
    {A B : Finset V} (hA : K5Support H A) (hB : K5Support H B) :
    (A ∩ B).card ≠ 2 := by
  intro hc
  obtain ⟨x,y,hxy,hAB⟩ := Finset.card_eq_two.mp hc
  have hx : x ∈ A ∩ B := by rw [hAB]; simp
  have hy : y ∈ A ∩ B := by rw [hAB]; simp
  obtain ⟨P,hPA,hP⟩ := hA.commonPair hxy (mem_inter.mp hx).1 (mem_inter.mp hy).1
  obtain ⟨Q,hQB,hQ⟩ := hB.commonPair hxy (mem_inter.mp hx).2 (mem_inter.mp hy).2
  have hPQ : Disjoint P Q := by
    apply disjoint_left.mpr
    intro z hzP hzQ
    have hz : z ∈ A ∩ B := mem_inter.mpr ⟨hPA hzP,hQB hzQ⟩
    rw [hAB] at hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hP.2.1 hzP
    · exact hP.2.2.1 hzP
  exact literalAvoids_not_commonMatching havoid ⟨x,y,hxy,P,Q,hP,hQ,hPQ⟩

/-- PV11 support-intersection case three, using the exact two-completion count. -/
theorem support_intersection_ne_three {H : TripleSystem V} (havoid : LiteralAvoids H)
    {A B : Finset V} (hA : K5Support H A) (hB : K5Support H B) :
    (A ∩ B).card ≠ 3 := by
  classical
  intro hAB
  let Q := A \ B
  have hQA : Q ⊆ A := Finset.sdiff_subset
  have hQ : Q.card = 2 := by
    have he := Finset.card_sdiff_add_card_inter A B
    have ha := hA.card
    dsimp [Q]
    omega
  have hext := hA.two_extensions hQA hQ
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp
    (show 1 < ((A \ Q).filter (fun z => insert z Q ∈ H)).card by omega)
  obtain ⟨hxAQ,hxH⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyAQ,hyH⟩ := Finset.mem_filter.mp hy
  obtain ⟨hxA,hxQ⟩ := Finset.mem_sdiff.mp hxAQ
  obtain ⟨hyA,hyQ⟩ := Finset.mem_sdiff.mp hyAQ
  have hxB : x ∈ B := by
    by_contra hn
    exact hxQ (Finset.mem_sdiff.mpr ⟨hxA,hn⟩)
  have hyB : y ∈ B := by
    by_contra hn
    exact hyQ (Finset.mem_sdiff.mpr ⟨hyA,hn⟩)
  have hC : CommonPair H x y Q := ⟨hQ,hxQ,hyQ,hxH,hyH⟩
  obtain ⟨P,hPB,hP⟩ := hB.commonPair hxy hxB hyB
  have hQP : Disjoint Q P := by
    apply Finset.disjoint_left.mpr
    intro z hzQ hzP
    exact (Finset.mem_sdiff.mp hzQ).2 (hPB hzP)
  exact literalAvoids_not_commonMatching havoid ⟨x,y,hxy,Q,P,hC,hP,hQP⟩

/-- Distinct absent triples in an exceptional support meet in exactly one
 vertex, because the only two allowed omissions do. -/
lemma K5Support.absent_intersection {H : TripleSystem V} {A E F : Finset V}
    (hA : K5Support H A) (hEA : E ⊆ A) (hFA : F ⊆ A)
    (hE : E.card = 3) (hF : F.card = 3) (hEF : E ≠ F)
    (hEH : E ∉ H) (hFH : F ∉ H) : (E ∩ F).card = 1 := by
  obtain ⟨a,b,c,d,e,hnd,hAeq,hpresent⟩ := hA
  have hEM : E = {a,b,c} ∨ E = {c,d,e} := by
    by_contra hn
    push_neg at hn
    exact hEH (hpresent E hEA hE hn.1 hn.2)
  have hFM : F = {a,b,c} ∨ F = {c,d,e} := by
    by_contra hn
    push_neg at hn
    exact hFH (hpresent F hFA hF hn.1 hn.2)
  have hi : ({a,b,c} : Finset V) ∩ {c,d,e} = {c} := by
    ext z
    simp only [mem_inter,mem_insert,mem_singleton]
    grind [List.nodup_cons]
  rcases hEM with rfl | rfl <;> rcases hFM with rfl | rfl
  · exact False.elim (hEF rfl)
  · rw [hi]; simp
  · rw [Finset.inter_comm,hi]; simp
  · exact False.elim (hEF rfl)

/-- A finite-family property used only as an intermediate combinatorial
 interface; the full source rigidity theorem must supply it in PV11. -/
def SupportsThin (H : TripleSystem V) : Prop :=
  ∀ A ∈ supports H, ∀ B ∈ supports H, A ≠ B → (A ∩ B).card ≤ 1

lemma disjoint_inside_thin_supports {H : TripleSystem V} (hthin : SupportsThin H)
    {A B P Q : Finset V} {y : V} (hA : A ∈ supports H) (hB : B ∈ supports H)
    (hAB : A ≠ B) (hyA : y ∈ A) (hyB : y ∈ B)
    (hPA : P ⊆ A) (hQB : Q ⊆ B) (hyP : y ∉ P) : Disjoint P Q := by
  apply Finset.disjoint_left.mpr
  intro z hzP hzQ
  have hyz : y ≠ z := by intro he; exact hyP (he.symm ▸ hzP)
  have hp : ({y,z} : Finset V) ⊆ A ∩ B := by
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.mem_inter]
    exact ⟨⟨hyA,hyB⟩,⟨hPA hzP,hQB hzQ⟩⟩
  have hc := Finset.card_le_card hp
  rw [Finset.card_pair hyz] at hc
  have ht := hthin A hA B hB hAB
  omega

/-- PV11 Claim 1, support uniqueness for a fixed orientation, after the
 actual support rigidity theorem is available. -/
lemma SecondaryWitness.support_unique {H : TripleSystem V} (havoid : LiteralAvoids H)
    (hthin : SupportsThin H) {x y : V} {P Q A B : Finset V}
    (hP : SecondaryWitness H x y P A) (hQ : SecondaryWitness H x y Q B) : A = B := by
  by_contra hAB
  have hPQ := disjoint_inside_thin_supports hthin hP.1 hQ.1 hAB hP.2.2.1 hQ.2.2.1
    hP.2.2.2.1 hQ.2.2.2.1 hP.2.2.2.2.2.2.1
  have hxy : x ≠ y := by intro he; exact hP.2.1 (he.symm ▸ hP.2.2.1)
  exact literalAvoids_not_commonMatching havoid ⟨x,y,hxy,P,Q,hP.2.2.2.2,hQ.2.2.2.2,hPQ⟩

/-- The two charged pair families are disjoint once support rigidity is proved. -/
lemma mainPairs_disjoint_secondaryPairs {H : TripleSystem V} (havoid : LiteralAvoids H)
    (hthin : SupportsThin H) : Disjoint (mainPairs H) (secondaryPairs H) := by
  apply Finset.disjoint_left.mpr
  intro S hM hS
  obtain ⟨_,x,y,rfl,Q,A,hA,hxA,hyA,hQA,hQ⟩ := mem_secondaryPairs.mp hS
  obtain ⟨B,hB,hSB,hSc⟩ := mem_mainPairs.mp hM
  have hxB : x ∈ B := hSB (by simp)
  have hyB : y ∈ B := hSB (by simp)
  have hAB : A ≠ B := by intro he; exact hxA (he.symm ▸ hxB)
  have hxy : x ≠ y := by intro he; exact hxA (he.symm ▸ hyA)
  obtain ⟨P,hPB,hP⟩ := (mem_supports.mp hB).commonPair hxy hxB hyB
  have hQP := disjoint_inside_thin_supports hthin hA hB hAB hyA hyB hQA hPB hQ.2.2.1
  exact literalAvoids_not_commonMatching havoid ⟨x,y,hxy,Q,P,hQ,hP,hQP⟩

noncomputable def mainTriples (H : TripleSystem V) : TripleSystem V := by
  classical
  exact H.filter (fun E => ∃ A ∈ supports H, E ⊆ A)

noncomputable def secondaryTriples (H : TripleSystem V) : TripleSystem V := by
  classical
  exact H.filter (fun E => ∃ A ∈ supports H, (E ∩ A).card = 2)

lemma mem_mainTriples {H : TripleSystem V} {E : Finset V} :
    E ∈ mainTriples H ↔ E ∈ H ∧ ∃ A ∈ supports H, E ⊆ A := by
  classical
  simp [mainTriples]

lemma mem_secondaryTriples {H : TripleSystem V} {E : Finset V} :
    E ∈ secondaryTriples H ↔ E ∈ H ∧ ∃ A ∈ supports H, (E ∩ A).card = 2 := by
  classical
  simp [secondaryTriples]

lemma removed_eq_main_union_secondary {H : TripleSystem V} (hH : Uniform H) :
    removed H = mainTriples H ∪ secondaryTriples H := by
  ext E
  constructor
  · intro hE
    obtain ⟨hEH,A,hA,hc⟩ := mem_removed.mp hE
    have hEcard := hH E hEH
    have hle : (E ∩ A).card ≤ E.card := card_le_card Finset.inter_subset_left
    by_cases heq : (E ∩ A).card = 2
    · exact Finset.mem_union_right _ (mem_secondaryTriples.mpr ⟨hEH,A,hA,heq⟩)
    · have hEA : E ⊆ A := by
        have hEq : E ∩ A = E := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
        exact Finset.inter_eq_left.mp hEq
      exact Finset.mem_union_left _ (mem_mainTriples.mpr ⟨hEH,A,hA,hEA⟩)
  · intro hE
    rcases Finset.mem_union.mp hE with hE | hE
    · obtain ⟨hEH,A,hA,hEA⟩ := mem_mainTriples.mp hE
      apply mem_removed.mpr
      refine ⟨hEH,A,hA,?_⟩
      rw [Finset.inter_eq_left.mpr hEA,hH E hEH]
      decide
    · obtain ⟨hEH,A,hA,hc⟩ := mem_secondaryTriples.mp hE
      exact mem_removed.mpr ⟨hEH,A,hA,by omega⟩

lemma mainPairs_card {H : TripleSystem V} (hthin : SupportsThin H) :
    (mainPairs H).card = 10 * (supports H).card := by
  classical
  have hd : (↑(supports H) : Set (Finset V)).PairwiseDisjoint (fun A => A.powersetCard 2) := by
    intro A hA B hB hAB
    apply Finset.disjoint_left.mpr
    intro S hSA hSB
    obtain ⟨hSA,hSc⟩ := Finset.mem_powersetCard.mp hSA
    obtain ⟨hSB,_⟩ := Finset.mem_powersetCard.mp hSB
    have hs : S ⊆ A ∩ B := by intro x hx; exact Finset.mem_inter.mpr ⟨hSA hx,hSB hx⟩
    have hc := Finset.card_le_card hs
    have ht := hthin A hA B hB hAB
    omega
  change ((supports H).biUnion (fun A => A.powersetCard 2)).card = _
  rw [Finset.card_biUnion hd]
  calc
    _ = ∑ A ∈ supports H, 10 := by
      apply Finset.sum_congr rfl
      intro A hA
      simp [(mem_supports.mp hA).card]
      norm_num [Nat.choose]
    _ = _ := by simp [Nat.mul_comm]

lemma mainTriples_card_le_mainPairs {H : TripleSystem V} (hH : Uniform H)
    (hthin : SupportsThin H) : (mainTriples H).card ≤ (mainPairs H).card := by
  classical
  have hsub : mainTriples H ⊆ (supports H).biUnion (fun A => A.powersetCard 3) := by
    intro E hE
    obtain ⟨hEH,A,hA,hEA⟩ := mem_mainTriples.mp hE
    exact Finset.mem_biUnion.mpr ⟨A,hA,Finset.mem_powersetCard.mpr ⟨hEA,hH E hEH⟩⟩
  calc
    (mainTriples H).card ≤ ((supports H).biUnion (fun A => A.powersetCard 3)).card := Finset.card_le_card hsub
    _ ≤ ∑ A ∈ supports H, (A.powersetCard 3).card := Finset.card_biUnion_le
    _ = ∑ A ∈ supports H, 10 := by
      apply Finset.sum_congr rfl
      intro A hA
      simp [(mem_supports.mp hA).card]
      norm_num [Nat.choose]
    _ = 10 * (supports H).card := by simp [Nat.mul_comm]
    _ = (mainPairs H).card := (mainPairs_card hthin).symm

/-- Two distinct absent pairs in one vertex-link of a K5-minus support
 must be disjoint. This is the exact missing-matching fact in the reviewed
 alternative four-intersection proof. -/
lemma K5Support.absent_link_pairs_disjoint {H : TripleSystem V} {A P Q : Finset V} {a : V}
    (hA : K5Support H A) (hP : P.card = 2) (hQ : Q.card = 2)
    (haP : a ∉ P) (haQ : a ∉ Q) (hPA : insert a P ⊆ A) (hQA : insert a Q ⊆ A)
    (hPQ : P ≠ Q) (hPH : insert a P ∉ H) (hQH : insert a Q ∉ H) : Disjoint P Q := by
  have hne : insert a P ≠ insert a Q := by
    intro he
    have he' := congrArg (Finset.erase · a) he
    simp only [Finset.erase_insert haP,Finset.erase_insert haQ] at he'
    exact hPQ he'
  have hi := hA.absent_intersection hPA hQA (by simp [haP,hP]) (by simp [haQ,hQ]) hne hPH hQH
  apply Finset.disjoint_left.mpr
  intro z hzP hzQ
  have haz : a ≠ z := by intro he; exact haP (he.symm ▸ hzP)
  have hsub : ({a,z} : Finset V) ⊆ insert a P ∩ insert a Q := by
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.mem_inter]
    exact ⟨⟨by simp,by simp⟩,⟨Finset.mem_insert_of_mem hzP,Finset.mem_insert_of_mem hzQ⟩⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair haz,hi] at hc
  omega

/-- Any two different perfect matchings of the four other support vertices
 cannot both be blocked in this vertex-link. -/
lemma K5Support.two_matchings {H : TripleSystem V} {A : Finset V} {a u v w z : V}
    (hA : K5Support H A) (hset : A = {a,u,v,w,z}) (hnd : [a,u,v,w,z].Nodup) :
    (insert a ({u,v} : Finset V) ∈ H ∧ insert a ({w,z} : Finset V) ∈ H) ∨
    (insert a ({u,w} : Finset V) ∈ H ∧ insert a ({v,z} : Finset V) ∈ H) := by
  classical
  simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,not_or,and_true] at hnd
  by_contra hn
  have h0 : insert a ({u,v} : Finset V) ∉ H ∨ insert a ({w,z} : Finset V) ∉ H := by tauto
  have h1 : insert a ({u,w} : Finset V) ∉ H ∨ insert a ({v,z} : Finset V) ∉ H := by tauto
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · have hne : ({u,v} : Finset V) ≠ {u,w} := by
      intro he
      have hm : v ∈ ({u,w} : Finset V) := by rw [←he]; simp
      grind [Finset.mem_insert,Finset.mem_singleton]
    have hd := hA.absent_link_pairs_disjoint (P:={u,v}) (Q:={u,w})
      (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp [hset,Finset.insert_subset_iff]) (by simp [hset,Finset.insert_subset_iff]) hne h0 h1
    exact Finset.disjoint_left.mp hd (by simp : u ∈ ({u,v} : Finset V)) (by simp)
  · have hne : ({u,v} : Finset V) ≠ {v,z} := by
      intro he
      have hm : u ∈ ({v,z} : Finset V) := by rw [←he]; simp
      grind [Finset.mem_insert,Finset.mem_singleton]
    have hd := hA.absent_link_pairs_disjoint (P:={u,v}) (Q:={v,z})
      (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp [hset,Finset.insert_subset_iff]) (by simp [hset,Finset.insert_subset_iff]) hne h0 h1
    exact Finset.disjoint_left.mp hd (by simp : v ∈ ({u,v} : Finset V)) (by simp)
  · have hne : ({w,z} : Finset V) ≠ {u,w} := by
      intro he
      have hm : z ∈ ({u,w} : Finset V) := by rw [←he]; simp
      grind [Finset.mem_insert,Finset.mem_singleton]
    have hd := hA.absent_link_pairs_disjoint (P:={w,z}) (Q:={u,w})
      (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp [hset,Finset.insert_subset_iff]) (by simp [hset,Finset.insert_subset_iff]) hne h0 h1
    exact Finset.disjoint_left.mp hd (by simp : w ∈ ({w,z} : Finset V)) (by simp)
  · have hne : ({w,z} : Finset V) ≠ {v,z} := by
      intro he
      have hm : w ∈ ({v,z} : Finset V) := by rw [←he]; simp
      grind [Finset.mem_insert,Finset.mem_singleton]
    have hd := hA.absent_link_pairs_disjoint (P:={w,z}) (Q:={v,z})
      (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp [hset,Finset.insert_subset_iff]) (by simp [hset,Finset.insert_subset_iff]) hne h0 h1
    exact Finset.disjoint_left.mp hd (by simp : z ∈ ({w,z} : Finset V)) (by simp)

lemma K5Support.three_matchings {H : TripleSystem V} {A : Finset V} {a u v w z : V}
    (hA : K5Support H A) (hset : A = {a,u,v,w,z}) (hnd : [a,u,v,w,z].Nodup) :
    ((insert a ({u,v} : Finset V) ∈ H ∧ insert a ({w,z} : Finset V) ∈ H) ∨
      (insert a ({u,w} : Finset V) ∈ H ∧ insert a ({v,z} : Finset V) ∈ H)) ∧
    ((insert a ({u,v} : Finset V) ∈ H ∧ insert a ({w,z} : Finset V) ∈ H) ∨
      (insert a ({u,z} : Finset V) ∈ H ∧ insert a ({v,w} : Finset V) ∈ H)) ∧
    ((insert a ({u,w} : Finset V) ∈ H ∧ insert a ({v,z} : Finset V) ∈ H) ∨
      (insert a ({u,z} : Finset V) ∈ H ∧ insert a ({v,w} : Finset V) ∈ H)) := by
  have hset1 : A = {a,u,v,z,w} := by
    rw [hset]
    ext t
    simp only [Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hset2 : A = {a,u,w,z,v} := by
    rw [hset]
    ext t
    simp only [Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hnd1 : [a,u,v,z,w].Nodup := by grind [List.nodup_cons]
  have hnd2 : [a,u,w,z,v].Nodup := by grind [List.nodup_cons]
  refine ⟨hA.two_matchings hset hnd,?_,?_⟩
  · simpa only [Finset.pair_comm] using hA.two_matchings hset1 hnd1
  · simpa only [Finset.pair_comm] using hA.two_matchings hset2 hnd2

lemma common_of_two_out_of_three {A0 A1 A2 B0 B1 B2 : Prop}
    (hA : (A0 ∨ A1) ∧ (A0 ∨ A2) ∧ (A1 ∨ A2))
    (hB : (B0 ∨ B1) ∧ (B0 ∨ B2) ∧ (B1 ∨ B2)) :
    (A0 ∧ B0) ∨ (A1 ∧ B1) ∨ (A2 ∧ B2) := by
  tauto

set_option maxHeartbeats 1200000 in
/-- The two supports' outside links share a full perfect matching on their
 four common vertices, giving the literal six-vertex forbidden witness. -/
lemma common_four_supports_impossible {H : TripleSystem V} (havoid : LiteralAvoids H)
    {a b u v w z : V} (hnd : [a,b,u,v,w,z].Nodup)
    (hA : K5Support H {a,u,v,w,z}) (hB : K5Support H {b,u,v,w,z}) : False := by
  have hndA : [a,u,v,w,z].Nodup := by grind [List.nodup_cons]
  have hndB : [b,u,v,w,z].Nodup := by grind [List.nodup_cons]
  have hAM := hA.three_matchings rfl hndA
  have hBM := hB.three_matchings rfl hndB
  have hcommon :
      ((insert a ({u,v} : Finset V) ∈ H ∧ insert a ({w,z} : Finset V) ∈ H) ∧
       (insert b ({u,v} : Finset V) ∈ H ∧ insert b ({w,z} : Finset V) ∈ H)) ∨
      ((insert a ({u,w} : Finset V) ∈ H ∧ insert a ({v,z} : Finset V) ∈ H) ∧
       (insert b ({u,w} : Finset V) ∈ H ∧ insert b ({v,z} : Finset V) ∈ H)) ∨
      ((insert a ({u,z} : Finset V) ∈ H ∧ insert a ({v,w} : Finset V) ∈ H) ∧
       (insert b ({u,z} : Finset V) ∈ H ∧ insert b ({v,w} : Finset V) ∈ H)) :=
    common_of_two_out_of_three hAM hBM
  have hab : a ≠ b := by grind [List.nodup_cons]
  have hau : a ≠ u := by grind [List.nodup_cons]
  have hav : a ≠ v := by grind [List.nodup_cons]
  have haw : a ≠ w := by grind [List.nodup_cons]
  have haz : a ≠ z := by grind [List.nodup_cons]
  have hbu : b ≠ u := by grind [List.nodup_cons]
  have hbv : b ≠ v := by grind [List.nodup_cons]
  have hbw : b ≠ w := by grind [List.nodup_cons]
  have hbz : b ≠ z := by grind [List.nodup_cons]
  have huv : u ≠ v := by grind [List.nodup_cons]
  have huw : u ≠ w := by grind [List.nodup_cons]
  have huz : u ≠ z := by grind [List.nodup_cons]
  have hvw : v ≠ w := by grind [List.nodup_cons]
  have hvz : v ≠ z := by grind [List.nodup_cons]
  have hwz : w ≠ z := by grind [List.nodup_cons]
  rcases hcommon with h | h | h
  · exact literalAvoids_not_commonMatching havoid
      ⟨a,b,hab,{u,v},{w,z},
       ⟨by simp [huv],by simp [hau,hav],by simp [hbu,hbv],h.1.1,h.2.1⟩,
       ⟨by simp [hwz],by simp [haw,haz],by simp [hbw,hbz],h.1.2,h.2.2⟩,
       by simp [Finset.disjoint_insert_left,Finset.disjoint_singleton_left,huv,huw,huz,hvw,hvz,hwz,
         Ne.symm huv,Ne.symm huw,Ne.symm huz,Ne.symm hvw,Ne.symm hvz,Ne.symm hwz]⟩
  · exact literalAvoids_not_commonMatching havoid
      ⟨a,b,hab,{u,w},{v,z},
       ⟨by simp [huw],by simp [hau,haw],by simp [hbu,hbw],h.1.1,h.2.1⟩,
       ⟨by simp [hvz],by simp [hav,haz],by simp [hbv,hbz],h.1.2,h.2.2⟩,
       by simp [Finset.disjoint_insert_left,Finset.disjoint_singleton_left,huv,huw,huz,hvw,hvz,hwz,
         Ne.symm huv,Ne.symm huw,Ne.symm huz,Ne.symm hvw,Ne.symm hvz,Ne.symm hwz]⟩
  · exact literalAvoids_not_commonMatching havoid
      ⟨a,b,hab,{u,z},{v,w},
       ⟨by simp [huz],by simp [hau,haz],by simp [hbu,hbz],h.1.1,h.2.1⟩,
       ⟨by simp [hvw],by simp [hav,haw],by simp [hbv,hbw],h.1.2,h.2.2⟩,
       by simp [Finset.disjoint_insert_left,Finset.disjoint_singleton_left,huv,huw,huz,hvw,hvz,hwz,
         Ne.symm huv,Ne.symm huw,Ne.symm huz,Ne.symm hvw,Ne.symm hvz,Ne.symm hwz]⟩

theorem support_intersection_ne_four {H : TripleSystem V} (havoid : LiteralAvoids H)
    {A B : Finset V} (hA : K5Support H A) (hB : K5Support H B) :
    (A ∩ B).card ≠ 4 := by
  intro hAB
  obtain ⟨u,v,w,z,huv,huw,huz,hvw,hvz,hwz,hX⟩ := Finset.card_eq_four.mp hAB
  have hAs : (A \ B).card = 1 := by
    have he := Finset.card_sdiff_add_card_inter A B
    have ha := hA.card
    omega
  have hBs : (B \ A).card = 1 := by
    have he := Finset.card_sdiff_add_card_inter B A
    have hb := hB.card
    rw [Finset.inter_comm B A] at he
    omega
  obtain ⟨a,haEq⟩ := Finset.card_eq_one.mp hAs
  obtain ⟨b,hbEq⟩ := Finset.card_eq_one.mp hBs
  have ha : a ∈ A ∧ a ∉ B := Finset.mem_sdiff.mp (by rw [haEq]; simp)
  have hb : b ∈ B ∧ b ∉ A := Finset.mem_sdiff.mp (by rw [hbEq]; simp)
  have hab : a ≠ b := by intro he; exact ha.2 (he.symm ▸ hb.1)
  have haX : a ∉ ({u,v,w,z} : Finset V) := by
    intro hx
    exact ha.2 (Finset.mem_inter.mp (by rw [hX]; exact hx)).2
  have hbX : b ∉ ({u,v,w,z} : Finset V) := by
    intro hx
    exact hb.2 (Finset.mem_inter.mp (by rw [hX]; exact hx)).1
  have hsetA : A = {a,u,v,w,z} := by
    calc
      A = (A \ B) ∪ (A ∩ B) := by ext t; simp only [mem_union,mem_sdiff,mem_inter]; tauto
      _ = _ := by rw [haEq,hX]; simp only [Finset.singleton_union]
  have hsetB : B = {b,u,v,w,z} := by
    calc
      B = (B \ A) ∪ (A ∩ B) := by ext t; simp only [mem_union,mem_sdiff,mem_inter]; tauto
      _ = _ := by rw [hbEq,hX]; simp only [Finset.singleton_union]
  have hnd : [a,b,u,v,w,z].Nodup := by
    simp only [mem_insert,mem_singleton,not_or] at haX hbX
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,and_true]
    tauto
  exact common_four_supports_impossible havoid hnd (hsetA ▸ hA) (hsetB ▸ hB)

/-- Full exact support rigidity, including the reviewed alternative
 four-intersection argument and the source-faithful two/three cases. -/
theorem supports_thin {H : TripleSystem V} (havoid : LiteralAvoids H) : SupportsThin H := by
  intro A hA B hB hAB
  have hAS := mem_supports.mp hA
  have hBS := mem_supports.mp hB
  have ha := hAS.card
  have hb := hBS.card
  have hle : (A ∩ B).card ≤ 5 := (Finset.card_le_card Finset.inter_subset_left).trans (by omega)
  have hne2 := support_intersection_ne_two havoid hAS hBS
  have hne3 := support_intersection_ne_three havoid hAS hBS
  have hne4 := support_intersection_ne_four havoid hAS hBS
  have hne5 : (A ∩ B).card ≠ 5 := by
    intro hc
    have hi : A ∩ B = A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hsub : A ⊆ B := Finset.inter_eq_left.mp hi
    exact hAB (Finset.eq_of_subset_of_card_le hsub (by omega))
  omega

lemma pair_eq_with_member {P : Finset V} (hc : P.card = 2) {u : V} (hu : u ∈ P) :
    ∃ v, v ≠ u ∧ P = {u,v} := by
  obtain ⟨a,b,hab,hP⟩ := Finset.card_eq_two.mp hc
  have hu' : u = a ∨ u = b := by simpa [hP] using hu
  rcases hu' with rfl | rfl
  · exact ⟨b,hab.symm,hP⟩
  · exact ⟨a,hab,by simpa only [Finset.pair_comm] using hP⟩

lemma other_member_of_intersect {P : Finset V} {u v : V}
    (h : ¬ Disjoint ({u,v} : Finset V) P) (hu : u ∉ P) : v ∈ P := by
  by_contra hv
  apply h
  apply Finset.disjoint_left.mpr
  intro z hz hzP
  simp only [Finset.mem_insert,Finset.mem_singleton] at hz
  exact hz.elim (fun he => hu (he ▸ hzP)) (fun he => hv (he ▸ hzP))

/-- The triangle alternative in PV11's local three-witness argument. -/
lemma triangle_configuration_impossible {H : TripleSystem V} (havoid : LiteralAvoids H)
    {A T : Finset V} {x y : V} (hA : K5Support H A) (hTA : T ⊆ A)
    (hx : x ∉ A) (hy : y ∈ A) (hPi : Pi H T {x,y}) : False := by
  classical
  have hyT : y ∉ T := by
    intro hyT
    exact Finset.disjoint_left.mp hPi.disjoint hyT (by simp)
  have hiA : insert y T ⊆ A := Finset.insert_subset_iff.mpr ⟨hy,hTA⟩
  have hiCard : (insert y T).card = 4 := by simp [hyT,hPi.root_card]
  have hzCard : (A \ insert y T).card = 1 := by
    have he := Finset.card_sdiff_add_card_eq_card hiA
    have ha := hA.card
    omega
  obtain ⟨z,hzEq⟩ := Finset.card_eq_one.mp hzCard
  have hz : z ∈ A ∧ z ∉ insert y T := Finset.mem_sdiff.mp (by rw [hzEq]; simp)
  have hzy : z ≠ y := fun he => hz.2 (by simp [he])
  have hzT : z ∉ T := fun hzT => hz.2 (Finset.mem_insert_of_mem hzT)
  let Q : Finset V := {y,z}
  have hQA : Q ⊆ A := by simp only [Q,Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨hy,hz.1⟩
  have hQ : Q.card = 2 := by simp [Q,Ne.symm hzy]
  have hTQ : T ⊆ A \ Q := by
    intro t ht
    apply Finset.mem_sdiff.mpr
    refine ⟨hTA ht,?_⟩
    simp only [Q,Finset.mem_insert,Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact hyT ht
    · exact hzT ht
  have hComp : A \ Q = T := (Finset.eq_of_subset_of_card_le hTQ (by
    have he := Finset.card_sdiff_add_card_eq_card hQA
    have ha := hA.card
    have ht := hPi.root_card
    omega)).symm
  have hext := hA.two_extensions hQA hQ
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp
    (show 1 < ((A \ Q).filter (fun t => insert t Q ∈ H)).card by omega)
  obtain ⟨haC,haH⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbC,hbH⟩ := Finset.mem_filter.mp hb
  have haT : a ∈ T := by simpa only [hComp] using haC
  have hbT : b ∈ T := by simpa only [hComp] using hbC
  obtain ⟨c,hca,hcb,hTset⟩ := PrivatePairs.triple_of_pair_subset hPi.root_card hab haT hbT
  have hcT : c ∈ T := by simp [hTset]
  have hC : CommonPair H a b Q := ⟨hQ,(Finset.mem_sdiff.mp haC).2,(Finset.mem_sdiff.mp hbC).2,haH,hbH⟩
  have hD : CommonPair H a b {x,c} := hPi.rootCommonPair hTset hab hca.symm hcb.symm (by simp)
  have hxQ : x ∉ Q := fun hxQ => hx (hQA hxQ)
  have hcQ : c ∉ Q := (Finset.mem_sdiff.mp (hTQ hcT)).2
  have hd : Disjoint ({x,c} : Finset V) Q := by
    simp only [Finset.disjoint_insert_left,Finset.disjoint_singleton_left]
    exact ⟨hxQ,hcQ⟩
  exact literalAvoids_not_commonMatching havoid ⟨a,b,hab,{x,c},Q,hD,hC,hd⟩

lemma triangle_witnesses_impossible {H : TripleSystem V} (havoid : LiteralAvoids H)
    {A : Finset V} {x y u v w : V} (hA : K5Support H A) (hx : x ∉ A) (hy : y ∈ A)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (huvA : ({u,v} : Finset V) ⊆ A) (huwA : ({u,w} : Finset V) ⊆ A)
    (hP : CommonPair H x y {u,v}) (hQ : CommonPair H x y {u,w})
    (hR : CommonPair H x y {v,w}) : False := by
  have hxy : x ≠ y := by intro he; exact hx (he.symm ▸ hy)
  have hTA : ({u,v,w} : Finset V) ⊆ A := by
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨huvA (by simp),huvA (by simp),huwA (by simp)⟩
  have hfaces : ∀ S ⊆ ({u,v,w} : Finset V), S.card = 2 → CommonPair H x y S := by
    intro S hST hSc
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hSc
    have ha : a = u ∨ a = v ∨ a = w := by simpa using hST (by simp : a ∈ ({a,b} : Finset V))
    have hb : b = u ∨ b = v ∨ b = w := by simpa using hST (by simp : b ∈ ({a,b} : Finset V))
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first
      | exact False.elim (hab rfl)
      | simpa only [Finset.pair_comm] using hP
      | simpa only [Finset.pair_comm] using hQ
      | simpa only [Finset.pair_comm] using hR
  have hPi : Pi H {u,v,w} {x,y} := by
    refine ⟨by simp [huv,huw,hvw],by simp [hxy],?_,?_⟩
    · apply Finset.disjoint_left.mpr
      intro t ht htk
      have htA := hTA ht
      simp only [Finset.mem_insert,Finset.mem_singleton] at htk ht
      rcases htk with rfl | rfl
      · exact hx htA
      · rcases ht with rfl | rfl | rfl
        · exact hP.2.2.1 (by simp)
        · exact hP.2.2.1 (by simp)
        · exact hQ.2.2.1 (by simp)
    · intro S hST hSc a ha
      have hC := hfaces S hST hSc
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hC.2.2.2.1
      · exact hC.2.2.2.2
  exact triangle_configuration_impossible havoid hA hTA hx hy hPi

lemma two_of_three {P Q R : Prop} (h : (P ∨ Q) ∧ (P ∨ R) ∧ (Q ∨ R)) :
    (P ∧ Q) ∨ (P ∧ R) ∨ (Q ∧ R) := by tauto

/-- Actual six-vertex witness in the star alternative of PV11 Claim1. -/
lemma star_two_faces_impossible {H : TripleSystem V} (havoid : LiteralAvoids H)
    {x y u v w z : V} (hnd : [x,y,u,v,w,z].Nodup)
    (hP : CommonPair H x y {u,v}) (hQ : CommonPair H x y {u,w})
    (hE : insert y ({v,z} : Finset V) ∈ H) (hF : insert y ({w,z} : Finset V) ∈ H) : False := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,and_true] at hnd
  have hxy : x ≠ y := by tauto
  have hxu : x ≠ u := by tauto
  have hxv : x ≠ v := by tauto
  have hxw : x ≠ w := by tauto
  have hxz : x ≠ z := by tauto
  have hyu : y ≠ u := by tauto
  have hyv : y ≠ v := by tauto
  have hyw : y ≠ w := by tauto
  have hyz : y ≠ z := by tauto
  have huv : u ≠ v := by tauto
  have huw : u ≠ w := by tauto
  have huz : u ≠ z := by tauto
  have hvw : v ≠ w := by tauto
  have hvz : v ≠ z := by tauto
  have hwz : w ≠ z := by tauto
  have hC : CommonPair H v w {x,u} := by
    refine ⟨by simp [hxu],by simp [Ne.symm hxv,Ne.symm huv],by simp [Ne.symm hxw,Ne.symm huw],?_,?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hP.2.2.2.1
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hQ.2.2.2.1
  have hD : CommonPair H v w {y,z} := by
    refine ⟨by simp [hyz],by simp [Ne.symm hyv,hvz],by simp [Ne.symm hyw,hwz],?_,?_⟩
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hE
    · simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hF
  have hd : Disjoint ({x,u} : Finset V) {y,z} := by
    simp [Finset.disjoint_insert_left,Finset.disjoint_singleton_left,hxy,hxz,Ne.symm hyu,huz,Ne.symm hxy,Ne.symm hxz,hyu,Ne.symm huz]
  exact literalAvoids_not_commonMatching havoid ⟨v,w,hvw,{x,u},{y,z},hC,hD,hd⟩

lemma star_witnesses_impossible {H : TripleSystem V} (havoid : LiteralAvoids H)
    {A : Finset V} {x y u v w z : V} (hA : K5Support H A)
    (hset : A = {y,u,v,w,z}) (hnd : [y,u,v,w,z].Nodup) (hx : x ∉ A)
    (hP : CommonPair H x y {u,v}) (hQ : CommonPair H x y {u,w})
    (hR : CommonPair H x y {u,z}) : False := by
  have hnd6 : [x,y,u,v,w,z].Nodup := by
    rw [hset] at hx
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hx
    grind [List.nodup_cons]
  have hm := two_of_three (hA.three_matchings hset hnd)
  rcases hm with hm | hm | hm
  · exact star_two_faces_impossible havoid hnd6 hP hQ hm.2.2 hm.1.2
  · exact star_two_faces_impossible havoid
      (show [x,y,u,z,v,w].Nodup by grind [List.nodup_cons]) hR hP
      (by simpa only [Finset.pair_comm] using hm.1.2) hm.2.2
  · exact star_two_faces_impossible havoid
      (show [x,y,u,z,w,v].Nodup by grind [List.nodup_cons]) hR hQ
      (by simpa only [Finset.pair_comm] using hm.1.2)
      (by simpa only [Finset.pair_comm] using hm.2.2)
noncomputable def witnessPairs (H : TripleSystem V) (x y : V) (A : Finset V) : Finset (Finset V) := by
  classical
  exact (A.powersetCard 2).filter (CommonPair H x y)

lemma mem_witnessPairs {H : TripleSystem V} {x y : V} {A Q : Finset V} :
    Q ∈ witnessPairs H x y A ↔ Q ⊆ A ∧ CommonPair H x y Q := by
  classical
  simp only [witnessPairs,Finset.mem_filter,Finset.mem_powersetCard]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.1⟩,h.2⟩⟩

/-- PV11 Claim1's at-most-two witness-pair clause, fully supplied from the
 published triangle/star argument with all actual vertex supports. -/
theorem witnessPairs_card_le_two {H : TripleSystem V} (havoid : LiteralAvoids H)
    {A : Finset V} {x y : V} (hA : K5Support H A) (hx : x ∉ A) (hy : y ∈ A) :
    (witnessPairs H x y A).card ≤ 2 := by
  classical
  by_contra hn
  obtain ⟨P,Q,R,hP,hQ,hR,hPQ,hPR,hQR⟩ := Finset.two_lt_card_iff.mp
    (show 2 < (witnessPairs H x y A).card by omega)
  obtain ⟨hPA,hCP⟩ := mem_witnessPairs.mp hP
  obtain ⟨hQA,hCQ⟩ := mem_witnessPairs.mp hQ
  obtain ⟨hRA,hCR⟩ := mem_witnessPairs.mp hR
  have hxy : x ≠ y := by intro he; exact hx (he.symm ▸ hy)
  have hiPQ := PrivatePairs.commonPairs_intersect havoid hxy hCP hCQ
  have hiPR := PrivatePairs.commonPairs_intersect havoid hxy hCP hCR
  have hiQR := PrivatePairs.commonPairs_intersect havoid hxy hCQ hCR
  obtain ⟨u,huP,huQ⟩ := Finset.not_disjoint_iff.mp hiPQ
  obtain ⟨v,hvu,hPeq⟩ := pair_eq_with_member hCP.1 huP
  obtain ⟨w,hwu,hQeq⟩ := pair_eq_with_member hCQ.1 huQ
  have hvw : v ≠ w := by intro he; exact hPQ (by rw [hPeq,hQeq,he])
  have huA : u ∈ A := hPA (by rw [hPeq]; simp)
  have hvA : v ∈ A := hPA (by rw [hPeq]; simp)
  have hwA : w ∈ A := hQA (by rw [hQeq]; simp)
  by_cases huR : u ∈ R
  · obtain ⟨z,hzu,hReq⟩ := pair_eq_with_member hCR.1 huR
    have hzv : z ≠ v := by intro he; exact hPR (by rw [hPeq,hReq,he])
    have hzw : z ≠ w := by intro he; exact hQR (by rw [hQeq,hReq,he])
    have hzA : z ∈ A := hRA (by rw [hReq]; simp)
    have hyu : y ≠ u := by intro he; exact hCP.2.2.1 (by rw [hPeq]; simp [he])
    have hyv : y ≠ v := by intro he; exact hCP.2.2.1 (by rw [hPeq]; simp [he])
    have hyw : y ≠ w := by intro he; exact hCQ.2.2.1 (by rw [hQeq]; simp [he])
    have hyz : y ≠ z := by intro he; exact hCR.2.2.1 (by rw [hReq]; simp [he])
    have hnd : [y,u,v,w,z].Nodup := by
      simp [List.nodup_cons,hyu,hyv,hyw,hyz,Ne.symm hvu,Ne.symm hwu,Ne.symm hzu,hvw,Ne.symm hzv,Ne.symm hzw]
    have hsub : ({y,u,v,w,z} : Finset V) ⊆ A := by
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨hy,huA,hvA,hwA,hzA⟩
    have hc : ({y,u,v,w,z} : Finset V).card = 5 := by simpa using List.toFinset_card_of_nodup hnd
    have hset : A = {y,u,v,w,z} := (Finset.eq_of_subset_of_card_le hsub (by rw [hA.card,hc])).symm
    exact star_witnesses_impossible havoid hA hset hnd hx
      (by simpa only [hPeq] using hCP) (by simpa only [hQeq] using hCQ) (by simpa only [hReq] using hCR)
  · have hvR : v ∈ R := other_member_of_intersect (by simpa only [hPeq] using hiPR) huR
    have hwR : w ∈ R := other_member_of_intersect (by simpa only [hQeq] using hiQR) huR
    have hReq : R = {v,w} := (Finset.eq_of_subset_of_card_le
      (show ({v,w} : Finset V) ⊆ R by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨hvR,hwR⟩)
      (by simp [hCR.1,hvw])).symm
    exact triangle_witnesses_impossible havoid hA hx hy (Ne.symm hvu) (Ne.symm hwu) hvw
      (by simpa only [hPeq] using hPA) (by simpa only [hQeq] using hQA)
      (by simpa only [hPeq] using hCP) (by simpa only [hQeq] using hCQ) (by simpa only [hReq] using hCR)

/-- Actual PV11 incidence, with the secondary triple and pair both retained. -/
def Incidence (H : TripleSystem V) (E S : Finset V) : Prop :=
  ∃ x y, S = {x,y} ∧ ∃ Q A, SecondaryWitness H x y Q A ∧ E = insert x Q

lemma SecondaryWitness.edge_secondary {H : TripleSystem V} {x y : V} {Q A : Finset V}
    (hW : SecondaryWitness H x y Q A) : insert x Q ∈ secondaryTriples H := by
  have hi : insert x Q ∩ A = Q := by
    ext z
    simp only [Finset.mem_inter,Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hz,hzA⟩
      · exact False.elim (hW.2.1 hzA)
      · exact hz
    · intro hz
      exact ⟨Or.inr hz,hW.2.2.2.1 hz⟩
  exact mem_secondaryTriples.mpr ⟨hW.2.2.2.2.2.2.2.1,A,hW.1,by rw [hi]; exact hW.2.2.2.2.1⟩

lemma SecondaryWitness.pair_secondary {H : TripleSystem V} {x y : V} {Q A : Finset V}
    (hW : SecondaryWitness H x y Q A) : ({x,y} : Finset V) ∈ secondaryPairs H := by
  have hxy : x ≠ y := by intro he; exact hW.2.1 (he.symm ▸ hW.2.2.1)
  exact mem_secondaryPairs.mpr ⟨mem_Bpairs_pair.mpr ⟨hxy,Q,hW.2.2.2.2⟩,x,y,rfl,Q,A,hW⟩

noncomputable def incidentPairs (H : TripleSystem V) (E : Finset V) : Finset (Finset V) := by
  classical
  exact (secondaryPairs H).filter (Incidence H E)

noncomputable def incidentTriples (H : TripleSystem V) (S : Finset V) : Finset (Finset V) := by
  classical
  exact (secondaryTriples H).filter (fun E => Incidence H E S)

noncomputable def orientedEdges (H : TripleSystem V) (x y : V) : Finset (Finset V) := by
  classical
  exact H.filter (fun E => ∃ Q A, SecondaryWitness H x y Q A ∧ E = insert x Q)

lemma mem_orientedEdges {H : TripleSystem V} {x y : V} {E : Finset V} :
    E ∈ orientedEdges H x y ↔ ∃ Q A, SecondaryWitness H x y Q A ∧ E = insert x Q := by
  classical
  simp only [orientedEdges,Finset.mem_filter]
  constructor
  · exact And.right
  · rintro ⟨Q,A,hW,rfl⟩
    exact ⟨hW.2.2.2.2.2.2.2.1,Q,A,hW,rfl⟩

lemma orientedEdges_card_le_two {H : TripleSystem V} (havoid : LiteralAvoids H) (x y : V) :
    (orientedEdges H x y).card ≤ 2 := by
  classical
  by_cases hex : ∃ Q A, SecondaryWitness H x y Q A
  · obtain ⟨Q0,A0,hW0⟩ := hex
    have hsub : orientedEdges H x y ⊆ (witnessPairs H x y A0).image (insert x) := by
      intro E hE
      obtain ⟨Q,A,hW,rfl⟩ := mem_orientedEdges.mp hE
      have he := SecondaryWitness.support_unique havoid (supports_thin havoid) hW hW0
      subst A
      exact Finset.mem_image.mpr ⟨Q,mem_witnessPairs.mpr ⟨hW.2.2.2.1,hW.2.2.2.2⟩,rfl⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans
      (witnessPairs_card_le_two havoid (mem_supports.mp hW0.1) hW0.2.1 hW0.2.2.1))
  · have he : orientedEdges H x y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro E hE
      obtain ⟨Q,A,hW,_⟩ := mem_orientedEdges.mp hE
      exact hex ⟨Q,A,hW⟩
    simp [he]

lemma incidence_pair_iff {H : TripleSystem V} {E : Finset V} {x y : V} (hxy : x ≠ y) :
    Incidence H E {x,y} ↔ E ∈ orientedEdges H x y ∨ E ∈ orientedEdges H y x := by
  constructor
  · rintro ⟨a,b,he,Q,A,hW,hE⟩
    have hx : x = a ∨ x = b := by
      have hm : x ∈ ({a,b} : Finset V) := by rw [←he]; simp
      simpa using hm
    have hy : y = a ∨ y = b := by
      have hm : y ∈ ({a,b} : Finset V) := by rw [←he]; simp
      simpa using hm
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (hxy rfl)
    · exact Or.inl (mem_orientedEdges.mpr ⟨Q,A,hW,hE⟩)
    · exact Or.inr (mem_orientedEdges.mpr ⟨Q,A,hW,hE⟩)
    · exact False.elim (hxy rfl)
  · rintro (hE | hE)
    · obtain ⟨Q,A,hW,hE⟩ := mem_orientedEdges.mp hE
      exact ⟨x,y,rfl,Q,A,hW,hE⟩
    · obtain ⟨Q,A,hW,hE⟩ := mem_orientedEdges.mp hE
      exact ⟨y,x,Finset.pair_comm x y,Q,A,hW,hE⟩

lemma incidentTriples_card_le_four {H : TripleSystem V} (havoid : LiteralAvoids H)
    {x y : V} (hxy : x ≠ y) : (incidentTriples H {x,y}).card ≤ 4 := by
  classical
  have hsub : incidentTriples H {x,y} ⊆ orientedEdges H x y ∪ orientedEdges H y x := by
    intro E hE
    have hI := (Finset.mem_filter.mp hE).2
    exact Finset.mem_union.mpr ((incidence_pair_iff hxy).mp hI)
  have h0 := orientedEdges_card_le_two havoid x y
  have h1 := orientedEdges_card_le_two havoid y x
  have h2 := Finset.card_union_le (orientedEdges H x y) (orientedEdges H y x)
  have h3 := Finset.card_le_card hsub
  omega

lemma incidentTriples_card_le_two {H : TripleSystem V} (havoid : LiteralAvoids H)
    {x y : V} (hxy : x ≠ y) (hrev : ¬ ∃ Q A, SecondaryWitness H y x Q A) :
    (incidentTriples H {x,y}).card ≤ 2 := by
  classical
  have hsub : incidentTriples H {x,y} ⊆ orientedEdges H x y := by
    intro E hE
    rcases (incidence_pair_iff hxy).mp (Finset.mem_filter.mp hE).2 with hf | hr
    · exact hf
    · obtain ⟨Q,A,hW,_⟩ := mem_orientedEdges.mp hr
      exact False.elim (hrev ⟨Q,A,hW⟩)
  exact (Finset.card_le_card hsub).trans (orientedEdges_card_le_two havoid x y)
lemma pair_fixed_injective (x : V) : Function.Injective (fun y : V => ({x,y} : Finset V)) := by
  intro a b he
  dsimp only at he
  by_cases ha : a = x
  · have hb : b ∈ ({x,a} : Finset V) := by rw [he]; simp
    simp [ha] at hb
    exact ha.trans hb.symm
  · have hm : a ∈ ({x,b} : Finset V) := by rw [←he]; simp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    exact hm.resolve_left ha

noncomputable def extensionPairs (H : TripleSystem V) (x : V) (A Q : Finset V) : Finset (Finset V) := by
  classical
  exact ((A \ Q).filter (fun y => insert y Q ∈ H)).image (fun y => ({x,y} : Finset V))

lemma extensionPairs_card_ge_two {H : TripleSystem V} {x : V} {A Q : Finset V}
    (hA : K5Support H A) (hQA : Q ⊆ A) (hQ : Q.card = 2) :
    2 ≤ (extensionPairs H x A Q).card := by
  classical
  change 2 ≤ (((A \ Q).filter (fun y => insert y Q ∈ H)).image (fun y => ({x,y} : Finset V))).card
  rw [Finset.card_image_of_injective _ (pair_fixed_injective x)]
  exact hA.two_extensions hQA hQ

lemma extensionPairs_sub_incident {H : TripleSystem V} {E A Q : Finset V} {x : V}
    (hA : A ∈ supports H) (hx : x ∉ A) (hQA : Q ⊆ A) (hQ : Q.card = 2)
    (hE : E ∈ H) (hEq : E = insert x Q) : extensionPairs H x A Q ⊆ incidentPairs H E := by
  classical
  intro S hS
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨hyAQ,hyH⟩ := Finset.mem_filter.mp hy
  obtain ⟨hyA,hyQ⟩ := Finset.mem_sdiff.mp hyAQ
  have hxQ : x ∉ Q := fun hxQ => hx (hQA hxQ)
  have hC : CommonPair H x y Q := ⟨hQ,hxQ,hyQ,by simpa only [hEq] using hE,hyH⟩
  have hW : SecondaryWitness H x y Q A := ⟨hA,hx,hyA,hQA,hC⟩
  exact Finset.mem_filter.mpr ⟨hW.pair_secondary,x,y,rfl,Q,A,hW,hEq⟩

lemma secondary_decomposition {H : TripleSystem V} (hH : Uniform H)
    {E : Finset V} (hE : E ∈ secondaryTriples H) :
    ∃ x Q A, A ∈ supports H ∧ x ∉ A ∧ Q ⊆ A ∧ Q.card = 2 ∧ E ∈ H ∧ E = insert x Q := by
  obtain ⟨hEH,A,hA,hEA⟩ := mem_secondaryTriples.mp hE
  have hDiff : (E \ A).card = 1 := by
    have he := Finset.card_sdiff_add_card_inter E A
    have hEc := hH E hEH
    omega
  obtain ⟨x,hxEq⟩ := Finset.card_eq_one.mp hDiff
  have hx : x ∈ E ∧ x ∉ A := Finset.mem_sdiff.mp (by rw [hxEq]; simp)
  refine ⟨x,E ∩ A,A,hA,hx.2,Finset.inter_subset_right,hEA,hEH,?_⟩
  calc
    E = (E \ A) ∪ (E ∩ A) := by ext z; simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]; tauto
    _ = _ := by rw [hxEq]; simp only [Finset.singleton_union]

lemma incidentPairs_card_ge_two {H : TripleSystem V} (hH : Uniform H)
    {E : Finset V} (hE : E ∈ secondaryTriples H) : 2 ≤ (incidentPairs H E).card := by
  obtain ⟨x,Q,A,hA,hx,hQA,hQ,hEH,hEq⟩ := secondary_decomposition hH hE
  exact (extensionPairs_card_ge_two (x:=x) (mem_supports.mp hA) hQA hQ).trans
    (Finset.card_le_card (extensionPairs_sub_incident hA hx hQA hQ hEH hEq))

lemma thin_support_common_vertex_unique {H : TripleSystem V} (havoid : LiteralAvoids H)
    {A B : Finset V} (hA : A ∈ supports H) (hB : B ∈ supports H) (hAB : A ≠ B)
    {u v : V} (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∈ A) (hvB : v ∈ B) : u = v := by
  by_contra huv
  have hsub : ({u,v} : Finset V) ⊆ A ∩ B := by
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.mem_inter]
    exact ⟨⟨huA,huB⟩,⟨hvA,hvB⟩⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair huv] at hc
  have ht := supports_thin havoid A hA B hB hAB
  omega

/-- The four-neighbor clause in PV11's degree comparison, retaining both
 actual exceptional supports and all four distinct charged pairs. -/
lemma incidentPairs_card_ge_four {H : TripleSystem V} (havoid : LiteralAvoids H)
    {E A B Q R : Finset V} {x y : V} (hW : SecondaryWitness H x y Q A)
    (hV : SecondaryWitness H y x R B) (hE : E = insert x Q) :
    4 ≤ (incidentPairs H E).card := by
  classical
  have hxy : x ≠ y := by intro he; exact hW.2.1 (he.symm ▸ hW.2.2.1)
  have hi := PrivatePairs.commonPairs_intersect havoid hxy hW.2.2.2.2 (commonPair_symm hV.2.2.2.2)
  obtain ⟨u,huQ,huR⟩ := Finset.not_disjoint_iff.mp hi
  obtain ⟨v,hvu,hQeq⟩ := pair_eq_with_member hW.2.2.2.2.1 huQ
  have huA : u ∈ A := hW.2.2.2.1 huQ
  have huB : u ∈ B := hV.2.2.2.1 huR
  have hvQ : v ∈ Q := by rw [hQeq]; simp
  have hvA : v ∈ A := hW.2.2.2.1 hvQ
  have hAB : A ≠ B := by intro he; exact hW.2.1 (he.symm ▸ hV.2.2.1)
  have hvB : v ∉ B := by
    intro hvB
    exact hvu (thin_support_common_vertex_unique havoid hW.1 hV.1 hAB huA huB hvA hvB).symm
  have hxu : x ≠ u := by intro he; exact hW.2.1 (he.symm ▸ huA)
  have hxv : x ≠ v := by intro he; exact hW.2.1 (he.symm ▸ hvA)
  let Q' : Finset V := {u,x}
  have hQ'B : Q' ⊆ B := by
    simp only [Q',Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨huB,hV.2.2.1⟩
  have hQ' : Q'.card = 2 := by simp [Q',Ne.symm hxu]
  have hE' : E = insert v Q' := by
    rw [hE,hQeq]
    simp only [Q',Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,Finset.union_assoc]
  have hEH : E ∈ H := by rw [hE]; exact hW.2.2.2.2.2.2.2.1
  have hsub0 := extensionPairs_sub_incident hW.1 hW.2.1 hW.2.2.2.1 hW.2.2.2.2.1 hEH hE
  have hsub1 := extensionPairs_sub_incident hV.1 hvB hQ'B hQ' hEH hE'
  have hd : Disjoint (extensionPairs H x A Q) (extensionPairs H v B Q') := by
    apply Finset.disjoint_left.mpr
    intro S h0 h1
    obtain ⟨z,hz,he0⟩ := Finset.mem_image.mp h0
    obtain ⟨z',hz',he1⟩ := Finset.mem_image.mp h1
    have hv : v ∈ ({x,z} : Finset V) := by rw [he0,←he1]; simp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · exact hxv hv.symm
    · have hzQ : z ∉ Q := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).2
      exact hzQ (hv ▸ hvQ)
  have h0 := extensionPairs_card_ge_two (x:=x) (mem_supports.mp hW.1) hW.2.2.2.1 hW.2.2.2.2.1
  have h1 := extensionPairs_card_ge_two (x:=v) (mem_supports.mp hV.1) hQ'B hQ'
  have hc := Finset.card_le_card (Finset.union_subset hsub0 hsub1)
  rw [Finset.card_union_of_disjoint hd] at hc
  omega

/-- Full source incidence degree comparison. The two and four neighbor cases
 are proved from actual secondary witnesses, not assumed as a supplier. -/
theorem incidence_degree_comparison {H : TripleSystem V} (hH : Uniform H)
    (havoid : LiteralAvoids H) {E S : Finset V} (hE : E ∈ secondaryTriples H)
    (hI : Incidence H E S) : (incidentTriples H S).card ≤ (incidentPairs H E).card := by
  obtain ⟨x,y,rfl,Q,A,hW,hEq⟩ := hI
  have hxy : x ≠ y := by intro he; exact hW.2.1 (he.symm ▸ hW.2.2.1)
  by_cases hrev : ∃ R B, SecondaryWitness H y x R B
  · obtain ⟨R,B,hV⟩ := hrev
    exact (incidentTriples_card_le_four havoid hxy).trans (incidentPairs_card_ge_four havoid hW hV hEq)
  · exact (incidentTriples_card_le_two havoid hxy hrev).trans (incidentPairs_card_ge_two hH hE)
lemma subtype_filtered_card {X : Type*} [DecidableEq X] (s : Finset X)
    (p : X → Prop) [DecidablePred p] :
    ((Finset.univ : Finset s).filter (fun x : s => p x)).card = (s.filter p).card := by
  have hu : (Finset.univ : Finset s) = s.attach := by ext; simp
  rw [hu,Finset.filter_attach,Finset.card_map,Finset.card_attach]

lemma degree_charge_finite {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (s : Finset X) (t : Finset Y) (R : X → Y → Prop) [DecidableRel R]
    (hpos : ∀ x ∈ s, ∃ y ∈ t, R x y)
    (hdeg : ∀ x ∈ s, ∀ y ∈ t, R x y →
      (s.filter (fun z => R z y)).card ≤ (t.filter (fun z => R x z)).card) :
    s.card ≤ t.card := by
  classical
  have h := Erdos643.DegreeCharge.card_le_card_of_degree (fun (x : s) (y : t) => R x y)
    (by
      intro x
      obtain ⟨y,hy,hxy⟩ := hpos x x.property
      exact ⟨⟨y,hy⟩,hxy⟩)
    (by
      intro x y hxy
      have hr : (Erdos643.DegreeCharge.rightNeighbors (fun (x : s) (y : t) => R x y) y).card =
          (s.filter (fun z => R z (y : Y))).card := by
        calc
          _ = ((Finset.univ : Finset s).filter (fun z : s => R z (y : Y))).card := by
            congr 1
            ext z
            simp [Erdos643.DegreeCharge.rightNeighbors]
          _ = _ := subtype_filtered_card s (fun z => R z (y : Y))
      have hl : (Erdos643.DegreeCharge.leftNeighbors (fun (x : s) (y : t) => R x y) x).card =
          (t.filter (fun z => R (x : X) z)).card := by
        calc
          _ = ((Finset.univ : Finset t).filter (fun z : t => R (x : X) z)).card := by
            congr 1
            ext z
            simp [Erdos643.DegreeCharge.leftNeighbors]
          _ = _ := subtype_filtered_card t (fun z => R (x : X) z)
      rw [hr,hl]
      exact hdeg x x.property y y.property hxy)
  simpa using h

/-- Actual secondary triples are paid for by actual secondary charged pairs.
 All positivity and degree hypotheses of the weighted finite-set theorem are
 supplied by the preceding structural incidence lemmas. -/
theorem secondaryTriples_card_le_secondaryPairs {H : TripleSystem V}
    (hH : Uniform H) (havoid : LiteralAvoids H) :
    (secondaryTriples H).card ≤ (secondaryPairs H).card := by
  classical
  apply degree_charge_finite (secondaryTriples H) (secondaryPairs H) (Incidence H)
  · intro E hE
    have hc := incidentPairs_card_ge_two hH hE
    obtain ⟨S,hS⟩ := Finset.card_pos.mp (show 0 < (incidentPairs H E).card by omega)
    obtain ⟨hSP,hI⟩ := Finset.mem_filter.mp hS
    exact ⟨S,hSP,hI⟩
  · intro E hE S hS hI
    exact incidence_degree_comparison hH havoid hE hI

noncomputable def chargedPairs (H : TripleSystem V) : Finset (Finset V) :=
  mainPairs H ∪ secondaryPairs H

lemma chargedPairs_disjoint_Bpairs {H : TripleSystem V} (havoid : LiteralAvoids H) :
    Disjoint (chargedPairs H) (Bpairs (H \ removed H)) := by
  apply Finset.disjoint_left.mpr
  intro S hS hB
  rcases Finset.mem_union.mp hS with hS | hS
  · exact Finset.disjoint_left.mp (mainPairs_disjoint_Bpairs havoid) hS hB
  · exact Finset.disjoint_left.mp (secondaryPairs_disjoint_Bpairs havoid) hS hB

lemma chargedPairs_subset_unordered_pairs (H : TripleSystem V) :
    chargedPairs H ⊆ (Finset.univ.powersetCard 2 : Finset (Finset V)) := by
  intro S hS
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.subset_univ _,?_⟩
  rcases Finset.mem_union.mp hS with hS | hS
  · obtain ⟨A,hA,hSA,hSc⟩ := mem_mainPairs.mp hS
    exact hSc
  · exact (mem_Bpairs.mp (mem_secondaryPairs.mp hS).1).1

lemma removed_card_le_chargedPairs {H : TripleSystem V} (hH : Uniform H) (havoid : LiteralAvoids H) :
    (removed H).card ≤ (chargedPairs H).card := by
  have ht := supports_thin havoid
  change (removed H).card ≤ (mainPairs H ∪ secondaryPairs H).card
  rw [Finset.card_union_of_disjoint (mainPairs_disjoint_secondaryPairs havoid ht)]
  rw [removed_eq_main_union_secondary hH]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add (mainTriples_card_le_mainPairs hH ht) (secondaryTriples_card_le_secondaryPairs hH havoid))

/-- Published PV2009 Lemma11 with all structural, support and weighted
 incidence suppliers proved, and the exact original unordered pair universe. -/
theorem pv2009_lemma11 (H : TripleSystem V) (hH : Uniform H) (havoid : LiteralAvoids H) :
    ∃ R : TripleSystem V, R ⊆ H ∧ ¬ HasK5Minus (H \ R) ∧
      (Bpairs (H \ R)).card + R.card ≤ (Fintype.card V).choose 2 := by
  classical
  refine ⟨removed H,removed_subset H,removed_cleans H,?_⟩
  have hBsub : Bpairs (H \ removed H) ⊆ (Finset.univ.powersetCard 2 : Finset (Finset V)) := by
    intro S hS
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,(mem_Bpairs.mp hS).1⟩
  have hsub := Finset.union_subset hBsub (chargedPairs_subset_unordered_pairs H)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (chargedPairs_disjoint_Bpairs havoid).symm] at hc
  simp only [Finset.card_powersetCard,Finset.card_univ] at hc
  exact (Nat.add_le_add_left (removed_card_le_chargedPairs hH havoid) _).trans hc

end K5Cleaning
end Erdos643
