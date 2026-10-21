import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
import Mathlib.Tactic

/-! The K5-filled construction, conditional on a supplied genuine upstream block design. -/
namespace Erdos643Design
open Finset
variable {V : Type*} [DecidableEq V]

def triples (B : Finset (Finset V)) : Finset (Finset V) :=
  B.biUnion (fun b => b.powersetCard 3)

omit [DecidableEq V] in
lemma block_eq (B : Finset (Finset V)) (hB : B.IsBlockDesign 2 5)
    {b c S : Finset V} (hb : b ∈ B) (hc : c ∈ B)
    (hS : S.card = 2) (hsb : S ⊆ b) (hsc : S ⊆ c) : b = c := by
  obtain ⟨d, hd, hu⟩ := hB.2 S hS
  exact (hu b ⟨hb, hsb⟩).trans (hu c ⟨hc, hsc⟩).symm

lemma inter_card_le_one (B : Finset (Finset V)) (hB : B.IsBlockDesign 2 5)
    {b c : Finset V} (hb : b ∈ B) (hc : c ∈ B) (hbc : b ≠ c) :
    (b ∩ c).card ≤ 1 := by
  by_contra hn
  obtain ⟨S, hs, hcard⟩ := exists_subset_card_eq (s := b ∩ c) (n := 2) (by omega)
  exact hbc (block_eq B hB hb hc hcard (hs.trans inter_subset_left)
    (hs.trans inter_subset_right))

lemma powersets_disjoint (B : Finset (Finset V)) (hB : B.IsBlockDesign 2 5)
    (k : ℕ) (hk : 2 ≤ k) :
    (B : Set (Finset V)).PairwiseDisjoint (fun b => b.powersetCard k) := by
  intro b hb c hc hbc
  apply disjoint_left.mpr
  intro S hs ht
  obtain ⟨hsb, hsk⟩ := mem_powersetCard.mp hs
  obtain ⟨hsc, _⟩ := mem_powersetCard.mp ht
  have hm : S ⊆ b ∩ c := subset_inter hsb hsc
  have hh := card_le_card hm
  have hi := inter_card_le_one B hB hb hc hbc
  omega

lemma uniform (B : Finset (Finset V)) : (triples B).IsUniform 3 := by
  intro e he
  obtain ⟨b, hb, he⟩ := mem_biUnion.mp he
  exact (mem_powersetCard.mp he).2

lemma pairs_cover [Fintype V] (B : Finset (Finset V)) (hB : B.IsBlockDesign 2 5) :
    B.biUnion (fun b => b.powersetCard 2) = (univ : Finset V).powersetCard 2 := by
  ext S
  simp only [mem_biUnion, mem_powersetCard, subset_univ, true_and]
  constructor
  · rintro ⟨b, hb, hs, hc⟩; exact hc
  · intro hS
    obtain ⟨b, hb, _⟩ := hB.2 S hS
    exact ⟨b, hb.1, hb.2, hS⟩

theorem card_triples [Fintype V] (B : Finset (Finset V))
    (hB : B.IsBlockDesign 2 5) : (triples B).card = (Fintype.card V).choose 2 := by
  have h3 := card_biUnion (powersets_disjoint B hB 3 (by omega))
  have h2 := card_biUnion (powersets_disjoint B hB 2 (by omega))
  have heq : ∑ b ∈ B, (b.powersetCard 3).card = ∑ b ∈ B, (b.powersetCard 2).card := by
    apply sum_congr rfl
    intro b hb
    rw [card_powersetCard, card_powersetCard, hB.1 b hb]
    decide
  calc
    (triples B).card = ∑ b ∈ B, (b.powersetCard 3).card := h3
    _ = ∑ b ∈ B, (b.powersetCard 2).card := heq
    _ = (B.biUnion (fun b => b.powersetCard 2)).card := h2.symm
    _ = (Fintype.card V).choose 2 := by rw [pairs_cover B hB, card_powersetCard, card_univ]

lemma inter_partition {a c d : Finset V} (ha : a ⊆ c ∪ d) (hcd : Disjoint c d) :
    a.card = (a ∩ c).card + (a ∩ d).card := by
  have hh : a = (a ∩ c) ∪ (a ∩ d) := by
    rw [← inter_union_distrib_left]
    exact (inter_eq_left.mpr ha).symm
  calc
    a.card = ((a ∩ c) ∪ (a ∩ d)).card := congrArg Finset.card hh
    _ = _ := card_union_of_disjoint (hcd.mono inter_subset_right inter_subset_right)

lemma blocks_of_large_inter (B : Finset (Finset V)) (hB : B.IsBlockDesign 2 5)
    {a c b d : Finset V} (hb : b ∈ B) (hd : d ∈ B)
    (hab : a ⊆ b) (hcd : c ⊆ d) (hac : 2 ≤ (a ∩ c).card) : b = d := by
  by_contra hne
  have hh : a ∩ c ⊆ b ∩ d := inter_subset_inter hab hcd
  have := card_le_card hh
  have := inter_card_le_one B hB hb hd hne
  omega

lemma impossible_with_large_inter (B : Finset (Finset V)) (hB : B.IsBlockDesign 2 5)
    {a b c d : Finset V} (ha : a ∈ triples B) (hb : b ∈ triples B)
    (hc : c ∈ triples B) (hd : d ∈ triples B)
    (hab : Disjoint a b) (hcd : Disjoint c d) (hu : a ∪ b = c ∪ d)
    (hne : a ≠ c) (hlarge : 2 ≤ (a ∩ c).card) : False := by
  have ha3 := uniform B a ha
  have hb3 := uniform B b hb
  have hc3 := uniform B c hc
  have hd3 := uniform B d hd
  obtain ⟨ba, hba, ha'⟩ := mem_biUnion.mp ha
  obtain ⟨has, _⟩ := mem_powersetCard.mp ha' 
  obtain ⟨bb, hbb, hb'⟩ := mem_biUnion.mp hb
  obtain ⟨hbs, _⟩ := mem_powersetCard.mp hb' 
  obtain ⟨bc, hbc, hc'⟩ := mem_biUnion.mp hc
  obtain ⟨hcs, _⟩ := mem_powersetCard.mp hc' 
  obtain ⟨bd, hbd, hd'⟩ := mem_biUnion.mp hd
  obtain ⟨hds, _⟩ := mem_powersetCard.mp hd' 
  have heqac := blocks_of_large_inter B hB hba hbc has hcs hlarge
  have hpartc := inter_partition (a := c) (c := a) (d := b)
    (by rw [hu]; exact subset_union_left) hab
  have hpartb := inter_partition (a := b) (c := c) (d := d)
    (by rw [← hu]; exact subset_union_right) hcd
  have hlarge' : 2 ≤ (b ∩ d).card := by
    rw [inter_comm c a] at hpartc
    rw [inter_comm c b] at hpartc
    omega
  have heqbd := blocks_of_large_inter B hB hbb hbd hbs hds hlarge'
  subst bc
  subst bd
  by_cases hbab : ba = bb
  · have hsub : a ∪ b ⊆ ba := union_subset has (hbab ▸ hbs)
    have hcard := card_le_card hsub
    rw [card_union_of_disjoint hab, ha3, hb3, hB.1 ba hba] at hcard
    omega
  · have hi := inter_card_le_one B hB hba hbb hbab
    have hna : ¬ a ⊆ c := by
      intro hs
      exact hne (eq_of_subset_of_card_le hs (by omega))
    have hnc : ¬ c ⊆ a := by
      intro hs
      exact hne (eq_of_subset_of_card_le hs (by omega)).symm
    obtain ⟨x, hxa, hxc⟩ := not_subset.mp hna
    obtain ⟨y, hyc, hya⟩ := not_subset.mp hnc
    have hxd : x ∈ d := by
      have hx : x ∈ c ∪ d := by rw [← hu]; exact mem_union_left _ hxa
      exact (mem_union.mp hx).resolve_left hxc
    have hyb : y ∈ b := by
      have hy : y ∈ a ∪ b := by rw [hu]; exact mem_union_left _ hyc
      exact (mem_union.mp hy).resolve_left hya
    have hxy := card_le_one.mp hi x (mem_inter.mpr ⟨has hxa, hds hxd⟩)
      y (mem_inter.mpr ⟨hcs hyc, hbs hyb⟩)
    exact hya (hxy ▸ hxa)

theorem avoids (B : Finset (Finset V)) (hB : B.IsBlockDesign 2 5) :
    ¬ (triples B).HasRepeatedDisjointUnion := by
  rintro ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, hu, _, _, hnac, hnad, _, _⟩
  by_cases hlarge : 2 ≤ (a ∩ c).card
  · exact impossible_with_large_inter B hB ha hb hc hd hab hcd hu hnac hlarge
  · have hpart := inter_partition (a := a) (c := c) (d := d)
      (by rw [← hu]; exact subset_union_left) hcd
    have ha3 := uniform B a ha
    have hlarge' : 2 ≤ (a ∩ d).card := by omega
    exact impossible_with_large_inter B hB ha hb hd hc hab hcd.symm
      (hu.trans (union_comm c d)) hnad hlarge'

/-- Construction witness in the genuine upstream predicates, with no existence assertion. -/
theorem supplied_design_construction [Fintype V] (B : Finset (Finset V))
    (hB : B.IsBlockDesign 2 5) :
    ∃ H : Finset (Finset V), H.IsUniform 3 ∧ ¬ H.HasRepeatedDisjointUnion ∧
      H.card = (Fintype.card V).choose 2 :=
  ⟨triples B, uniform B, avoids B hB, card_triples B hB⟩

/-- A supplied design yields the matching lower bound for the actual upstream extremal number. -/
theorem design_lower_bound (n : ℕ) (B : Finset (Finset (Fin n)))
    (hB : B.IsBlockDesign 2 5) :
    n.choose 2 ≤ Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) := by
  classical
  have hcard : (triples B).card = n.choose 2 := by
    simpa only [Fintype.card_fin] using card_triples B hB
  unfold Hypergraph.extremalNumber
  rw [← hcard]
  apply Finset.le_sup (f := Finset.card)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, avoids B hB⟩
  intro e he
  exact mem_powersetCard.mpr ⟨subset_univ e, uniform B e he⟩

/-- Equality requires the independent upper bound and an actually supplied design. -/
theorem extremal_eq_of_design (n : ℕ) (B : Finset (Finset (Fin n)))
    (hB : B.IsBlockDesign 2 5)
    (hupper : Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) ≤
      n.choose 2) :
    Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) = n.choose 2 :=
  Nat.le_antisymm hupper (design_lower_bound n B hB)

end Erdos643Design
