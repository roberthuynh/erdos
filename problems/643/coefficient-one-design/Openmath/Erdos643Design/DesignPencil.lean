import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
import Mathlib.Tactic

/-! The partition obtained by deleting a point from its incident design blocks.
Every structural fact is derived from the actual upstream design predicate. -/
set_option autoImplicit false

namespace Erdos643Design.DesignPencil
open Finset
variable {V : Type*} [DecidableEq V]

def pencil (D : Finset (Finset V)) (p : V) : Finset (Finset V) :=
  D.filter (fun b => p ∈ b)

def groups (D : Finset (Finset V)) (p : V) : Finset (Finset V) :=
  (pencil D p).image (fun b => b.erase p)

theorem group_card (D : Finset (Finset V)) (hD : D.IsBlockDesign 2 5) (p : V)
    {g : Finset V} (hg : g ∈ groups D p) : g.card = 4 := by
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hg
  obtain ⟨hbD, hpb⟩ := mem_filter.mp hb
  rw [card_erase_of_mem hpb, hD.1 b hbD]

theorem point_not_mem_group (D : Finset (Finset V)) (p : V)
    {g : Finset V} (hg : g ∈ groups D p) : p ∉ g := by
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hg
  exact notMem_erase p b

/-- Every vertex other than the deleted point lies in exactly one pencil group. -/
theorem unique_group (D : Finset (Finset V)) (hD : D.IsBlockDesign 2 5)
    (p v : V) (hvp : v ≠ p) :
    ∃! g, g ∈ groups D p ∧ v ∈ g := by
  have hpv : p ≠ v := hvp.symm
  obtain ⟨b, hb, hbu⟩ := hD.2 {p,v} (by simp [hpv])
  have hpb : p ∈ b := hb.2 (by simp)
  have hvb : v ∈ b := hb.2 (by simp)
  refine ⟨b.erase p, ⟨mem_image.mpr ⟨b, mem_filter.mpr ⟨hb.1,hpb⟩, rfl⟩,
    mem_erase.mpr ⟨hvp,hvb⟩⟩, ?_⟩
  intro g hg
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hg.1
  obtain ⟨hcD, hpc⟩ := mem_filter.mp hc
  have hvc : v ∈ c := (mem_erase.mp hg.2).2
  have hcb : c = b := hbu c ⟨hcD, by
    simpa only [insert_subset_iff, singleton_subset_iff] using And.intro hpc hvc⟩
  exact congrArg (fun a => a.erase p) hcb

/-- Distinct groups are disjoint, without assuming any partition data. -/
theorem groups_pairwise_disjoint (D : Finset (Finset V)) (hD : D.IsBlockDesign 2 5)
    (p : V) : (groups D p : Set (Finset V)).PairwiseDisjoint id := by
  intro g hg h hh hne
  apply disjoint_left.mpr
  intro v hvg hvh
  have hvp : v ≠ p := by
    intro heq
    exact point_not_mem_group D p hg (heq ▸ hvg)
  obtain ⟨a, ha, hau⟩ := unique_group D hD p v hvp
  exact hne ((hau g ⟨hg,hvg⟩).trans (hau h ⟨hh,hvh⟩).symm)

theorem groups_union [Fintype V] (D : Finset (Finset V)) (hD : D.IsBlockDesign 2 5)
    (p : V) : (groups D p).biUnion id = (univ : Finset V).erase p := by
  ext v
  constructor
  · intro hv
    obtain ⟨g, hg, hvg⟩ := mem_biUnion.mp hv
    apply mem_erase.mpr
    refine ⟨?_, mem_univ v⟩
    intro heq
    exact point_not_mem_group D p hg (heq ▸ hvg)
  · intro hv
    obtain ⟨g, hg, _⟩ := unique_group D hD p v (mem_erase.mp hv).1
    exact mem_biUnion.mpr ⟨g,hg.1,hg.2⟩

/-- Four vertices in each group account for every vertex except the deleted point. -/
theorem groups_card_mul_four [Fintype V] (D : Finset (Finset V))
    (hD : D.IsBlockDesign 2 5) (p : V) :
    (groups D p).card * 4 = Fintype.card V - 1 := by
  have hsum : ∑ g ∈ groups D p, g.card = (groups D p).card * 4 := by
    calc
      _ = ∑ _g ∈ groups D p, 4 := by
        apply sum_congr rfl
        intro g hg
        exact group_card D hD p hg
      _ = _ := by simp
  calc
    (groups D p).card * 4 = ∑ g ∈ groups D p, g.card := hsum.symm
    _ = ((groups D p).biUnion id).card :=
      (card_biUnion (groups_pairwise_disjoint D hD p)).symm
    _ = ((univ : Finset V).erase p).card := congrArg Finset.card (groups_union D hD p)
    _ = Fintype.card V - 1 := by rw [card_erase_of_mem (mem_univ p), card_univ]

theorem groups_card_of_card [Fintype V] (D : Finset (Finset V))
    (hD : D.IsBlockDesign 2 5) (p : V) (m : ℕ)
    (hcard : Fintype.card V = 4 * m + 1) : (groups D p).card = m := by
  have hm := groups_card_mul_four D hD p
  rw [hcard] at hm
  omega

end Erdos643Design.DesignPencil
