import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic

/-!
Literal finite triple systems and the exact repeated-disjoint-union target.
This module is part of the full dependency development; it is not an extremal bound.
-/
namespace Erdos643
namespace HypergraphBasics

open Finset

variable {V : Type*} [DecidableEq V]

abbrev TripleSystem (V : Type*) := Finset (Finset V)

def Uniform (H : TripleSystem V) : Prop := ∀ e ∈ H, e.card = 3

def FourDistinct (A B C D : Finset V) : Prop :=
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D

def Forbidden (H : TripleSystem V) : Prop :=
  ∃ A ∈ H, ∃ B ∈ H, ∃ C ∈ H, ∃ D ∈ H,
    FourDistinct A B C D ∧ Disjoint A B ∧ Disjoint C D ∧ A ∪ B = C ∪ D

def LiteralAvoids (H : TripleSystem V) : Prop :=
  ∀ A ∈ H, ∀ B ∈ H, ∀ C ∈ H, ∀ D ∈ H,
    Disjoint A B → Disjoint C D → A ∪ B = C ∪ D →
    ({A, B} : Finset (Finset V)) = {C, D}

lemma disjoint_union_cancel {A B D : Finset V}
    (hAB : Disjoint A B) (hAD : Disjoint A D) (hu : A ∪ B = A ∪ D) : B = D := by
  ext x
  constructor
  · intro hx
    have hxA : x ∉ A := fun hxA => (disjoint_left.mp hAB) hxA hx
    have hxU : x ∈ A ∪ D := by rw [← hu]; exact mem_union_right A hx
    exact (mem_union.mp hxU).resolve_left hxA
  · intro hx
    have hxA : x ∉ A := fun hxA => (disjoint_left.mp hAD) hxA hx
    have hxU : x ∈ A ∪ B := by rw [hu]; exact mem_union_right A hx
    exact (mem_union.mp hxU).resolve_left hxA

lemma uniform_nonempty {H : TripleSystem V} (hH : Uniform H)
    {e : Finset V} (he : e ∈ H) : e.Nonempty := by
  exact card_pos.mp (by rw [hH e he]; decide)

lemma disjoint_ne_of_uniform {H : TripleSystem V} (hH : Uniform H)
    {A B : Finset V} (hA : A ∈ H) (hd : Disjoint A B) : A ≠ B := by
  intro he
  subst B
  have hzero : A = ∅ := disjoint_self.mp hd
  have hcard := hH A hA
  simp [hzero] at hcard

/-- Uniform triple systems' literal avoidance is exactly the four-distinct-edge prohibition. -/
theorem literalAvoids_iff_not_forbidden {H : TripleSystem V} (hH : Uniform H) :
    LiteralAvoids H ↔ ¬ Forbidden H := by
  constructor
  · intro havoid
    rintro ⟨A, hA, B, hB, C, hC, D, hD, hdist, hAB, hCD, hu⟩
    have hp := havoid A hA B hB C hC D hD hAB hCD hu
    have hm : A ∈ ({C, D} : Finset (Finset V)) := by rw [← hp]; simp
    simp only [mem_insert, mem_singleton] at hm
    exact hm.elim hdist.2.1 hdist.2.2.1
  · intro havoid A hA B hB C hC D hD hAB hCD hu
    by_cases hac : A = C
    · subst C
      have hbd := disjoint_union_cancel hAB hCD hu
      simp [hbd]
    by_cases had : A = D
    · subst D
      have hbc := disjoint_union_cancel hAB hCD.symm (by simpa [union_comm] using hu)
      simp [hbc, pair_comm]
    have hab := disjoint_ne_of_uniform hH hA hAB
    have hcd := disjoint_ne_of_uniform hH hC hCD
    have hbc : B ≠ C := by
      intro he
      subst C
      have had' : A = D := disjoint_union_cancel hAB.symm hCD
        (by simpa [union_comm] using hu)
      exact had had'
    have hbd : B ≠ D := by
      intro he
      subst D
      have hac' : A = C := disjoint_union_cancel hAB.symm hCD.symm
        (by simpa [union_comm] using hu)
      exact hac hac'
    exact False.elim (havoid ⟨A, hA, B, hB, C, hC, D, hD,
      ⟨hab, hac, had, hbc, hbd, hcd⟩, hAB, hCD, hu⟩)

/-- A common-link edge is an actual pair outside BOTH centers. -/
def CommonPair (H : TripleSystem V) (x y : V) (P : Finset V) : Prop :=
  P.card = 2 ∧ x ∉ P ∧ y ∉ P ∧ insert x P ∈ H ∧ insert y P ∈ H

def CommonMatching (H : TripleSystem V) : Prop :=
  ∃ x y, x ≠ y ∧ ∃ P Q, CommonPair H x y P ∧ CommonPair H x y Q ∧ Disjoint P Q

lemma matching_disjoint {x y : V} {P Q : Finset V}
    (hxy : x ≠ y) (hxP : x ∉ P) (hxQ : x ∉ Q)
    (hyP : y ∉ P) (hyQ : y ∉ Q) (hPQ : Disjoint P Q) :
    Disjoint (insert x P) (insert y Q) := by
  apply disjoint_left.mpr
  intro z hzA hzB
  simp only [mem_insert] at hzA hzB
  rcases hzA with hzx | hzP
  · subst z
    exact hzB.elim hxy hxQ
  · rcases hzB with hzy | hzQ
    · subst z
      exact hyP hzP
    · exact (disjoint_left.mp hPQ) hzP hzQ

/-- Every common-link matching has the original full six-vertex support. -/
theorem matching_support_card {H : TripleSystem V} {x y : V} {P Q : Finset V}
    (hxy : x ≠ y) (hP : CommonPair H x y P) (hQ : CommonPair H x y Q)
    (hPQ : Disjoint P Q) : ((insert x P) ∪ (insert y Q)).card = 6 := by
  rw [card_union_of_disjoint (matching_disjoint hxy hP.2.1 hQ.2.1 hP.2.2.1 hQ.2.2.1 hPQ)]
  simp [card_insert_of_notMem hP.2.1, card_insert_of_notMem hQ.2.2.1, hP.1, hQ.1]

/-- An auxiliary matching would contradict literal avoidance, using actual edges. -/
theorem literalAvoids_not_commonMatching {H : TripleSystem V} (havoid : LiteralAvoids H) :
    ¬ CommonMatching H := by
  rintro ⟨x, y, hxy, P, Q, hP, hQ, hPQ⟩
  have hAB := matching_disjoint hxy hP.2.1 hQ.2.1 hP.2.2.1 hQ.2.2.1 hPQ
  have hCD := matching_disjoint hxy hQ.2.1 hP.2.1 hQ.2.2.1 hP.2.2.1 hPQ.symm
  have hu : insert x P ∪ insert y Q = insert x Q ∪ insert y P := by
    ext z
    simp only [mem_union, mem_insert]
    tauto
  have hp := havoid (insert x P) hP.2.2.2.1 (insert y Q) hQ.2.2.2.2
    (insert x Q) hQ.2.2.2.1 (insert y P) hP.2.2.2.2 hAB hCD hu
  have hm : insert x P ∈ ({insert x Q, insert y P} : Finset (Finset V)) := by
    rw [← hp]; simp
  simp only [mem_insert, mem_singleton] at hm
  rcases hm with he | he
  · have hPQeq : P = Q := by
      ext z
      have hz := congrArg (fun s : Finset V => z ∈ s) he
      simp only [mem_insert] at hz
      by_cases hzx : z = x
      · subst z
        simp [hP.2.1, hQ.2.1]
      · simpa [hzx] using hz
    have hself : Disjoint P P := by simpa [← hPQeq] using hPQ
    have hzero : P = ∅ := disjoint_self.mp hself
    have hcard := hP.1
    simp [hzero] at hcard
  · have hx : x ∈ insert y P := by rw [← he]; simp
    simp only [mem_insert] at hx
    exact hx.elim hxy hP.2.1

/-- Disjoint triples have the literal six-vertex union, including every vertex. -/
theorem disjoint_triples_support_card {H : TripleSystem V} (hH : Uniform H)
    {A B : Finset V} (hA : A ∈ H) (hB : B ∈ H) (hd : Disjoint A B) :
    (A ∪ B).card = 6 := by
  rw [card_union_of_disjoint hd, hH A hA, hH B hB]

/-- The auxiliary witness entails four distinct original hyperedges. -/
theorem commonMatching_forbidden {H : TripleSystem V} (hH : Uniform H)
    (hm : CommonMatching H) : Forbidden H := by
  by_contra hf
  exact literalAvoids_not_commonMatching ((literalAvoids_iff_not_forbidden hH).mpr hf) hm

/-- A pair not contained in a triple misses at least two points of the triple. -/
lemma pair_outside_triple_disjoint_pair {T Q : Finset V}
    (hT : T.card = 3) (hQ : Q.card = 2) (hnot : ¬ Q ⊆ T) :
    ∃ S ⊆ T, S.card = 2 ∧ Disjoint S Q := by
  have hn : (Q \ T).Nonempty := sdiff_nonempty.mpr hnot
  have hp := card_pos.mpr hn
  have hqeq := card_sdiff_add_card_inter Q T
  have hteq := card_sdiff_add_card_inter T Q
  have hi : (T ∩ Q).card = (Q ∩ T).card := by rw [inter_comm]
  have htwo : 2 ≤ (T \ Q).card := by omega
  obtain ⟨S, hS, hSc⟩ := exists_subset_card_eq htwo
  refine ⟨S, hS.trans sdiff_subset, hSc, ?_⟩
  apply disjoint_left.mpr
  intro x hxS hxQ
  exact (mem_sdiff.mp (hS hxS)).2 hxQ

/-- PV Lemma 6's triangle rigidity, stated without a circular Pi dependency. -/
theorem common_triangle_rigidity {H : TripleSystem V} (havoid : LiteralAvoids H)
    {a b : V} (hab : a ≠ b) {T : Finset V} (hT : T.card = 3)
    (hfaces : ∀ S, S ⊆ T → S.card = 2 → CommonPair H a b S)
    {Q : Finset V} (hQ : CommonPair H a b Q) : Q ⊆ T := by
  by_contra hnot
  obtain ⟨S, hST, hSc, hSQ⟩ := pair_outside_triple_disjoint_pair hT hQ.1 hnot
  exact literalAvoids_not_commonMatching havoid
    ⟨a, b, hab, S, Q, hfaces S hST hSc, hQ, hSQ⟩

end HypergraphBasics
end Erdos643
