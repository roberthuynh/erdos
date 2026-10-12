import R691.Main
import H3Unequal.Main

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.Omit1UnitCutAdapterR707
open QB4 B5 Omit1PrefixR691
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {q : ℕ}
variable {A B : Finset V} {a b : V}

/-- Literal original unit-cut inequalities for one actual original omission pair. -/
def UnitCuts (q : ℕ) (G : SimpleGraph V) (A B : Finset V) (a b : V) : Prop :=
  ∀ S : Finset V, (q : ℤ) * ((if b ∈ S then 1 else 0) -
    (if a ∈ S then 1 else 0)) ≤ g q G A B S

omit [Fintype V] in
/-- Every retained rectangular cut is paid by the original source cut containing b. -/
theorem retained_cuts (hd : Disjoint A B) (ha : a ∈ A) (hb : b ∈ B)
    (uc : UnitCuts q G A B a b) :
    ∀ X ⊆ A \ {a}, ∀ Y ⊆ B \ {b},
      q * #X ≤ ec G X ((B \ {b}) \ Y) + q * #Y := by
  intro X hX Y hY
  have hXA : X ⊆ A := hX.trans sdiff_subset
  have hYB : Y ⊆ B := hY.trans sdiff_subset
  have haB : a ∉ B := disjoint_left.mp hd ha
  have hbA : b ∉ A := disjoint_right.mp hd hb
  have hab : a ≠ b := fun he => haB (he.symm ▸ hb)
  have haX : a ∉ X := by
    intro hx
    exact (mem_sdiff.mp (hX hx)).2 (mem_singleton_self a)
  have hbY : b ∉ Y := by
    intro hy
    exact (mem_sdiff.mp (hY hy)).2 (mem_singleton_self b)
  let S := X ∪ insert b Y
  have haS : a ∉ S := by
    simp only [S, mem_union, mem_insert]
    exact fun h => h.elim haX (fun h => h.elim hab (fun hy => haB (hYB hy)))
  have hbS : b ∈ S := by simp [S]
  have hAS : A ∩ S = X := by
    ext v
    simp only [S, mem_inter, mem_union, mem_insert]
    constructor
    · rintro ⟨hvA, hvX | hvb | hvY⟩
      · exact hvX
      · exact False.elim (hbA (hvb ▸ hvA))
      · exact False.elim (disjoint_left.mp hd hvA (hYB hvY))
    · intro hvX
      exact ⟨hXA hvX, Or.inl hvX⟩
  have hBS : B ∩ S = insert b Y := by
    ext v
    simp only [S, mem_inter, mem_union, mem_insert]
    constructor
    · rintro ⟨hvB, hvX | hvb | hvY⟩
      · exact False.elim (disjoint_left.mp hd (hXA hvX) hvB)
      · exact Or.inl hvb
      · exact Or.inr hvY
    · intro hv
      exact ⟨hv.elim (fun he => he ▸ hb) (fun hy => hYB hy), Or.inr hv⟩
  have hBout : B \ S = (B \ {b}) \ Y := by
    ext v
    simp only [S, mem_sdiff, mem_union, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hvB, hv⟩
      exact ⟨⟨hvB, fun he => hv (Or.inr (Or.inl he))⟩,
        fun hy => hv (Or.inr (Or.inr hy))⟩
    · rintro ⟨⟨hvB, hvb⟩, hvY⟩
      refine ⟨hvB, ?_⟩
      rintro (hvX | he | hy)
      · exact disjoint_left.mp hd (hXA hvX) hvB
      · exact hvb he
      · exact hvY hy
  have hc := uc S
  simp only [hbS, haS, if_true, if_false, sub_zero, mul_one] at hc
  unfold g k at hc
  rw [hAS, hBS, hBout, card_insert_of_notMem hbY, Nat.cast_add, Nat.cast_one] at hc
  have hz : (q : ℤ) * #X ≤ (ec G X ((B \ {b}) \ Y) : ℤ) + q * #Y := by
    nlinarith
  exact_mod_cast hz

omit [Fintype V] in
/-- The output is a finset of original adjacent pairs, with capacity one per pair. -/
theorem factor_on (hd : Disjoint A B) (hbal : #A = #B)
    (ha : a ∈ A) (hb : b ∈ B) (uc : UnitCuts q G A B a b) :
    FactorOn q G (A \ {a}) (B \ {b}) := by
  have hcard : #(A \ {a}) = #(B \ {b}) := by
    simp only [sdiff_singleton_eq_erase, card_erase_of_mem ha, card_erase_of_mem hb, hbal]
  exact B5Factor.exists_target_factor (A \ {a}) (B \ {b}) hcard
    (retained_cuts hd ha hb uc)

/-- Actual endpoint omission has exact, proper, nonempty support in the original graph. -/
theorem exact_original_factor (hd : Disjoint A B) (hbal : #A = #B)
    (ha : a ∈ A) (hb : b ∈ B) (hq : 0 < q) (hsize : q ≤ #A - 1)
    (uc : UnitCuts q G A B a b) :
    FactorOn q G (A \ {a}) (B \ {b}) ∧
    ∃ H : G.Subgraph,
      H.verts = (↑((A \ {a}) ∪ (B \ {b})) : Set V) ∧
      H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  have hf := factor_on hd hbal ha hb uc
  refine ⟨hf, H3Unequal.factor_exact_subgraph hq ?_ (hd.mono sdiff_subset sdiff_subset) hf⟩
  apply card_pos.mp
  have hc : #(A \ {a}) = #A - 1 := by
    simp only [sdiff_singleton_eq_erase, card_erase_of_mem ha]
  omega

omit [Fintype V] in
/-- The literal exact support equals the original shore union minus both endpoints. -/
theorem support_eq (hd : Disjoint A B) (ha : a ∈ A) (hb : b ∈ B) :
    (A \ {a}) ∪ (B \ {b}) = (A ∪ B) \ {a, b} := by
  have haB : a ∉ B := disjoint_left.mp hd ha
  have hbA : b ∉ A := disjoint_right.mp hd hb
  ext v
  simp only [mem_union, mem_sdiff, mem_singleton, mem_insert]
  aesop

/-- The retained support omits an actual original vertex and is therefore proper. -/
theorem support_proper (hd : Disjoint A B) (ha : a ∈ A) (hb : b ∈ B) :
    #((A \ {a}) ∪ (B \ {b})) < Fintype.card V := by
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, ?_⟩
  intro he
  have haa : a ∈ (A \ {a}) ∪ (B \ {b}) := by rw [he]; exact mem_univ a
  rw [support_eq hd ha hb] at haa
  exact (mem_sdiff.mp haa).2 (by simp)

/-- A reusable contradiction helper for arbitrary-support original Noq. -/
theorem contradict_noq (hd : Disjoint A B) (hbal : #A = #B)
    (ha : a ∈ A) (hb : b ∈ B) (hq : 0 < q) (hsize : q ≤ #A - 1)
    (uc : UnitCuts q G A B a b) (hno : AllHTopCritical.Noq q G) : False := by
  obtain ⟨_, H, _, hn, hr⟩ := exact_original_factor hd hbal ha hb hq hsize uc
  exact hno ⟨H, hn, hr⟩

/-- Direct specialization to the canonical R691 host; no host field supplies UC. -/
theorem host_exact_original_factor {L : ℤ} (host : Host q L G A B)
    (ha : a ∈ A) (hb : b ∈ B) (hsize : q ≤ #A - 1)
    (uc : UnitCuts q G A B a b) :
    FactorOn q G (A \ {a}) (B \ {b}) ∧
    ∃ H : G.Subgraph,
      H.verts = (↑((A \ {a}) ∪ (B \ {b})) : Set V) ∧
      H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  exact exact_original_factor host.disjoint host.balanced ha hb
    (by have h := host.large; omega) hsize uc

#print axioms retained_cuts
#print axioms factor_on
#print axioms exact_original_factor
#print axioms support_eq
#print axioms support_proper
#print axioms contradict_noq
#print axioms host_exact_original_factor
end Erdos585.Omit1UnitCutAdapterR707
