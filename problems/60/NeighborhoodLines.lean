import Mathlib.Combinatorics.Configuration
import Mathlib.Tactic

/-!
Actual projective-incidence ingredients of COUNT-BASED-COMPLETION.md §6.
`cross_pairs_le_missing` constructs an injection from actual cross pairs of
points on two pencil lines into the actual missing-line set.
`three_pencil_dominant` proves at most six outliers on an actual dominant
line from an explicit three-portion pencil decomposition and pair-line premise.
`off_line_join_family` constructs the actual missing-line families at an
exception point. `common_exception_point` proves that any two exception
points from dominant portions must coincide, with the exact numerical range.

Remaining producer obligations: the projective embedding; derivation of the
nonfeasible-neighborhood pair-line premise from the actual graph and its full
rows; selection of a high-incidence neighbor u; construction and ordering of
the at-most-three actual pencil portions. These are NOT assumed conclusions
of any theorem here. No global point-to-line bijection, reciprocity, or
polarity containment is asserted by this bounded ingredient module.
-/

namespace Erdos60.Completion
open Configuration
open scoped Classical
variable {P L : Type*} [Membership P L] [Configuration.HasLines P L]
variable [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]

omit [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L] in
/-- Cross pairs between two disjoint portions of distinct actual lines
inject into their actual joining lines. -/
theorem cross_pairs_le_missing (A B : Finset P) (M : Finset L) (l m : L)
    (ha : ∀ a ∈ A, a ∈ l ∧ a ∉ m)
    (hb : ∀ b ∈ B, b ∈ m ∧ b ∉ l)
    (hpair : ∀ a ∈ A, ∀ b ∈ B, ∀ n : L, a ∈ n → b ∈ n → n ∈ M) :
    A.card * B.card ≤ M.card := by
  classical
  have hne (a : A) (b : B) : (a : P) ≠ b := by
    intro h
    exact (ha a a.property).2 (h ▸ (hb b b.property).1)
  let f : A × B → {n // n ∈ M} := fun ab =>
    ⟨Configuration.HasLines.mkLine (hne ab.1 ab.2),
      hpair ab.1 ab.1.property ab.2 ab.2.property _
        (Configuration.HasLines.mkLine_ax (P := P) (L := L) (hne ab.1 ab.2)).1
        (Configuration.HasLines.mkLine_ax (P := P) (L := L) (hne ab.1 ab.2)).2⟩
  have hf : Function.Injective f := by
    intro ab cd hh
    have he : (f ab).val = (f cd).val := congrArg Subtype.val hh
    have hab : ab.1.val ∈ (f ab).val ∧ ab.2.val ∈ (f ab).val := Configuration.HasLines.mkLine_ax (P := P) (L := L) (hne ab.1 ab.2)
    have hcd : cd.1.val ∈ (f cd).val ∧ cd.2.val ∈ (f cd).val := Configuration.HasLines.mkLine_ax (P := P) (L := L) (hne cd.1 cd.2)
    have hac : ab.1.val = cd.1.val := by
      have hnl : (f ab).val ≠ l := by
        intro h
        exact (hb ab.2 ab.2.property).2 (h ▸ hab.2)
      exact (Configuration.Nondegenerate.eq_or_eq
        hab.1 (by rw [he]; exact hcd.1) (ha ab.1 ab.1.property).1 (ha cd.1 cd.1.property).1).resolve_right hnl
    have hbd : ab.2.val = cd.2.val := by
      have hnm : (f ab).val ≠ m := by
        intro h
        exact (ha ab.1 ab.1.property).2 (h ▸ hab.1)
      exact (Configuration.Nondegenerate.eq_or_eq
        hab.2 (by rw [he]; exact hcd.2) (hb ab.2 ab.2.property).1 (hb cd.2 cd.2.property).1).resolve_right hnm
    exact Prod.ext (Subtype.ext hac) (Subtype.ext hbd)
  have hh := Fintype.card_le_of_injective f hf
  simpa using hh

omit [Fintype P] [Fintype L] [DecidableEq P] in
/-- The joins from an off-line point to distinct points on an actual line
are distinct actual members of the missing-line set. -/
theorem off_line_join_family (A : Finset P) (M : Finset L) (l : L) (w : P)
    (hw : w ∉ l) (ha : ∀ a ∈ A, a ∈ l)
    (hpair : ∀ a ∈ A, ∀ n : L, w ∈ n → a ∈ n → n ∈ M) :
    ∃ Q : Finset L, Q ⊆ M ∧ Q.card = A.card ∧ ∀ n ∈ Q, w ∈ n := by
  classical
  have hne (a : A) : w ≠ (a : P) := fun h => hw (h ▸ ha a a.property)
  let f : A → L := fun a => Configuration.HasLines.mkLine (hne a)
  let Q := Finset.univ.image f
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    have hn : f a ≠ l := by
      intro h
      exact hw (h ▸ (Configuration.HasLines.mkLine_ax (P := P) (L := L) (hne a)).1)
    exact (Configuration.Nondegenerate.eq_or_eq
      (Configuration.HasLines.mkLine_ax (P := P) (L := L) (hne a)).2
      (by change (b:P) ∈ f a; rw [he]; exact (Configuration.HasLines.mkLine_ax (P := P) (L := L) (hne b)).2)
      (ha a a.property) (ha b b.property)).resolve_right hn
  refine ⟨Q,?_,?_,?_⟩
  · intro n hn
    obtain ⟨a,ha',rfl⟩ := Finset.mem_image.mp hn
    exact hpair a a.property _ (Configuration.HasLines.mkLine_ax (P := P) (L := L) (hne a)).1
      (Configuration.HasLines.mkLine_ax (P := P) (L := L) (hne a)).2
  · simp [Q, Finset.card_image_of_injective _ hf]
  · intro n hn
    obtain ⟨a,ha',rfl⟩ := Finset.mem_image.mp hn
    exact (Configuration.HasLines.mkLine_ax (P := P) (L := L) (hne a)).1

omit [Fintype P] [Fintype L] in
/-- Two sufficiently large actual missing-line families cannot have distinct
centers, because two different points determine at most one common line. -/
theorem large_pencils_same_center (M Q R : Finset L) (w z : P)
    (hQ : Q ⊆ M) (hR : R ⊆ M)
    (hw : ∀ n ∈ Q, w ∈ n) (hz : ∀ n ∈ R, z ∈ n)
    (hlarge : M.card + 1 < Q.card + R.card) : w = z := by
  classical
  by_contra hne
  have hi : (Q ∩ R).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro l hl m hm
    have hl' := Finset.mem_inter.mp hl
    have hm' := Finset.mem_inter.mp hm
    exact (Configuration.Nondegenerate.eq_or_eq
      (hw l hl'.1) (hz l hl'.2) (hw m hm'.1) (hz m hm'.2)).resolve_left hne
  have hu : (Q ∪ R).card ≤ M.card :=
    Finset.card_le_card (Finset.union_subset hQ hR)
  have hh := Finset.card_union_add_card_inter Q R
  omega

omit [Fintype P] [Fintype L] [DecidableEq L] in
/-- Three actual pencil portions give a dominant actual line with at most
six outliers, using the §6 constants. The pencil decomposition is explicit;
this theorem does not assume near-collinearity. -/
theorem three_pencil_dominant (N A B C : Finset P) (M : Finset L)
    (l m n : L) (u : P) (q : ℝ) (hq : 10^8 ≤ q)
    (hN : 999*q/1000 ≤ N.card) (hM : (M.card : ℝ) ≤ 1002*q/1000)
    (hu : u ∈ l) (hcover : N ⊆ insert u (A ∪ B ∪ C))
    (hA : A ⊆ N) (hB : B ⊆ N) (hC : C ⊆ N)
    (ha : ∀ a ∈ A, a ∈ l ∧ a ∉ m ∧ a ∉ n)
    (hb : ∀ b ∈ B, b ∈ m ∧ b ∉ l)
    (hc : ∀ c ∈ C, c ∈ n ∧ c ∉ l)
    (hmaxB : B.card ≤ A.card) (hmaxC : C.card ≤ A.card)
    (hpair : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → ∀ k : L, x ∈ k → y ∈ k → k ∈ M) :
    (N.filter fun x => x ∉ l).card ≤ 6 := by
  classical
  have hAB := cross_pairs_le_missing A B M l m
    (fun a ha' => ⟨(ha a ha').1,(ha a ha').2.1⟩) hb
    (fun a ha' b hb' k hak hbk => hpair a (hA ha') b (hB hb')
      (fun he => (hb b hb').2 (he ▸ (ha a ha').1)) k hak hbk)
  have hAC := cross_pairs_le_missing A C M l n
    (fun a ha' => ⟨(ha a ha').1,(ha a ha').2.2⟩) hc
    (fun a ha' c hc' k hak hck => hpair a (hA ha') c (hC hc')
      (fun he => (hc c hc').2 (he ▸ (ha a ha').1)) k hak hck)
  have hn : N.card ≤ 1 + A.card + B.card + C.card := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_insert_le u (A ∪ B ∪ C)
    have h3 := Finset.card_union_le (A ∪ B) C
    have h4 := Finset.card_union_le A B
    omega
  have hnR : (N.card : ℝ) ≤ 1 + (A.card : ℝ) + B.card + C.card := by exact_mod_cast hn
  have hbR : (B.card : ℝ) ≤ A.card := by exact_mod_cast hmaxB
  have hcR : (C.card : ℝ) ≤ A.card := by exact_mod_cast hmaxC
  have habR : (A.card : ℝ) * B.card ≤ M.card := by exact_mod_cast hAB
  have hacR : (A.card : ℝ) * C.card ≤ M.card := by exact_mod_cast hAC
  have hb3 : B.card ≤ 3 := by
    by_contra hh
    have hh4 : (4 : ℝ) ≤ B.card := by exact_mod_cast (show 4 ≤ B.card by omega)
    have hmul : 4*(A.card : ℝ) ≤ (A.card : ℝ)*B.card := by nlinarith [mul_nonneg (show 0 ≤ (A.card : ℝ) by positivity) (sub_nonneg.mpr hh4)]
    nlinarith
  have hc3 : C.card ≤ 3 := by
    by_contra hh
    have hh4 : (4 : ℝ) ≤ C.card := by exact_mod_cast (show 4 ≤ C.card by omega)
    have hmul : 4*(A.card : ℝ) ≤ (A.card : ℝ)*C.card := by nlinarith [mul_nonneg (show 0 ≤ (A.card : ℝ) by positivity) (sub_nonneg.mpr hh4)]
    nlinarith
  have hs : N.filter (fun x => x ∉ l) ⊆ B ∪ C := by
    intro x hx
    obtain ⟨hxN,hxl⟩ := Finset.mem_filter.mp hx
    have hh := hcover hxN
    simp only [Finset.mem_insert, Finset.mem_union] at hh ⊢
    rcases hh with rfl | (ha'|hb') | hc'
    · exact False.elim (hxl hu)
    · exact False.elim (hxl (ha x ha').1)
    · exact Or.inl hb'
    · exact Or.inr hc'
  have hh := (Finset.card_le_card hs).trans (Finset.card_union_le B C)
  omega

omit [Fintype P] [Fintype L] in
/-- Any two exceptional points arising from such dominant line portions are
the same point, even when they belong to different neighborhoods. -/
theorem common_exception_point (A B : Finset P) (M : Finset L) (l m : L) (w z : P)
    (q : ℝ) (hq : 10^8 ≤ q)
    (hM : (M.card : ℝ) ≤ 1002*q/1000)
    (hA : 999*q/1000-6 ≤ A.card) (hB : 999*q/1000-6 ≤ B.card)
    (hw : w ∉ l) (hz : z ∉ m)
    (ha : ∀ a ∈ A, a ∈ l) (hb : ∀ b ∈ B, b ∈ m)
    (hpairA : ∀ a ∈ A, ∀ k : L, w ∈ k → a ∈ k → k ∈ M)
    (hpairB : ∀ b ∈ B, ∀ k : L, z ∈ k → b ∈ k → k ∈ M) : w = z := by
  obtain ⟨Q,hQ,hQc,hQw⟩ := off_line_join_family A M l w hw ha hpairA
  obtain ⟨R,hR,hRc,hRz⟩ := off_line_join_family B M m z hz hb hpairB
  apply large_pencils_same_center M Q R w z hQ hR hQw hRz
  rw [hQc,hRc]
  have hh : (M.card : ℝ) + 1 < (A.card : ℝ) + B.card := by linarith
  exact_mod_cast hh

#print axioms three_pencil_dominant
#print axioms common_exception_point
#print axioms cross_pairs_le_missing
#print axioms off_line_join_family
#print axioms large_pencils_same_center
end Erdos60.Completion
