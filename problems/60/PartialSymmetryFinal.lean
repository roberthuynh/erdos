import SymmetryIncidenceCount
import PartialSymmetry

namespace Erdos60.PartialSymmetryFinal
open Finset
open Erdos60.PartialSymmetryCompletion
variable {P L : Type*} [Membership P L] [Fintype P] [Fintype L]

noncomputable def transposeRow (line : P ≃ L) (x : P) : Finset P := by
  classical
  exact univ.filter (fun y => x ∈ line y)

@[simp] theorem mem_transposeRow (line : P ≃ L) (x y : P) :
    y ∈ transposeRow line x ↔ x ∈ line y := by
  classical
  simp [transposeRow]

theorem transposeRow_card [Configuration.ProjectivePlane P L] (line : P ≃ L) (x : P) :
    (transposeRow line x).card = Configuration.ProjectivePlane.order P L+1 := by
  classical
  have he := Fintype.card_congr (line.subtypeEquivOfSubtype (p := fun l : L => x ∈ l))
  have hc := Configuration.ProjectivePlane.lineCount_eq L x
  have hc' : Fintype.card {l : L // x ∈ l} = Configuration.ProjectivePlane.order P L+1 := by
    simpa [Configuration.lineCount, Nat.card_eq_fintype_card] using hc
  simpa [transposeRow, Fintype.card_subtype] using he.trans hc'

theorem good_tangent [Configuration.ProjectivePlane P L] (line : P ≃ L)
    (good : Finset P) (hs : Erdos60.PartialSymmetry.SymmetricAt line (↑good : Set P))
    {x a : P} (ha : a ∈ good) (hxa : x ≠ a) :
    (sectionPts (transposeRow line x) (line a)).card = 1 := by
  classical
  obtain ⟨l, hl, huniq⟩ := Configuration.HasLines.existsUnique_line P L x a hxa
  let y := line.symm l
  have hyl : line y = l := line.apply_symm_apply l
  apply Finset.card_eq_one.mpr
  refine ⟨y, ?_⟩
  ext z
  simp only [sectionPts, mem_filter, mem_transposeRow, mem_singleton]
  constructor
  · intro hz
    have haz : a ∈ line z := (hs a ha z).mpr hz.2
    have hline : line z = l := huniq (line z) ⟨hz.1, haz⟩
    apply line.injective
    exact hline.trans hyl.symm
  · intro hz
    subst z
    refine ⟨?_, ?_⟩
    · rw [hyl]
      exact hl.1
    · apply (hs a ha y).mp
      rw [hyl]
      exact hl.2

/-- The first substantive completion step: every transposed row is a line
of the actual plane. The size hypothesis bounds the exceptional index set. -/
theorem transposeRow_is_line [Configuration.ProjectivePlane P L] (line : P ≃ L)
    (good : Finset P) (hs : Erdos60.PartialSymmetry.SymmetricAt line (↑good : Set P))
    (hsize : Fintype.card P + 2 ≤ good.card + 2*Configuration.ProjectivePlane.order P L)
    (x : P) : ∃ l : L, transposeRow line x = sectionPts (univ : Finset P) l := by
  classical
  by_cases hx : x ∈ good
  · refine ⟨line x, ?_⟩
    ext y
    simp only [mem_transposeRow, sectionPts, mem_filter, mem_univ, true_and]
    exact hs x hx y
  · have hS := transposeRow_card line x
    have hcol : ∃ l : L, ∀ z ∈ transposeRow line x, z ∈ l := by
      by_contra hn
      push_neg at hn
      have hb := bad_lines_lower_of_not_collinear (transposeRow line x) hS hn
      let bad : Finset L := univ.filter (fun l => (sectionPts (transposeRow line x) l).card ≠ 1)
      have hdis : Disjoint bad (good.image line) := by
        apply Finset.disjoint_left.mpr
        intro l hl hg
        obtain ⟨a, ha, rfl⟩ := mem_image.mp hg
        have hneq : x ≠ a := fun he => hx (he ▸ ha)
        have ht := good_tangent line good hs ha hneq
        exact (mem_filter.mp hl).2 ht
      have hcard : bad.card + good.card ≤ Fintype.card L := by
        have hh := Finset.card_le_card (Finset.subset_univ (bad ∪ good.image line))
        rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ line.injective] at hh
        simpa using hh
      have heq : Fintype.card P = Fintype.card L :=
        (Configuration.ProjectivePlane.card_points P L).trans
          (Configuration.ProjectivePlane.card_lines P L).symm
      change 2*Configuration.ProjectivePlane.order P L ≤ bad.card at hb
      omega
    obtain ⟨l, hl⟩ := hcol
    refine ⟨l, Finset.eq_of_subset_of_card_le ?_ ?_⟩
    · intro z hz
      simp [sectionPts, hl z hz]
    · have hc := Configuration.ProjectivePlane.pointCount_eq P l
      have hcard : (sectionPts (univ : Finset P) l).card = Configuration.ProjectivePlane.order P L+1 := by
        simpa [sectionPts, Configuration.pointCount, Nat.card_eq_fintype_card,
          Fintype.card_subtype] using hc
      omega

theorem poor_lines_unique [Configuration.ProjectivePlane P L] (line : P ≃ L)
    (good : Finset P)
    (hsize : Fintype.card P+2 ≤ good.card+2*Configuration.ProjectivePlane.order P L)
    {x y : P} (hx : (sectionPts good (line x)).card ≤ 1)
    (hy : (sectionPts good (line y)).card ≤ 1) : x = y := by
  classical
  by_contra hxy
  let A := sectionPts (univ : Finset P) (line x)
  let B := sectionPts (univ : Finset P) (line y)
  let A' := A \ good
  let B' := B \ good
  have hac : A.card = Configuration.ProjectivePlane.order P L+1 := by
    simpa [A, sectionPts, Configuration.pointCount, Nat.card_eq_fintype_card,
      Fintype.card_subtype] using Configuration.ProjectivePlane.pointCount_eq P (line x)
  have hbc : B.card = Configuration.ProjectivePlane.order P L+1 := by
    simpa [B, sectionPts, Configuration.pointCount, Nat.card_eq_fintype_card,
      Fintype.card_subtype] using Configuration.ProjectivePlane.pointCount_eq P (line y)
  have hai : A ∩ good = sectionPts good (line x) := by
    ext a
    simp [A, sectionPts, and_comm]
  have hbi : B ∩ good = sectionPts good (line y) := by
    ext a
    simp [B, sectionPts, and_comm]
  have ha := Finset.card_sdiff_add_card_inter A good
  have hb := Finset.card_sdiff_add_card_inter B good
  rw [hai] at ha
  rw [hbi] at hb
  have hab : (A' ∩ B').card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have haa := (mem_sdiff.mp (mem_inter.mp ha).1).1
    have hab := (mem_sdiff.mp (mem_inter.mp ha).2).1
    have hba := (mem_sdiff.mp (mem_inter.mp hb).1).1
    have hbb := (mem_sdiff.mp (mem_inter.mp hb).2).1
    have haa' : a ∈ line x := by simpa [A, sectionPts] using haa
    have hab' : a ∈ line y := by simpa [B, sectionPts] using hab
    have hba' : b ∈ line x := by simpa [A, sectionPts] using hba
    have hbb' : b ∈ line y := by simpa [B, sectionPts] using hbb
    exact (Configuration.Nondegenerate.eq_or_eq haa' hba' hab' hbb').resolve_right
      (fun he => hxy (line.injective he))
  have hdis : Disjoint (A' ∪ B') good := by
    apply Finset.disjoint_left.mpr
    intro a ha hg
    rcases mem_union.mp ha with h | h
    · exact (mem_sdiff.mp h).2 hg
    · exact (mem_sdiff.mp h).2 hg
  have hle := Finset.card_le_card (Finset.subset_univ ((A' ∪ B') ∪ good))
  rw [Finset.card_union_of_disjoint hdis] at hle
  have hu := Finset.card_union_add_card_inter A' B'
  simp only [Finset.card_univ] at hle
  change A'.card + (sectionPts good (line x)).card = A.card at ha
  change B'.card + (sectionPts good (line y)).card = B.card at hb
  omega

/-- A row with two good points is already fixed by the row-line completion. -/
theorem rich_row_symmetric [Configuration.ProjectivePlane P L] (line : P ≃ L)
    (good : Finset P) (hs : Erdos60.PartialSymmetry.SymmetricAt line (↑good : Set P))
    (hsize : Fintype.card P+2 ≤ good.card+2*Configuration.ProjectivePlane.order P L)
    {x : P} (hx : 2 ≤ (sectionPts good (line x)).card) :
    ∀ y : P, x ∈ line y ↔ y ∈ line x := by
  classical
  obtain ⟨l, hl⟩ := transposeRow_is_line line good hs hsize x
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hx
  have ha' : a ∈ good ∧ a ∈ line x := by simpa [sectionPts] using ha
  have hb' : b ∈ good ∧ b ∈ line x := by simpa [sectionPts] using hb
  have hal : a ∈ l := by
    have hax := (hs a ha'.1 x).mp ha'.2
    have har : a ∈ transposeRow line x := by simpa using hax
    rw [hl] at har
    simpa [sectionPts] using har
  have hbl : b ∈ l := by
    have hbx := (hs b hb'.1 x).mp hb'.2
    have hbr : b ∈ transposeRow line x := by simpa using hbx
    rw [hl] at hbr
    simpa [sectionPts] using hbr
  have he : l = line x :=
    (Configuration.Nondegenerate.eq_or_eq hal hbl ha'.2 hb'.2).resolve_left hab
  intro y
  have hmem := Finset.ext_iff.mp hl y
  simpa [sectionPts, he] using hmem

/-- Full partial-incidence symmetry. The size assumption is the equivalent
complement bound; `partial_symmetry` below gives the published threshold. -/
theorem partial_symmetry_complement [Configuration.ProjectivePlane P L]
    (line : P ≃ L) (good : Finset P)
    (hs : Erdos60.PartialSymmetry.SymmetricAt line (↑good : Set P))
    (hsize : Fintype.card P+2 ≤ good.card+2*Configuration.ProjectivePlane.order P L) :
    ∀ x y : P, x ∈ line y ↔ y ∈ line x := by
  classical
  intro x y
  by_cases hx : 2 ≤ (sectionPts good (line x)).card
  · exact rich_row_symmetric line good hs hsize hx y
  · by_cases hy : 2 ≤ (sectionPts good (line y)).card
    · exact (rich_row_symmetric line good hs hsize hy x).symm
    · have he : x = y := poor_lines_unique line good hsize (by omega) (by omega)
      subst y
      rfl

/-- Published HMY (2023) Lemma 2.1, with a common point/line indexing.
The selected rows are symmetric against all columns, including the complement. -/
theorem partial_symmetry [Configuration.ProjectivePlane P L]
    (line : P ≃ L) (good : Finset P)
    (hs : Erdos60.PartialSymmetry.SymmetricAt line (↑good : Set P))
    (hsize : Configuration.ProjectivePlane.order P L^2-
      Configuration.ProjectivePlane.order P L+3 ≤ good.card) :
    ∀ x y : P, x ∈ line y ↔ y ∈ line x := by
  apply partial_symmetry_complement line good hs
  have hq := Configuration.ProjectivePlane.one_lt_order P L
  have hc := Configuration.ProjectivePlane.card_points P L
  have hh : Configuration.ProjectivePlane.order P L ≤
      Configuration.ProjectivePlane.order P L^2 := by nlinarith
  omega

#print axioms transposeRow_is_line
#print axioms poor_lines_unique
#print axioms rich_row_symmetric
#print axioms partial_symmetry
end Erdos60.PartialSymmetryFinal
