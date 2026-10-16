import AllHLargestNonstrict.Intersections

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHLargestNonstrict
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Data
variable {h q a₀ j : ℕ} {A B : Finset V} (d : Data h q a₀ j G A B)
include d

/-- Only the parameter-free finite maximum interface is reused from R109. -/
lemma high_compare_union {Z K T : Finset V}
    (hk : AllHTopTwo.HighAbove q j G A B Z K)
    (hT : LargePositive q j G A B T) (hZT : Z ⊆ T) :
    thetaJ q j G A B T ≤ thetaJ q j G A B (K ∪ T) := by
  have hI := d.large_intersection hk.positive.1 hk.positive.2.1 hk.positive.2.2
    hT.1 hT.2.1 hT.2.2
  have hzi : Z ⊆ K ∩ T := subset_inter hk.contains hZT
  have hθi : thetaJ q j G A B (K ∩ T) ≤ thetaJ q j G A B K := by
    by_cases hp : 0 < thetaJ q j G A B (K ∩ T)
    · exact hk.height _ ⟨inter_subset_left.trans hk.positive.1, hI, hp⟩ hzi
    · have hpk := hk.positive.2.2
      omega
  have hs := H3Unequal.Input.theta_supermod (G := G) q j A B K T
  omega

/-- The local escape is discharged by the new nonstrict PetalEscape proof in Main. -/
lemma select_up_to (escape : PetalEscapeClaim (G := G)) :
    ∀ (n : ℕ) (Z : Finset V), Z ⊆ B →
      (∀ T, LargePositive q j G A B T → Z ⊆ T → thetaJ q j G A B T ≤ 2 * (n : ℤ)) →
      ∃ Y : Finset V, Y ⊆ B ∧ Z ⊆ Y ∧ #Y ≤ #Z + n ∧
        ∀ T, LargePositive q j G A B T → Y ⊆ T → False := by
  intro n
  induction n with
  | zero =>
      intro Z hZ hmax
      refine ⟨Z, hZ, Subset.rfl, by omega, ?_⟩
      intro T hT hZT
      have hh := hmax T hT hZT
      have hp := hT.2.2
      norm_num at hh
      omega
  | succ n ih =>
      intro Z hZ hmax
      by_cases hex : ∃ T, LargePositive q j G A B T ∧ Z ⊆ T
      · obtain ⟨K, hk⟩ := AllHTopTwo.exists_high_above (G := G) q j hex
        have hH := hmax K hk.positive hk.contains
        have hstep : ∃ z ∈ B \ K,
            ∀ T, LargePositive q j G A B T → insert z Z ⊆ T →
              thetaJ q j G A B T ≤ 2 * (n : ℤ) := by
          by_cases htwo : 2 ≤ thetaJ q j G A B K
          · obtain ⟨z, hzR, hcost⟩ :=
              escape h q a₀ j A B K d hk.positive.1 hk.positive.2.1 htwo hk.strict
            have hzK := (mem_sdiff.mp hzR).2
            refine ⟨z, hzR, ?_⟩
            intro T hT hZT
            have hzT : z ∈ T := hZT (mem_insert_self _ _)
            have hZTi : Z ⊆ T := (subset_insert z Z).trans hZT
            have hc := hcost (T \ K) (Finset.sdiff_subset_sdiff_left K hT.1)
              (mem_sdiff.mpr ⟨hzT, hzK⟩)
            have he : K ∪ (T \ K) = K ∪ T := by
              ext v
              simp only [mem_union, mem_sdiff]
              tauto
            rw [extensionCost, he] at hc
            have hcomp := d.high_compare_union hk hT hZTi
            push_cast at hH
            omega
          · have hR := d.positive_complement hk.positive.1 hk.positive.2.2
            have hav : (B \ K).Nonempty := card_pos.mp (by omega)
            obtain ⟨z, hzR⟩ := hav
            have hzK := (mem_sdiff.mp hzR).2
            refine ⟨z, hzR, ?_⟩
            intro T hT hZT
            have hzT : z ∈ T := hZT (mem_insert_self _ _)
            have hZTi : Z ⊆ T := (subset_insert z Z).trans hZT
            have hne : K ≠ K ∪ T := by
              intro he
              exact hzK (he ▸ mem_union_right K hzT)
            have hstrict := hk.strict (K ∪ T) (union_subset hk.positive.1 hT.1)
              subset_union_left hne
            have hcomp := d.high_compare_union hk hT hZTi
            have hpos := hT.2.2
            omega
        obtain ⟨z, hzR, hzmax⟩ := hstep
        have hnew : insert z Z ⊆ B :=
          insert_subset_iff.mpr ⟨(mem_sdiff.mp hzR).1, hZ⟩
        obtain ⟨Y, hY, hZY, hcard, hkill⟩ := ih (insert z Z) hnew hzmax
        refine ⟨Y, hY, (subset_insert z Z).trans hZY, ?_, hkill⟩
        have hc := card_insert_le z Z
        omega
      · refine ⟨Z, hZ, Subset.rfl, by omega, ?_⟩
        intro T hT hZT
        exact hex ⟨T, hT, hZT⟩

/-- The same original omission pays all cuts under the nonstrict floor. -/
theorem common_omission (escape : PetalEscapeClaim (G := G)) :
    ∃ O : Finset V, O ⊆ B ∧ #O = j ∧
      ∀ T ⊆ B, O ⊆ T → thetaJ q j G A B T ≤ 0 := by
  have hheight : ∀ T, LargePositive q j G A B T → (∅ : Finset V) ⊆ T →
      thetaJ q j G A B T ≤ 2 * (j : ℤ) := by
    intro T hT _
    have hh := d.theta_large_le hT.1 hT.2.1
    have hj := d.parameters.j_bounds
    omega
  obtain ⟨Y, hY, _, hcY, hkill⟩ := d.select_up_to escape j ∅ (empty_subset _) hheight
  have hYj : #Y ≤ j := by simpa using hcY
  have hB : j ≤ #B := by have hc := d.shores_large; omega
  have hav : j - #Y ≤ #(B \ Y) := by
    have hc := card_sdiff_add_card_eq_card hY
    omega
  obtain ⟨U, hU, hcU⟩ := exists_subset_card_eq hav
  have hdis : Disjoint Y U := disjoint_left.mpr fun _ hy hu => (mem_sdiff.mp (hU hu)).2 hy
  let O := Y ∪ U
  have hOB : O ⊆ B := union_subset hY (hU.trans sdiff_subset)
  have hOj : #O = j := by
    rw [card_union_of_disjoint hdis]
    omega
  refine ⟨O, hOB, hOj, ?_⟩
  intro T hT hOT
  by_cases hlarge : q - 1 ≤ #T
  · by_contra! hp
    exact hkill T ⟨hT, hlarge, hp⟩ ((subset_union_left : Y ⊆ O).trans hOT)
  · have hq := d.parameters.q_pos
    exact d.small_good hOj hOT (by omega)

end Data
end Erdos585.AllHLargestNonstrict
