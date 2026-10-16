import AllHNextNonstrict.Intersections

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHNextNonstrict
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Data
variable {h q a₀ j : ℕ} {A B : Finset V} (d : Data h q a₀ j G A B)
include d

lemma high_compare_union {Z K T : Finset V} (hk : AllHTopTwo.HighAbove q j G A B Z K)
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

/-- Finite descent in the remaining maximum height. The escape premise is an
internal lemma proved from Data in PetalEscape, never a public host premise. -/
lemma select_up_to (escape : PetalEscapeClaim (G := G)) {N : Finset V}
    (hn : Neighborhood q j G A B N) :
    ∀ (n : ℕ) (Z : Finset V), Z ⊆ B \ N →
      (∀ T, LargePositive q j G A B T → Z ⊆ T → thetaJ q j G A B T ≤ 2 * (n : ℤ)) →
      ∃ Y : Finset V, Y ⊆ B \ N ∧ Z ⊆ Y ∧ #Y ≤ #Z + n ∧
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
        have hban : N \ K ⊆ B \ K := Finset.sdiff_subset_sdiff_left K hn.subset
        have hbanCard := d.neighborhood_residual hn hk.positive.1 hk.positive.2.1 hk.positive.2.2
        have hstep : ∃ z ∈ B \ K, z ∉ N ∧
            ∀ T, LargePositive q j G A B T → insert z Z ⊆ T →
              thetaJ q j G A B T ≤ 2 * (n : ℤ) := by
          by_cases htwo : 2 ≤ thetaJ q j G A B K
          · obtain ⟨z, hzR, hzban, hcost⟩ :=
              escape h q a₀ j A B K (N \ K) d hk.positive.1 hk.positive.2.1 htwo hk.strict hban hbanCard
            have hzK := (mem_sdiff.mp hzR).2
            have hzN : z ∉ N := fun hz => hzban (mem_sdiff.mpr ⟨hz, hzK⟩)
            refine ⟨z, hzR, hzN, ?_⟩
            intro T hT hZT
            have hzT : z ∈ T := hZT (mem_insert_self _ _)
            have hZTi : Z ⊆ T := (subset_insert z Z).trans hZT
            have hc := hcost (T \ K) (Finset.sdiff_subset_sdiff_left K hT.1) (mem_sdiff.mpr ⟨hzT, hzK⟩)
            have he : K ∪ (T \ K) = K ∪ T := by
              ext a
              simp only [mem_union, mem_sdiff]
              tauto
            rw [extensionCost, he] at hc
            have hcomp := d.high_compare_union hk hT hZTi
            push_cast at hH
            omega
          · have hR := d.positive_complement hk.positive.1 hk.positive.2.2
            have hq := d.parameters.numeric
            have hav : ((B \ K) \ (N \ K)).Nonempty := by
              apply card_pos.mp
              have hc := card_sdiff_add_card_eq_card hban
              omega
            obtain ⟨z, hz⟩ := hav
            obtain ⟨hzR, hzban⟩ := mem_sdiff.mp hz
            have hzK := (mem_sdiff.mp hzR).2
            have hzN : z ∉ N := fun hzN => hzban (mem_sdiff.mpr ⟨hzN, hzK⟩)
            refine ⟨z, hzR, hzN, ?_⟩
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
        obtain ⟨z, hzR, hzN, hzmax⟩ := hstep
        have hnew : insert z Z ⊆ B \ N := by
          apply insert_subset_iff.mpr
          exact ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp hzR).1, hzN⟩, hZ⟩
        obtain ⟨Y, hY, hZY, hcard, hkill⟩ := ih (insert z Z) hnew hzmax
        refine ⟨Y, hY, (subset_insert z Z).trans hZY, ?_, hkill⟩
        have hc := card_insert_le z Z
        omega
      · refine ⟨Z, hZ, Subset.rfl, by omega, ?_⟩
        intro T hT hZT
        exact hex ⟨T, hT, hZT⟩

/-- The odd maximum uses one actual top escape; lower heights use two-unit gains. -/
theorem common_omission (escape : PetalEscapeClaim (G := G))
    (top : TopEscapeClaim (G := G)) :
    ∃ O : Finset V, O ⊆ B ∧ #O = j ∧
      ∀ T ⊆ B, O ⊆ T → thetaJ q j G A B T ≤ 0 := by
  obtain ⟨N, hn⟩ := d.exists_neighborhood
  have hexY : ∃ Y : Finset V, Y ⊆ B \ N ∧ #Y ≤ j ∧
      ∀ T, LargePositive q j G A B T → Y ⊆ T → False := by
    by_cases hex : ∃ T, LargePositive q j G A B T
    · obtain ⟨K, hk⟩ := AllHTopTwo.exists_high_above (G := G) q j
        (show ∃ T, LargePositive q j G A B T ∧ (∅ : Finset V) ⊆ T from
          by obtain ⟨T, hT⟩ := hex; exact ⟨T, hT, empty_subset _⟩)
      by_cases hlow : thetaJ q j G A B K ≤ 2 * (j : ℤ)
      · have hheight : ∀ T, LargePositive q j G A B T → (∅ : Finset V) ⊆ T →
            thetaJ q j G A B T ≤ 2 * (j : ℤ) := by
          intro T hT hZT
          exact (hk.height T hT hZT).trans hlow
        obtain ⟨Y, hY, _, hcY, hkill⟩ :=
          d.select_up_to escape hn j ∅ (empty_subset _) hheight
        exact ⟨Y, hY, by simpa using hcY, hkill⟩
      · have hbound := d.theta_large_le hk.positive.1 hk.positive.2.1
        have hj := d.parameters.surplus_int
        have htop : thetaJ q j G A B K = 2 * (j : ℤ) + 1 := by omega
        have hban := Finset.sdiff_subset_sdiff_left K hn.subset
        have hbanCard := d.neighborhood_top_residual hn hk.positive.1 hk.positive.2.1 htop
        obtain ⟨z, hzR, hzban, hcost⟩ := top h q a₀ j A B K (N \ K) d
          hk.positive.1 hk.positive.2.1 htop hk.strict hban hbanCard
        have hzK := (mem_sdiff.mp hzR).2
        have hzN : z ∉ N := fun hz => hzban (mem_sdiff.mpr ⟨hz, hzK⟩)
        have hZ : ({z} : Finset V) ⊆ B \ N :=
          singleton_subset_iff.mpr (mem_sdiff.mpr ⟨(mem_sdiff.mp hzR).1, hzN⟩)
        have hheight : ∀ T, LargePositive q j G A B T → ({z} : Finset V) ⊆ T →
            thetaJ q j G A B T ≤ 2 * ((j - 1 : ℕ) : ℤ) := by
          intro T hT hZT
          have hzT := hZT (mem_singleton_self _)
          have hc := hcost (T \ K) (Finset.sdiff_subset_sdiff_left K hT.1)
            (mem_sdiff.mpr ⟨hzT, hzK⟩)
          have he : K ∪ (T \ K) = K ∪ T := by
            ext v
            simp only [mem_union, mem_sdiff]
            tauto
          rw [extensionCost, he] at hc
          have hcomp := d.high_compare_union hk hT (empty_subset _)
          have hjpos := d.parameters.j_pos
          omega
        obtain ⟨Y, hY, _, hcY, hkill⟩ :=
          d.select_up_to escape hn (j-1) {z} hZ hheight
        have hjpos := d.parameters.j_pos
        exact ⟨Y, hY, by simp only [card_singleton] at hcY; omega, hkill⟩
    · exact ⟨∅, empty_subset _, by simp, fun T hT _ => hex ⟨T, hT⟩⟩
  obtain ⟨Y, hY, hYj, hkill⟩ := hexY
  have hB := d.neighborhood_available hn
  have hav : j - #Y ≤ #((B \ N) \ Y) := by
    have hc := card_sdiff_add_card_eq_card hY
    omega
  obtain ⟨U, hU, hcU⟩ := exists_subset_card_eq hav
  have hdis : Disjoint Y U := disjoint_left.mpr fun _ hy hu => (mem_sdiff.mp (hU hu)).2 hy
  let O := Y ∪ U
  have hOBN : O ⊆ B \ N := union_subset hY (hU.trans sdiff_subset)
  have hOj : #O = j := by
    rw [card_union_of_disjoint hdis]
    omega
  refine ⟨O, hOBN.trans sdiff_subset, hOj, ?_⟩
  intro T hT hOT
  by_cases hlarge : q - 1 ≤ #T
  · by_contra! hp
    exact hkill T ⟨hT, hlarge, hp⟩ ((subset_union_left : Y ⊆ O).trans hOT)
  · have hq := d.parameters.q_pos
    exact d.small_good hn hOBN hOj hT hOT (by omega)

end Data
end Erdos585.AllHNextNonstrict
