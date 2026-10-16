import AllHTopTwo.Intersections

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHTopTwo
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A maximum-height original positive test above the current chosen points.
Its strict maximum property is derived by finite maximization. -/
structure HighAbove (q j : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B Z K : Finset V) : Prop where
  positive : LargePositive q j G A B K
  contains : Z ⊆ K
  height : ∀ T, LargePositive q j G A B T → Z ⊆ T →
    thetaJ q j G A B T ≤ thetaJ q j G A B K
  strict : ∀ T ⊆ B, K ⊆ T → K ≠ T →
    thetaJ q j G A B T ≤ thetaJ q j G A B K - 1

lemma exists_high_above (q j : ℕ) {A B Z : Finset V}
    (hex : ∃ T, LargePositive q j G A B T ∧ Z ⊆ T) :
    ∃ K, HighAbove q j G A B Z K := by
  let F := B.powerset.filter fun T => LargePositive q j G A B T ∧ Z ⊆ T
  have hF : F.Nonempty := by
    obtain ⟨T, hT, hZT⟩ := hex
    exact ⟨T, mem_filter.mpr ⟨mem_powerset.mpr hT.1, hT, hZT⟩⟩
  obtain ⟨M, hM, hm⟩ := exists_max_image F (thetaJ q j G A B) hF
  let E := F.filter fun T => thetaJ q j G A B T = thetaJ q j G A B M
  have hE : E.Nonempty := ⟨M, mem_filter.mpr ⟨hM, rfl⟩⟩
  obtain ⟨K, hK, hk⟩ := exists_max_image E Finset.card hE
  obtain ⟨hKF, hKM⟩ := mem_filter.mp hK
  obtain ⟨_, hKpos, hZK⟩ := mem_filter.mp hKF
  have hheight : ∀ T, LargePositive q j G A B T → Z ⊆ T →
      thetaJ q j G A B T ≤ thetaJ q j G A B K := by
    intro T hT hZT
    rw [hKM]
    exact hm T (mem_filter.mpr ⟨mem_powerset.mpr hT.1, hT, hZT⟩)
  refine ⟨K, hKpos, hZK, hheight, ?_⟩
  intro T hTB hKT hne
  by_cases hp : 0 < thetaJ q j G A B T
  · have hT : LargePositive q j G A B T :=
      ⟨hTB, hKpos.2.1.trans (card_le_card hKT), hp⟩
    have hθ := hheight T hT (hZK.trans hKT)
    have hnot : thetaJ q j G A B T ≠ thetaJ q j G A B K := by
      intro he
      have hTF : T ∈ F := mem_filter.mpr
        ⟨mem_powerset.mpr hTB, hT, hZK.trans hKT⟩
      have hTE : T ∈ E := mem_filter.mpr ⟨hTF, he.trans hKM⟩
      have hcard := hk T hTE
      have hlt : #K < #T := card_lt_card
        ⟨hKT, fun hTK => hne (Subset.antisymm hKT hTK)⟩
      omega
    omega
  · have hpos := hKpos.2.2
    omega

namespace Data
variable {h q j : ℕ} {A B : Finset V} (d : Data h q j G A B)
include d

lemma high_compare_union {Z K T : Finset V} (hk : HighAbove q j G A B Z K)
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
      · obtain ⟨K, hk⟩ := exists_high_above (G := G) q j hex
        have hH := hmax K hk.positive hk.contains
        have hban : N \ K ⊆ B \ K := Finset.sdiff_subset_sdiff_left K hn.subset
        have hbanCard := d.neighborhood_residual hn hk.positive.1 hk.positive.2.1 hk.positive.2.2
        have hstep : ∃ z ∈ B \ K, z ∉ N ∧
            ∀ T, LargePositive q j G A B T → insert z Z ⊆ T →
              thetaJ q j G A B T ≤ 2 * (n : ℤ) := by
          by_cases htwo : 2 ≤ thetaJ q j G A B K
          · obtain ⟨z, hzR, hzban, hcost⟩ :=
              escape h q j A B K (N \ K) d hk.positive.1 hk.positive.2.1 htwo hk.strict hban hbanCard
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

/-- One original omission is derived for every original cut simultaneously. -/
theorem common_omission (escape : PetalEscapeClaim (G := G)) :
    ∃ O : Finset V, O ⊆ B ∧ #O = j ∧
      ∀ T ⊆ B, O ⊆ T → thetaJ q j G A B T ≤ 0 := by
  obtain ⟨N, hn⟩ := d.exists_neighborhood
  have hheight : ∀ T, LargePositive q j G A B T → (∅ : Finset V) ⊆ T →
      thetaJ q j G A B T ≤ 2 * (j : ℤ) := by
    intro T hT _
    have hh := d.theta_large_le hT.1 hT.2.1
    have hj := d.parameters.j_bounds
    omega
  obtain ⟨Y, hY, _, hcY, hkill⟩ := d.select_up_to escape hn j ∅ (empty_subset _) hheight
  have hYj : #Y ≤ j := by simpa using hcY
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
end Erdos585.AllHTopTwo
