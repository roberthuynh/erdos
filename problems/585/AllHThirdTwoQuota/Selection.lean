import AllHThirdTwoQuota.Intersections

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHThirdTwoQuota
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
lemma select_up_to (escape : PetalEscapeClaim (G := G)) :
    ∀ (n : ℕ) (Z : Finset V), Z ⊆ B \ d.protectedCols →
      (∀ T, LargePositive q j G A B T → Z ⊆ T → thetaJ q j G A B T ≤ 2 * (n : ℤ)) →
      ∃ Y : Finset V, Y ⊆ B \ d.protectedCols ∧ Z ⊆ Y ∧ #Y ≤ #Z + n ∧
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
        have hban : d.protectedCols\K ⊆ B\K := sdiff_subset_sdiff_left K d.protected_subset
        have hbanCard := d.protected_residual_card hk.positive.1 hk.positive.2.1 hk.positive.2.2
        have hbanLocal : #(d.protectedCols\K)≤9*h-23 := by
          have hh := d.parameters.height
          omega
        have hstep : ∃ z ∈ B \ K, z ∉ d.protectedCols ∧
            ∀ T, LargePositive q j G A B T → insert z Z ⊆ T →
              thetaJ q j G A B T ≤ 2 * (n : ℤ) := by
          by_cases htwo : 2 ≤ thetaJ q j G A B K
          · obtain ⟨z, hzR, hzban, hcost⟩ :=
              escape h q a₀ j A B K (d.protectedCols\K) d hk.positive.1 hk.positive.2.1 htwo hk.strict hban hbanLocal
            have hzK := (mem_sdiff.mp hzR).2
            have hzN : z ∉ d.protectedCols := fun hn => hzban (mem_sdiff.mpr ⟨hn,hzK⟩)
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
            have hnum := d.parameters.numeric
            have hh := d.parameters.height_int
            have h10 : (10:ℤ)*h<q := by nlinarith [sq_nonneg (h:ℤ)]
            have hcard : #(d.protectedCols\K)<#(B\K) := by omega
            obtain ⟨z,hzR,hzban⟩ := AllHTopTwo.PetalEscape.exists_outside
              (B\K) (d.protectedCols\K) hcard
            have hzK := (mem_sdiff.mp hzR).2
            have hzN : z ∉ d.protectedCols := fun hn => hzban (mem_sdiff.mpr ⟨hn,hzK⟩)
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
        have hnew : insert z Z ⊆ B\d.protectedCols := by
          apply insert_subset_iff.mpr
          exact ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp hzR).1,hzN⟩,hZ⟩
        obtain ⟨Y, hY, hZY, hcard, hkill⟩ := ih (insert z Z) hnew hzmax
        refine ⟨Y, hY, (subset_insert z Z).trans hZY, ?_, hkill⟩
        have hc := card_insert_le z Z
        omega
      · refine ⟨Z, hZ, Subset.rfl, by omega, ?_⟩
        intro T hT hZT
        exact hex ⟨T, hT, hZT⟩

/-- The odd maximum uses one actual top escape; lower heights use two-unit gains. -/
theorem protected_common_omission (escape : PetalEscapeClaim (G := G))
    (top : TopEscapeClaim (G := G)) (hexLarge : ∃ T, LargePositive q j G A B T) :
    ∃ O : Finset V, O ⊆ B ∧ #O = j ∧ Disjoint O d.protectedCols ∧
      ∀ T ⊆ B, O ⊆ T → thetaJ q j G A B T ≤ 0 := by
  have hexY : ∃ Y : Finset V, Y ⊆ B \ d.protectedCols ∧ #Y ≤ j ∧
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
          d.select_up_to escape j ∅ (empty_subset _) hheight
        exact ⟨Y, hY, by simpa using hcY, hkill⟩
      · have hbound := d.theta_large_le hk.positive.1 hk.positive.2.1
        have hj := d.parameters.surplus_int
        have htop : thetaJ q j G A B K = 2 * (j : ℤ) + 1 := by omega
        have hban : d.protectedCols\K ⊆ B\K := sdiff_subset_sdiff_left K d.protected_subset
        have hbanCard := d.protected_residual_card hk.positive.1 hk.positive.2.1 hk.positive.2.2
        obtain ⟨z, hzR, hzban, hcost⟩ := top h q a₀ j A B K (d.protectedCols\K) d
          hk.positive.1 hk.positive.2.1 htop hk.strict hban hbanCard
        have hzK := (mem_sdiff.mp hzR).2
        have hzN : z ∉ d.protectedCols := fun hn => hzban (mem_sdiff.mpr ⟨hn,hzK⟩)
        have hZ : ({z} : Finset V) ⊆ B\d.protectedCols :=
          singleton_subset_iff.mpr (mem_sdiff.mpr ⟨(mem_sdiff.mp hzR).1,hzN⟩)
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
          d.select_up_to escape (j-1) {z} hZ hheight
        have hjpos := d.parameters.j_pos
        exact ⟨Y, hY, by simp only [card_singleton] at hcY; omega, hkill⟩
    · exact ⟨∅, empty_subset _, by simp, fun T hT _ => hex ⟨T, hT⟩⟩
  obtain ⟨Y, hY, hYj, hkill⟩ := hexY
  obtain ⟨K,hK⟩ := hexLarge
  have hB := d.allowed_card hK.1 hK.2.1 hK.2.2
  have hav : j - #Y ≤ #((B\d.protectedCols) \ Y) := by
    have hc := card_sdiff_add_card_eq_card hY
    omega
  obtain ⟨U, hU, hcU⟩ := exists_subset_card_eq hav
  have hdis : Disjoint Y U := disjoint_left.mpr fun _ hy hu => (mem_sdiff.mp (hU hu)).2 hy
  let O := Y ∪ U
  have hallowed : O ⊆ B\d.protectedCols := union_subset hY (hU.trans sdiff_subset)
  have hOBN : O⊆B := hallowed.trans sdiff_subset
  have havoid : Disjoint O d.protectedCols := disjoint_left.mpr
    (fun z hz => (mem_sdiff.mp (hallowed hz)).2)
  have hOj : #O = j := by
    rw [card_union_of_disjoint hdis]
    omega
  refine ⟨O, hOBN, hOj, havoid, ?_⟩
  intro T hT hOT
  by_cases hlarge : q - 1 ≤ #T
  · by_contra! hp
    exact hkill T ⟨hT, hlarge, hp⟩ ((subset_union_left : Y ⊆ O).trans hOT)
  · have hq := d.parameters.q_pos
    exact d.small_good (d.quota_of_disjoint hOBN hOj havoid) hOT (by omega)

/-- Quota existence is sufficient for ONE common omission; arbitrary feasible
omissions are used only when no large positive test exists. -/
theorem common_omission (escape : PetalEscapeClaim (G:=G))
    (top : TopEscapeClaim (G:=G)) (hfeasible : ∃ O, d.QuotaFeasible O) :
    ∃ O : Finset V, O⊆B ∧ #O=j ∧ ∀ T⊆B, O⊆T → thetaJ q j G A B T≤0 := by
  by_cases hex : ∃ T, LargePositive q j G A B T
  · obtain ⟨O,hOB,hOj,_,hcuts⟩ := d.protected_common_omission escape top hex
    exact ⟨O,hOB,hOj,hcuts⟩
  · obtain ⟨O,ho⟩ := hfeasible
    refine ⟨O,ho.1,ho.2.1,?_⟩
    intro T hT hOT
    by_cases hlarge : q-1≤#T
    · by_contra! hp
      exact hex ⟨T,hT,hlarge,hp⟩
    · have hq := d.parameters.q_pos
      exact d.small_good ho hOT (by omega)

end Data
end Erdos585.AllHThirdTwoQuota
