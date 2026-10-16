import L34.Core

/-! One internally derived common original omission, not a supplied selector. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.L34
open QB4 B5
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Balanced original factor from every derived complementary test. -/
lemma factor_of_nonpositive (q : ℕ) {U W : Finset V} (hcard : #W = #U)
    (hgood : ∀ T ⊆ W, thetaJ q 0 G U W T ≤ 0) : FactorOn q G U W := by
  have hcut : ∀ A ⊆ W, ∀ C ⊆ U, q * #A ≤ ec G A (U \ C) + q * #C := by
    intro A hA C hC
    have hg := hgood (W \ A) sdiff_subset
    have hm := mixed_le_theta (G := G) q (W := W) (T := W \ A)
      (sdiff_subset : U \ C ⊆ U)
    have hi : mixedTheta q G W (U \ C) (W \ A) - q =
        q * ((#A : ℤ) - #C) - (ec G A (U \ C) : ℤ) := by
      have hcA := card_sdiff_add_card_eq_card hA
      have hcC := card_sdiff_add_card_eq_card hC
      have he := ec_sdiff_add_right (G := G) hA (U \ C)
      have hcomm := ec_comm (G := G) (U \ C) A
      zify at hcard hcA hcC he hcomm
      rw [mixedTheta, row_sum]
      nlinarith
    have hz : (q : ℤ) * #A ≤ (ec G A (U \ C) : ℤ) + q * #C := by
      unfold thetaJ at hg
      norm_num at hg
      nlinarith
    exact_mod_cast hz
  exact FactorOn.swap (B5Factor.exists_target_factor (k := q) W U hcard hcut)

namespace Input
variable {q : ℕ} {U W : Finset V}

lemma balanced_factor (hq : 6 ≤ q) (h : Input q 0 G U W) : FactorOn q G U W := by
  apply factor_of_nonpositive q (by simpa using h.card)
  intro T hT
  by_contra! hp
  by_cases hne : T.Nonempty
  · have hh := (h.positive_shape hq hT hne hp).1
    omega
  · have ht : T = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hs : ∑ a ∈ U, max 0 (row q G W ∅ a) = 0 := by
      refine sum_eq_zero fun a ha => max_eq_left ?_
      have hd := h.minU a ha
      have he : dg G (∅ : Finset V) a = 0 := by simp [dg]
      unfold row
      rw [he]
      omega
    subst T
    simp only [thetaJ, theta, card_empty, Nat.cast_zero, mul_zero, sub_zero, hs,
      add_zero, sub_self] at hp
    omega

lemma deficient_exists (hq : 6 ≤ q) (h : Input q 1 G U W) :
    ∃ a ∈ U, (dg G W a : ℤ) < 2 * (q : ℤ) - 2 := by
  have hd := h.deficient
  norm_num at hd
  by_contra! hall
  have hz : deficiency (2 * (q : ℤ) - 2) G W U ≤ 0 :=
    sum_nonpos fun a ha => sub_nonpos.mpr (hall a ha)
  omega

lemma deficient_in_canonical (hq : 6 ≤ q) (h : Input q 1 G U W)
    {a : V} (ha : a ∈ U) (had : (dg G W a : ℤ) < 2 * (q : ℤ) - 2)
    {T : Finset V} (hT : T ⊆ W) (hne : T.Nonempty) (hp : 0 < theta q G U W T) :
    a ∈ canonical q G U W T := by
  have hs := h.positive_shape hq hT hne (by simpa only [thetaJ_one] using hp)
  let C := canonical q G U W T
  have hC : C ⊆ U := canonical_subset q U W T
  have hdefC : deficiency (2 * (q : ℤ) - 2) G W C = (q : ℤ) - 4 := hs.2.2.2.2.2.1
  have hdefU := h.deficient
  norm_num at hdefU
  have hr : deficiency (2 * (q : ℤ) - 2) G W (U \ C) = 0 := by
    have hc := card_sdiff_add_card_eq_card hC
    have he := ec_sdiff_add_left (G := G) hC W
    have h1 := deficiency_eq (G := G) (2 * (q : ℤ) - 2) W (U \ C)
    have h2 := deficiency_eq (G := G) (2 * (q : ℤ) - 2) W C
    have h3 := deficiency_eq (G := G) (2 * (q : ℤ) - 2) W U
    zify at hc he
    nlinarith
  by_contra haa
  have har : a ∈ U \ C := mem_sdiff.mpr ⟨ha, haa⟩
  have hle : 2 * (q : ℤ) - 2 - dg G W a ≤
      deficiency (2 * (q : ℤ) - 2) G W (U \ C) := by
    have hh := sum_le_sum_of_subset_of_nonneg (singleton_subset_iff.mpr har)
      (fun b hb _ => sub_nonneg.mpr (h.capU_int hq (mem_sdiff.mp hb).1))
    simpa only [sum_singleton, deficiency] using hh
  omega

lemma positive_uses_neighbors (hq : 6 ≤ q) (h : Input q 1 G U W)
    {a : V} (ha : a ∈ U) (had : (dg G W a : ℤ) < 2 * (q : ℤ) - 2)
    {T : Finset V} (hT : T ⊆ W) (hne : T.Nonempty) (hp : 0 < theta q G U W T) :
    q - 1 ≤ dg G T a := by
  have hs := h.positive_shape hq hT hne (by simpa only [thetaJ_one] using hp)
  have hac := h.deficient_in_canonical hq ha had hT hne hp
  have hC : canonical q G U W T ⊆ U := canonical_subset q U W T
  have he := card_erase_of_mem hac
  have hcc := card_le_card hC
  have hsp := h.sparse ((canonical q G U W T).erase a)
    ((erase_subset _ _).trans hC) T hT (by omega) (by omega)
  have hid := potential_erase_left (G := G) (2 * (q : ℤ) - 2) hac T
  have hgp := hs.2.2.2.2.2.2
  rw [hid, hgp] at hsp
  omega

lemma theta_nonempty_le_one (hq : 6 ≤ q) (h : Input q 1 G U W) {T : Finset V}
    (hT : T ⊆ W) (hne : T.Nonempty) : theta q G U W T ≤ 1 := by
  by_cases hp : 0 < theta q G U W T
  · have hh := (h.positive_shape hq hT hne (by simpa only [thetaJ_one] using hp)).2.2.2.1
    simpa only [thetaJ_one] using hh.le
  · omega

lemma positive_subset_max (hq : 6 ≤ q) (h : Input q 1 G U W)
    {M T : Finset V} (hM : IsMaxPositive q G U W M)
    (hT : T ⊆ W) (hne : T.Nonempty) (hp : 0 < theta q G U W T) : T ⊆ M := by
  by_contra hnot
  have hMW := hM.1
  have hmne := hM.2.1
  have hmpos := hM.2.2.1
  have hU : M ∪ T ⊆ W := union_subset hMW hT
  have hneU : M ≠ M ∪ T := by
    intro heq
    apply hnot
    simpa only [← heq] using (subset_union_right : T ⊆ M ∪ T)
  have hthetaU := hM.2.2.2 (M ∪ T) hU subset_union_left hneU
  have hmt : theta q G U W M = 1 := by
    simpa only [thetaJ_one] using
      (h.positive_shape hq hMW hmne (by simpa only [thetaJ_one] using hmpos)).2.2.2.1
  have htt : theta q G U W T = 1 := by
    simpa only [thetaJ_one] using
      (h.positive_shape hq hT hne (by simpa only [thetaJ_one] using hp)).2.2.2.1
  have hdis : Disjoint M T := by
    refine disjoint_left.mpr fun a ham hat => ?_
    have hi : (M ∩ T).Nonempty := ⟨a, mem_inter.mpr ⟨ham, hat⟩⟩
    have hh := h.theta_nonempty_le_one hq (inter_subset_left.trans hMW) hi
    have hsuper := theta_supermod (G := G) q U W M T
    omega
  obtain ⟨a, ha, had⟩ := h.deficient_exists hq
  have hm := h.positive_uses_neighbors hq ha had hMW hmne hmpos
  have ht := h.positive_uses_neighbors hq ha had hT hne hp
  have hd := dg_union_of_disjoint (G := G) hdis a
  have hc := dg_mono (G := G) hU a
  omega

/-- The original common omission is an output of the proof. -/
theorem uncovered (hq : 6 ≤ q) (h : Input q 1 G U W) :
    ∃ w ∈ W, ∀ T ⊆ W, w ∈ T → theta q G U W T ≤ 0 := by
  have hwne : W.Nonempty := card_pos.mp (by have hc := h.card; omega)
  by_cases hex : ∃ T ⊆ W, T.Nonempty ∧ 0 < theta q G U W T
  · obtain ⟨T, hT, htne, htpos⟩ := hex
    obtain ⟨M, hM⟩ := exists_max_positive q hT htne htpos
    have hs := h.positive_shape hq hM.1 hM.2.1
      (by simpa only [thetaJ_one] using hM.2.2.1)
    have hout : ∃ w ∈ W, w ∉ M := by
      by_contra! hcover
      have hcard := card_le_card hcover
      omega
    obtain ⟨w, hw, hwM⟩ := hout
    refine ⟨w, hw, fun S hS hwS => ?_⟩
    by_contra! hsp
    exact hwM (h.positive_subset_max hq hM hS ⟨w, hwS⟩ hsp hwS)
  · obtain ⟨w, hw⟩ := hwne
    refine ⟨w, hw, fun T hT hwT => ?_⟩
    by_contra! hp
    exact hex ⟨T, hT, ⟨w, hwT⟩, hp⟩

theorem surplus_factor (hq : 6 ≤ q) (h : Input q 1 G U W) :
    ∃ w ∈ W, FactorOn q G U (W.erase w) := by
  obtain ⟨w, hw, hgood⟩ := h.uncovered hq
  exact ⟨w, hw, factor_of_uncovered q h.card hw hgood⟩

end Input
end Erdos585.L34
