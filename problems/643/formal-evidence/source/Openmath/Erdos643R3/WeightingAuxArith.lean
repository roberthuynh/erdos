import Mathlib



set_option autoImplicit false

namespace Erdos643R3
namespace WeightingAux

/-! ## Sums of reciprocals -/

theorem inv_two_mul_le {s M : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ M) :
    1 / (2 * (M : ℚ)) ≤ 1 / (2 * (s : ℚ)) := by
  apply one_div_le_one_div_of_le
  · have : (1 : ℚ) ≤ (s : ℚ) := by exact_mod_cast h1
    linarith
  · have : (s : ℚ) ≤ (M : ℚ) := by exact_mod_cast h2
    linarith

/-- If `1 ≤ s z ≤ M` on `Z`, then `Σ_{z ∈ Z} 1/(2 s z) ≥ |Z| · 1/(2M)`. -/
theorem sum_ge_of_le {ι : Type*} (Z : Finset ι) (s : ι → ℕ) (M : ℕ)
    (h : ∀ z ∈ Z, 1 ≤ s z ∧ s z ≤ M) :
    (Z.card : ℚ) * (1 / (2 * (M : ℚ))) ≤ ∑ z ∈ Z, 1 / (2 * (s z : ℚ)) := by
  rw [← nsmul_eq_mul]
  apply Finset.card_nsmul_le_sum
  intro z hz
  exact inv_two_mul_le (h z hz).1 (h z hz).2

/-- If `1 ≤ s z ≤ M` on `Z` and `s z ≤ M1` on `U ⊆ Z`, then
`Σ_{z ∈ Z} 1/(2 s z) ≥ |Z|/(2M) + |U| (1/(2 M1) - 1/(2M))`. -/
theorem sum_ge_split {ι : Type*} [DecidableEq ι] (Z U : Finset ι) (hU : U ⊆ Z) (s : ι → ℕ)
    (M M1 : ℕ) (h : ∀ z ∈ Z, 1 ≤ s z ∧ s z ≤ M) (h1 : ∀ z ∈ U, s z ≤ M1) :
    (Z.card : ℚ) * (1 / (2 * (M : ℚ))) + (U.card : ℚ) * (1 / (2 * (M1 : ℚ)) - 1 / (2 * (M : ℚ))) ≤
      ∑ z ∈ Z, 1 / (2 * (s z : ℚ)) := by
  have e := Finset.sum_sdiff hU (f := fun z => 1 / (2 * (s z : ℚ)))
  have hA := sum_ge_of_le (Z \ U) s M (fun z hz => h z (Finset.sdiff_subset hz))
  have hB := sum_ge_of_le U s M1 (fun z hz => ⟨(h z (hU hz)).1, h1 z hz⟩)
  have hc : ((Z \ U).card : ℚ) = (Z.card : ℚ) - (U.card : ℚ) := by
    rw [Finset.card_sdiff_of_subset hU, Nat.cast_sub (Finset.card_le_card hU)]
  rw [hc] at hA
  have key : (Z.card : ℚ) * (1 / (2 * (M : ℚ))) +
      (U.card : ℚ) * (1 / (2 * (M1 : ℚ)) - 1 / (2 * (M : ℚ))) =
      ((Z.card : ℚ) - (U.card : ℚ)) * (1 / (2 * (M : ℚ))) + (U.card : ℚ) * (1 / (2 * (M1 : ℚ))) := by
    ring
  linarith

/-! ## Case A: `k2 ≤ 3` -/

theorem hA_bound (k : ℕ) (h1 : 1 ≤ k) (h3 : k ≤ 3) :
    5 / 12 ≤ ((k : ℚ) - 1) * (1 / 6) + (1 / (k : ℚ)) / 2 := by
  obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  all_goals norm_num

theorem hA_bound' (k : ℕ) (h1 : 1 ≤ k) (h3 : k ≤ 3) (h2 : k ≠ 2) :
    1 / 2 ≤ ((k : ℚ) - 1) * (1 / 6) + (1 / (k : ℚ)) / 2 := by
  obtain rfl | rfl : k = 1 ∨ k = 3 := by omega
  all_goals norm_num

/-- Case A with `k3 ≤ 3`, `(k1,k2,k3) ≠ (2,2,2)`: every option has `s ≤ 3`. -/
theorem caseA_low (k1 k2 k3 : ℕ) (h1 : 1 ≤ k1) (h12 : k1 ≤ k2) (h23 : k2 ≤ k3) (h3 : k3 ≤ 3)
    (hn : ¬ (k1 = 2 ∧ k2 = 2 ∧ k3 = 2)) (tc ta tb : ℚ)
    (htc : ((k1 : ℚ) - 1) * (1 / 6) ≤ tc) (hta : ((k2 : ℚ) - 1) * (1 / 6) ≤ ta)
    (htb : ((k3 : ℚ) - 1) * (1 / 6) ≤ tb) :
    4 / 3 ≤ tc + ta + tb + (1 / (k1 : ℚ) + 1 / (k2 : ℚ) + 1 / (k3 : ℚ)) / 2 := by
  have b1 := hA_bound k1 h1 (by omega)
  have b2 := hA_bound k2 (by omega) (by omega)
  have b3 := hA_bound k3 (by omega) h3
  by_cases e1 : k1 = 2
  · by_cases e2 : k2 = 2
    · have e3 : k3 ≠ 2 := fun e3 => hn ⟨e1, e2, e3⟩
      have b3' := hA_bound' k3 (by omega) h3 e3
      linarith
    · have b2' := hA_bound' k2 (by omega) (by omega) e2
      linarith
  · have b1' := hA_bound' k1 h1 (by omega) e1
    linarith

/-- The Case A table for `4 ≤ k3 ≤ 8` (draft rows with `k3 ≥ 4`), checked case by case. -/
theorem caseA_mid_closed (k1 k2 k3 : ℕ) (h1 : 1 ≤ k1) (h12 : k1 ≤ k2) (h2 : k2 ≤ 3)
    (h4 : 4 ≤ k3) (h8 : k3 ≤ 8) :
    4 / 3 ≤ ((k1 : ℚ) - 1) * (1 / (2 * (k3 : ℚ))) + ((k2 : ℚ) - 1) * (1 / (2 * (k3 : ℚ))) +
      ((k3 : ℚ) - 1) * (1 / 6) + (1 / (k1 : ℚ) + 1 / (k2 : ℚ) + 1 / (k3 : ℚ)) / 2 := by
  have hk1 : k1 ≤ 3 := by omega
  interval_cases k1 <;> interval_cases k2 <;> interval_cases k3 <;> norm_num

/-- Case A with `4 ≤ k3 ≤ 8`: options through `ab`, `bc` have `s ≤ k3`, through `ca` `s ≤ 3`. -/
theorem caseA_mid (k1 k2 k3 : ℕ) (h1 : 1 ≤ k1) (h12 : k1 ≤ k2) (h2 : k2 ≤ 3)
    (h4 : 4 ≤ k3) (h8 : k3 ≤ 8) (tc ta tb : ℚ)
    (htc : ((k1 : ℚ) - 1) * (1 / (2 * (k3 : ℚ))) ≤ tc)
    (hta : ((k2 : ℚ) - 1) * (1 / (2 * (k3 : ℚ))) ≤ ta)
    (htb : ((k3 : ℚ) - 1) * (1 / 6) ≤ tb) :
    4 / 3 ≤ tc + ta + tb + (1 / (k1 : ℚ) + 1 / (k2 : ℚ) + 1 / (k3 : ℚ)) / 2 := by
  have := caseA_mid_closed k1 k2 k3 h1 h12 h2 h4 h8
  linarith

/-- Case A with `k3 ≥ 9`: the options through `ca` alone give `τ ≥ (k3 - 1)/6 ≥ 4/3`. -/
theorem caseA_tail (k1 k2 k3 : ℕ) (h9 : 9 ≤ k3) (tc ta tb : ℚ)
    (htc : 0 ≤ tc) (hta : 0 ≤ ta) (htb : ((k3 : ℚ) - 1) * (1 / 6) ≤ tb) :
    4 / 3 ≤ tc + ta + tb + (1 / (k1 : ℚ) + 1 / (k2 : ℚ) + 1 / (k3 : ℚ)) / 2 := by
  have hk3 : (9 : ℚ) ≤ k3 := by exact_mod_cast h9
  have p1 : 0 ≤ 1 / (k1 : ℚ) := by positivity
  have p2 : 0 ≤ 1 / (k2 : ℚ) := by positivity
  have p3 : 0 ≤ 1 / (k3 : ℚ) := by positivity
  linarith

/-- Lemma 5 arithmetic: three options with `1 ≤ s ≤ 3`, one of the first two with `s ≤ 2`. -/
theorem light_arith (s1 s2 s3 : ℕ) (h1 : 1 ≤ s1 ∧ s1 ≤ 3) (h2 : 1 ≤ s2 ∧ s2 ≤ 3)
    (h3 : 1 ≤ s3 ∧ s3 ≤ 3) (h : s1 ≤ 2 ∨ s2 ≤ 2) :
    7 / 12 ≤ 1 / (2 * (s1 : ℚ)) + 1 / (2 * (s2 : ℚ)) + 1 / (2 * (s3 : ℚ)) := by
  have e2 : (1 : ℚ) / (2 * ((2 : ℕ) : ℚ)) = 1 / 4 := by norm_num
  have e3 : (1 : ℚ) / (2 * ((3 : ℕ) : ℚ)) = 1 / 6 := by norm_num
  have c1 := inv_two_mul_le h1.1 h1.2
  have c2 := inv_two_mul_le h2.1 h2.2
  have c3 := inv_two_mul_le h3.1 h3.2
  rcases h with h | h
  · have d1 := inv_two_mul_le h1.1 h
    linarith
  · have d2 := inv_two_mul_le h2.1 h
    linarith

/-- Type `(2,2,2)`: `σ/2 = 3/4`, so `τ ≥ 7/12` gives `τ + σ/2 ≥ 4/3`. -/
theorem case222 (k1 k2 k3 : ℕ) (e1 : k1 = 2) (e2 : k2 = 2) (e3 : k3 = 2) (tc ta tb : ℚ)
    (h : 7 / 12 ≤ tc + ta + tb) :
    4 / 3 ≤ tc + ta + tb + (1 / (k1 : ℚ) + 1 / (k2 : ℚ) + 1 / (k3 : ℚ)) / 2 := by
  subst e1 e2 e3
  have e : (1 : ℚ) / ((2 : ℕ) : ℚ) = 1 / 2 := by norm_num
  rw [e]
  linarith

/-! ## Case B: `k2 ≥ 4` -/

/-- Case B1 (`ρ = k1/k2 ≥ 7/9`): `τ + σ/2 ≥ (1+ρ)/(2t) + t/2 ≥ √(1+ρ) ≥ 4/3`, with AM–GM replaced by
`(4 k2 - 3 k3)² ≥ 0`. -/
theorem B1_arith (k1 k2 k3 : ℕ) (h1 : 1 ≤ k1) (h12 : k1 ≤ k2) (h23 : k2 ≤ k3) (h2 : 4 ≤ k2)
    (hρ : 7 * k2 ≤ 9 * k1) (tc ta tb : ℚ)
    (htc : ((k1 : ℚ) - 1) * (1 / (2 * (k3 : ℚ))) ≤ tc)
    (hta : ((k2 : ℚ) - 1) * (1 / (2 * (k3 : ℚ))) ≤ ta)
    (htb : ((k3 : ℚ) - 1) * (1 / (2 * (k2 : ℚ))) ≤ tb) :
    4 / 3 ≤ tc + ta + tb + (1 / (k1 : ℚ) + 1 / (k2 : ℚ) + 1 / (k3 : ℚ)) / 2 := by
  have K1 : (1 : ℚ) ≤ k1 := by exact_mod_cast h1
  have K12 : (k1 : ℚ) ≤ k2 := by exact_mod_cast h12
  have K23 : (k2 : ℚ) ≤ k3 := by exact_mod_cast h23
  have K2 : (4 : ℚ) ≤ k2 := by exact_mod_cast h2
  have Kρ : 7 * (k2 : ℚ) ≤ 9 * k1 := by exact_mod_cast hρ
  have p2 : (0 : ℚ) < k2 := by linarith
  have p3 : (0 : ℚ) < k3 := by linarith
  have hmain : 4 / 3 ≤ ((k1 : ℚ) + k2) / (2 * k3) + (k3 : ℚ) / (2 * k2) := by
    rw [div_add_div _ _ (by linarith : (0 : ℚ) < 2 * k3).ne' (by linarith : (0 : ℚ) < 2 * k2).ne',
      le_div_iff₀ (mul_pos (by linarith) (by linarith))]
    nlinarith [sq_nonneg (4 * (k2 : ℚ) - 3 * k3), mul_nonneg (sub_nonneg.mpr Kρ) p2.le]
  have h13 : 1 / (2 * (k3 : ℚ)) ≤ 1 / (2 * (k1 : ℚ)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have e : ((k1 : ℚ) - 1) * (1 / (2 * (k3 : ℚ))) + ((k2 : ℚ) - 1) * (1 / (2 * (k3 : ℚ))) +
      ((k3 : ℚ) - 1) * (1 / (2 * (k2 : ℚ))) + (1 / (k1 : ℚ) + 1 / (k2 : ℚ) + 1 / (k3 : ℚ)) / 2 =
      ((k1 : ℚ) + k2) / (2 * k3) + (k3 : ℚ) / (2 * k2) +
        (1 / (2 * (k1 : ℚ)) - 1 / (2 * (k3 : ℚ))) := by
    ring
  linarith

/-- Case B2, the key inequality `g ≥ 1/3 - 1/(2 k1)` with `g = (k1 - 1)/(2 max(3, 1 + μ)) + μ d`,
`d = 1/(2 max(3, k1)) - 1/(2 k2)`. -/
theorem B2_g (k1 k2 μ : ℕ) (h1 : 1 ≤ k1) (h2 : 4 ≤ k2) (hρ : 9 * k1 < 7 * k2) :
    1 / 3 - 1 / (2 * (k1 : ℚ)) ≤
      ((k1 : ℚ) - 1) * (1 / (2 * ((max 3 (1 + μ) : ℕ) : ℚ))) +
        (μ : ℚ) * (1 / (2 * ((max 3 k1 : ℕ) : ℚ)) - 1 / (2 * (k2 : ℚ))) := by
  have K1 : (1 : ℚ) ≤ k1 := by exact_mod_cast h1
  have K2 : (4 : ℚ) ≤ k2 := by exact_mod_cast h2
  have Kρ : 9 * (k1 : ℚ) < 7 * k2 := by exact_mod_cast hρ
  have hμ0 : (0 : ℚ) ≤ μ := Nat.cast_nonneg μ
  have hk1pos : (0 : ℚ) < 2 * (k1 : ℚ) := by linarith
  have hinv1 : 0 ≤ 1 / (2 * (k1 : ℚ)) := le_of_lt (one_div_pos.mpr hk1pos)
  have hM1le : max 3 k1 ≤ k2 := by omega
  have hM1pos : 0 < max 3 k1 := by omega
  have hd0 : 0 ≤ 1 / (2 * ((max 3 k1 : ℕ) : ℚ)) - 1 / (2 * (k2 : ℚ)) := by
    have hMq : (0 : ℚ) < ((max 3 k1 : ℕ) : ℚ) := by exact_mod_cast hM1pos
    have hMle : ((max 3 k1 : ℕ) : ℚ) ≤ (k2 : ℚ) := by exact_mod_cast hM1le
    have hle : 1 / (2 * (k2 : ℚ)) ≤ 1 / (2 * ((max 3 k1 : ℕ) : ℚ)) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  have hk2inv : 1 / (2 * (k2 : ℚ)) ≤ 1 / 8 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hdsmall : k1 ≤ 3 → 1 / 24 ≤ 1 / (2 * ((max 3 k1 : ℕ) : ℚ)) - 1 / (2 * (k2 : ℚ)) := by
    intro hk
    have hm : ((max 3 k1 : ℕ) : ℚ) = 3 := by
      rw [show max 3 k1 = 3 by omega]; norm_num
    rw [hm]
    have e6 : (1 : ℚ) / (2 * 3) = 1 / 6 := by norm_num
    rw [e6]
    linarith
  have hdbig : 4 ≤ k1 → 1 / (9 * (k1 : ℚ)) ≤
      1 / (2 * ((max 3 k1 : ℕ) : ℚ)) - 1 / (2 * (k2 : ℚ)) := by
    intro hk
    have hm : ((max 3 k1 : ℕ) : ℚ) = (k1 : ℚ) := by
      rw [show max 3 k1 = k1 by omega]
    rw [hm]
    have hpos2 : (0 : ℚ) < 2 * (k2 : ℚ) := by linarith
    have hpos18 : (0 : ℚ) < 18 * (k1 : ℚ) := by linarith
    have h7 : 1 / (2 * (k2 : ℚ)) ≤ 7 / (18 * (k1 : ℚ)) := by
      rw [div_le_div_iff₀ hpos2 hpos18]
      linarith
    have e : 1 / (2 * (k1 : ℚ)) - 7 / (18 * (k1 : ℚ)) = 1 / (9 * (k1 : ℚ)) := by
      ring
    linarith
  generalize hD : (1 / (2 * ((max 3 k1 : ℕ) : ℚ)) - 1 / (2 * (k2 : ℚ))) = d at hd0 hdsmall hdbig ⊢
  have hμd : 0 ≤ (μ : ℚ) * d := mul_nonneg hμ0 hd0
  rcases Nat.lt_or_ge μ 3 with hμ | hμ
  · -- `μ ≤ 2`: every option through `ab` has `s ≤ 3`
    have hy : ((max 3 (1 + μ) : ℕ) : ℚ) = 3 := by
      rw [show max 3 (1 + μ) = 3 by omega]; norm_num
    rw [hy]
    rcases Nat.lt_or_ge k1 3 with hk | hk
    · rcases (show k1 = 1 ∨ k1 = 2 by omega) with e | e
      · have hK : (k1 : ℚ) = 1 := by rw [e]; norm_num
        have hnum : 1 / 3 - 1 / (2 * (k1 : ℚ)) ≤ ((k1 : ℚ) - 1) * (1 / (2 * 3)) := by
          rw [hK]; norm_num
        linarith
      · have hK : (k1 : ℚ) = 2 := by rw [e]; norm_num
        have hnum : 1 / 3 - 1 / (2 * (k1 : ℚ)) ≤ ((k1 : ℚ) - 1) * (1 / (2 * 3)) := by
          rw [hK]; norm_num
        linarith
    · have K3 : (3 : ℚ) ≤ k1 := by exact_mod_cast hk
      have hnum : ((k1 : ℚ) - 1) * (1 / (2 * 3)) = ((k1 : ℚ) - 1) / 6 := by ring
      linarith
  · -- `μ ≥ 3`: options through `ab` have `s ≤ 1 + μ`
    have hy : ((max 3 (1 + μ) : ℕ) : ℚ) = 1 + (μ : ℚ) := by
      rw [show max 3 (1 + μ) = 1 + μ by omega, Nat.cast_add, Nat.cast_one]
    rw [hy]
    have hμ3 : (3 : ℚ) ≤ μ := by exact_mod_cast hμ
    have hypos : (0 : ℚ) < 2 * (1 + (μ : ℚ)) := by linarith
    have hfirst : 0 ≤ ((k1 : ℚ) - 1) * (1 / (2 * (1 + (μ : ℚ)))) :=
      mul_nonneg (by linarith) (le_of_lt (one_div_pos.mpr hypos))
    rcases Nat.lt_or_ge k1 4 with hk | hk
    · have hd24 := hdsmall (by omega)
      rcases (show k1 = 1 ∨ k1 = 2 ∨ k1 = 3 by omega) with e | e | e
      · have hK : (k1 : ℚ) = 1 := by rw [e]; norm_num
        have hnum : 1 / 3 - 1 / (2 * (k1 : ℚ)) ≤ 0 := by rw [hK]; norm_num
        linarith
      · have hK : (k1 : ℚ) = 2 := by rw [e]; norm_num
        have hnum : 1 / 3 - 1 / (2 * (k1 : ℚ)) = 1 / 12 := by rw [hK]; norm_num
        have hmu : 3 * (1 / 24 : ℚ) ≤ (μ : ℚ) * d := mul_le_mul hμ3 hd24 (by norm_num) hμ0
        linarith
      · have hK : (k1 : ℚ) = 3 := by rw [e]; norm_num
        have hnum : 1 / 3 - 1 / (2 * (k1 : ℚ)) = 1 / 6 := by rw [hK]; norm_num
        rcases Nat.lt_or_ge μ 4 with hμ4 | hμ4
        · have hμe : (μ : ℚ) = 3 := by exact_mod_cast (show μ = 3 by omega)
          have hval : ((k1 : ℚ) - 1) * (1 / (2 * (1 + (μ : ℚ)))) = 1 / 4 := by
            rw [hK, hμe]; norm_num
          linarith
        · have hμ4' : (4 : ℚ) ≤ μ := by exact_mod_cast hμ4
          have hmu : 4 * (1 / 24 : ℚ) ≤ (μ : ℚ) * d := mul_le_mul hμ4' hd24 (by norm_num) hμ0
          linarith
    · -- `k1 ≥ 4`: `d ≥ 1/(9 k1)` and `(k1-1)/(2y) + (y-1)/(9 k1) ≥ 1/3` for `y = 1 + μ`
      have hd9 := hdbig hk
      have K4 : (4 : ℚ) ≤ k1 := by exact_mod_cast hk
      have hmu : (μ : ℚ) * (1 / (9 * (k1 : ℚ))) ≤ (μ : ℚ) * d :=
        mul_le_mul_of_nonneg_left hd9 hμ0
      have hkey : 1 / 3 ≤ ((k1 : ℚ) - 1) * (1 / (2 * (1 + (μ : ℚ)))) +
          (μ : ℚ) * (1 / (9 * (k1 : ℚ))) := by
        have e : ((k1 : ℚ) - 1) * (1 / (2 * (1 + (μ : ℚ)))) + (μ : ℚ) * (1 / (9 * (k1 : ℚ))) =
            ((k1 : ℚ) - 1) / (2 * (1 + (μ : ℚ))) + (μ : ℚ) / (9 * (k1 : ℚ)) := by ring
        rw [e, div_add_div _ _ hypos.ne' (by linarith : (0 : ℚ) < 9 * (k1 : ℚ)).ne',
          le_div_iff₀ (mul_pos hypos (by linarith))]
        nlinarith [sq_nonneg (2 * (μ : ℚ) - 3 * (k1 : ℚ) + 1),
          mul_nonneg (by linarith : (0 : ℚ) ≤ (k1 : ℚ) - 4) (by linarith : (0 : ℚ) ≤ 9 * (k1 : ℚ) + 12)]
      linarith

/-- Case B2 (`ρ < 7/9`): combines `(3.3)` (`base + σ/2 ≥ 1 + 1/(2 k1)`) with `B2_g`; `nU = |U|`, `nV = |V|`. -/
theorem B2_arith (k1 k2 k3 nU nV : ℕ) (h1 : 1 ≤ k1) (h2 : 4 ≤ k2) (h23 : k2 ≤ k3)
    (hρ : 9 * k1 < 7 * k2) (tc ta tb : ℚ)
    (htc : ((k1 : ℚ) - 1) * (1 / (2 * ((max 3 (1 + max nU nV) : ℕ) : ℚ))) ≤ tc)
    (htb : ((k3 : ℚ) - 1) * (1 / (2 * (k2 : ℚ))) +
        (nU : ℚ) * (1 / (2 * ((max 3 k1 : ℕ) : ℚ)) - 1 / (2 * (k2 : ℚ))) ≤ tb)
    (hta : ((k2 : ℚ) - 1) * (1 / (2 * (k3 : ℚ))) +
        (nV : ℚ) * (1 / (2 * ((max 3 k1 : ℕ) : ℚ)) - 1 / (2 * (k3 : ℚ))) ≤ ta) :
    4 / 3 ≤ tc + ta + tb + (1 / (k1 : ℚ) + 1 / (k2 : ℚ) + 1 / (k3 : ℚ)) / 2 := by
  have K2 : (4 : ℚ) ≤ k2 := by exact_mod_cast h2
  have K23 : (k2 : ℚ) ≤ k3 := by exact_mod_cast h23
  have amgm : 1 ≤ (k3 : ℚ) / (2 * k2) + (k2 : ℚ) / (2 * k3) := by
    rw [div_add_div _ _ (by linarith : (0 : ℚ) < 2 * k2).ne' (by linarith : (0 : ℚ) < 2 * k3).ne',
      le_div_iff₀ (mul_pos (by linarith) (by linarith))]
    nlinarith [sq_nonneg ((k3 : ℚ) - k2)]
  have ebase : ((k3 : ℚ) - 1) * (1 / (2 * (k2 : ℚ))) + ((k2 : ℚ) - 1) * (1 / (2 * (k3 : ℚ))) +
      (1 / (k1 : ℚ) + 1 / (k2 : ℚ) + 1 / (k3 : ℚ)) / 2 =
      (k3 : ℚ) / (2 * k2) + (k2 : ℚ) / (2 * k3) + 1 / (2 * (k1 : ℚ)) := by ring
  have hM1le : max 3 k1 ≤ k2 := by omega
  have hM1pos : 0 < max 3 k1 := by omega
  have hMq : (0 : ℚ) < ((max 3 k1 : ℕ) : ℚ) := by exact_mod_cast hM1pos
  have hMle : ((max 3 k1 : ℕ) : ℚ) ≤ (k2 : ℚ) := by exact_mod_cast hM1le
  have hd1 : 0 ≤ 1 / (2 * ((max 3 k1 : ℕ) : ℚ)) - 1 / (2 * (k2 : ℚ)) := by
    have hle : 1 / (2 * (k2 : ℚ)) ≤ 1 / (2 * ((max 3 k1 : ℕ) : ℚ)) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  have hd21 : 1 / (2 * (k3 : ℚ)) ≤ 1 / (2 * (k2 : ℚ)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hμ : ((max nU nV : ℕ) : ℚ) ≤ (nU : ℚ) + (nV : ℚ) := by
    have : max nU nV ≤ nU + nV := by omega
    exact_mod_cast this
  have hnV : (0 : ℚ) ≤ nV := Nat.cast_nonneg nV
  have hUV : ((max nU nV : ℕ) : ℚ) * (1 / (2 * ((max 3 k1 : ℕ) : ℚ)) - 1 / (2 * (k2 : ℚ))) ≤
      (nU : ℚ) * (1 / (2 * ((max 3 k1 : ℕ) : ℚ)) - 1 / (2 * (k2 : ℚ))) +
        (nV : ℚ) * (1 / (2 * ((max 3 k1 : ℕ) : ℚ)) - 1 / (2 * (k3 : ℚ))) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hμ) hd1, mul_nonneg hnV (sub_nonneg.mpr hd21)]
  have hg := B2_g k1 k2 (max nU nV) h1 h2 hρ
  linarith

end WeightingAux
end Erdos643R3
