import Mathlib

/-! Actual finite threshold layers derive a second moment from density. -/
namespace Erdos642.CampaignFe72210bContinuation3.CodegreeLayerCake

variable {W : Type*}

def threshold (S : Finset W) (c : W → ℕ) (j : ℕ) : Finset W :=
  S.filter (fun w => j ≤ c w)
noncomputable def mass (S : Finset W) (c : W → ℕ) : ℝ := ∑ w ∈ S, (c w : ℝ)
noncomputable def weight (j : ℕ) : ℝ := 2 * (j : ℝ) - 1
noncomputable def low (Δ : ℕ) (a : ℝ) : Finset ℕ :=
  (Finset.Icc 1 Δ).filter (fun j => (j : ℝ) < 2*a)
noncomputable def high (Δ : ℕ) (a : ℝ) : Finset ℕ :=
  (Finset.Icc 1 Δ).filter (fun j => 2*a ≤ (j : ℝ))

 theorem mass_nonneg (S : Finset W) (c : W → ℕ) : 0 ≤ mass S c := by
  exact Finset.sum_nonneg fun w _ => Nat.cast_nonneg _

 theorem odd_sum_Icc (n : ℕ) : (∑ j ∈ Finset.Icc 1 n, weight j) = (n : ℝ)^2 := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1), ih]
    simp only [weight, Nat.cast_add, Nat.cast_one]
    ring

 theorem truncated_odd_sum (Δ n : ℕ) (hn : n ≤ Δ) :
    (∑ j ∈ Finset.Icc 1 Δ, if j ≤ n then weight j else 0) = (n : ℝ)^2 := by
  have he : (Finset.Icc 1 Δ).filter (fun j => j ≤ n) = Finset.Icc 1 n := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [← Finset.sum_filter, he, odd_sum_Icc]

/-- Exact finite layer cake, including zero codegrees and empty layers. -/
 theorem layer_cake (S : Finset W) (c : W → ℕ) (Δ : ℕ) (hc : ∀ w ∈ S, c w ≤ Δ) :
    (∑ w ∈ S, (c w : ℝ)^2) =
      ∑ j ∈ Finset.Icc 1 Δ, weight j * ((threshold S c j).card : ℝ) := by
  calc
    _ = ∑ w ∈ S, ∑ j ∈ Finset.Icc 1 Δ, if j ≤ c w then weight j else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      exact (truncated_odd_sum Δ (c w) (hc w hw)).symm
    _ = ∑ j ∈ Finset.Icc 1 Δ, ∑ w ∈ S, if j ≤ c w then weight j else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [threshold, Finset.natCast_card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> simp

/-- Threshold incidence is bounded by the actual total first moment. -/
 theorem threshold_incidence_le_mass (S : Finset W) (c : W → ℕ) (j : ℕ) :
    (j : ℝ) * ((threshold S c j).card : ℝ) ≤ mass S c := by
  calc
    _ = ∑ w ∈ threshold S c j, (j : ℝ) := by simp [mul_comm]
    _ ≤ ∑ w ∈ threshold S c j, (c w : ℝ) := by
      apply Finset.sum_le_sum
      intro w hw
      exact_mod_cast (Finset.mem_filter.mp hw).2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun w _ _ => Nat.cast_nonneg _)

/-- Derive the high-layer tail from density, rather than assume a tail premise. -/
 theorem density_tail_mul (S : Finset W) (c : W → ℕ) {j : ℕ} (a ell : ℝ)
    (hcut : 2*a ≤ (j : ℝ))
    (hdensity : (j : ℝ) * ((threshold S c j).card : ℝ) ≤
      a * (ell + ((threshold S c j).card : ℝ))) :
    (j : ℝ) * ((threshold S c j).card : ℝ) ≤ 2*a*ell := by
  have hn : (0 : ℝ) ≤ (threshold S c j).card := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_right hcut hn
  nlinarith

 theorem density_tail (S : Finset W) (c : W → ℕ) {j : ℕ} (hj : 1 ≤ j) (a ell : ℝ)
    (hcut : 2*a ≤ (j : ℝ))
    (hdensity : (j : ℝ) * ((threshold S c j).card : ℝ) ≤
      a * (ell + ((threshold S c j).card : ℝ))) :
    ((threshold S c j).card : ℝ) ≤ 2*a*ell/(j : ℝ) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  apply (le_div_iff₀ hj0).mpr
  simpa only [mul_comm] using density_tail_mul S c a ell hcut hdensity

/-- Count actual positive indices below an arbitrary real cutoff using their maximum. -/
 theorem positive_cut_card_le (J : Finset ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hpos : ∀ j ∈ J, 1 ≤ j) (hbound : ∀ j ∈ J, (j : ℝ) < b) :
    (J.card : ℝ) ≤ b := by
  by_cases hne : J.Nonempty
  · let m := J.max' hne
    have hm : m ∈ J := Finset.max'_mem J hne
    have hsub : J ⊆ Finset.Icc 1 m := by
      intro j hj
      exact Finset.mem_Icc.mpr ⟨hpos j hj, J.le_max' j hj⟩
    have hcard : J.card ≤ m := by
      simpa using Finset.card_le_card hsub
    have hcard' : (J.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hcard
    exact hcard'.trans (hbound m hm).le
  · have he : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simpa only [he, Finset.card_empty, Nat.cast_zero] using hb

 theorem low_card_le (Δ : ℕ) (a : ℝ) (ha : 0 ≤ a) : ((low Δ a).card : ℝ) ≤ 2*a := by
  apply positive_cut_card_le _ _ (by positivity)
  · intro j hj
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
  · intro j hj
    exact (Finset.mem_filter.mp hj).2

 theorem high_card_le (Δ : ℕ) (a : ℝ) : ((high Δ a).card : ℝ) ≤ (Δ : ℝ) := by
  have hh : (high Δ a).card ≤ Δ := by
    simpa [high] using Finset.card_le_card
      (Finset.filter_subset (fun j : ℕ => 2*a ≤ (j : ℝ)) (Finset.Icc 1 Δ))
  exact_mod_cast hh

 theorem low_sum_le_four (S : Finset W) (c : W → ℕ) (Δ : ℕ) (a ell : ℝ)
    (ha : 0 ≤ a) (hmass : mass S c ≤ ell*(Δ : ℝ)) :
    (∑ j ∈ low Δ a, weight j * ((threshold S c j).card : ℝ)) ≤ 4*a*ell*(Δ : ℝ) := by
  have hterm (j : ℕ) (_hj : j ∈ low Δ a) :
      weight j * ((threshold S c j).card : ℝ) ≤ 2 * mass S c := by
    have hh := threshold_incidence_le_mass S c j
    have hn : (0 : ℝ) ≤ (threshold S c j).card := Nat.cast_nonneg _
    unfold weight
    nlinarith
  calc
    _ ≤ ∑ j ∈ low Δ a, 2 * mass S c := Finset.sum_le_sum hterm
    _ = ((low Δ a).card : ℝ) * (2 * mass S c) := by simp
    _ ≤ (2*a)*(2*mass S c) :=
      mul_le_mul_of_nonneg_right (low_card_le Δ a ha)
        (mul_nonneg (by norm_num) (mass_nonneg S c))
    _ = 4*a*mass S c := by ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 4*a by positivity)
      nlinarith

 theorem high_sum_le_four (S : Finset W) (c : W → ℕ) (Δ : ℕ) (a ell : ℝ)
    (ha : 0 ≤ a) (hell : 0 ≤ ell)
    (hdensity : ∀ j ∈ Finset.Icc 1 Δ,
      (j : ℝ) * ((threshold S c j).card : ℝ) ≤
        a * (ell + ((threshold S c j).card : ℝ))) :
    (∑ j ∈ high Δ a, weight j * ((threshold S c j).card : ℝ)) ≤ 4*a*ell*(Δ : ℝ) := by
  have hterm (j : ℕ) (hj : j ∈ high Δ a) :
      weight j * ((threshold S c j).card : ℝ) ≤ 4*a*ell := by
    have hi := (Finset.mem_filter.mp hj).1
    have hcut := (Finset.mem_filter.mp hj).2
    have hh := density_tail_mul S c a ell hcut (hdensity j hi)
    have hn : (0 : ℝ) ≤ (threshold S c j).card := Nat.cast_nonneg _
    unfold weight
    nlinarith
  calc
    _ ≤ ∑ j ∈ high Δ a, 4*a*ell := Finset.sum_le_sum hterm
    _ = ((high Δ a).card : ℝ) * (4*a*ell) := by simp
    _ ≤ (Δ : ℝ)*(4*a*ell) := mul_le_mul_of_nonneg_right (high_card_le Δ a) (by positivity)
    _ = _ := by ring

/-- Density of actual thresholds plus a first moment derives the full square-sum bound. -/
 theorem square_sum_le_eight (S : Finset W) (c : W → ℕ) (Δ : ℕ) (a ell : ℝ)
    (ha : 1 ≤ a) (hell : 0 ≤ ell) (hc : ∀ w ∈ S, c w ≤ Δ)
    (hmass : mass S c ≤ ell*(Δ : ℝ))
    (hdensity : ∀ j ∈ Finset.Icc 1 Δ,
      (j : ℝ) * ((threshold S c j).card : ℝ) ≤
        a * (ell + ((threshold S c j).card : ℝ))) :
    (∑ w ∈ S, (c w : ℝ)^2) ≤ 8*a*ell*(Δ : ℝ) := by
  have ha0 : 0 ≤ a := by linarith
  rw [layer_cake S c Δ hc]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 Δ)
    (fun j => (j : ℝ) < 2*a) (fun j => weight j * ((threshold S c j).card : ℝ))
  calc
    _ = (∑ j ∈ low Δ a, weight j * ((threshold S c j).card : ℝ)) +
        ∑ j ∈ high Δ a, weight j * ((threshold S c j).card : ℝ) := by
      simpa only [low, high, not_lt] using hsplit.symm
    _ ≤ 4*a*ell*(Δ : ℝ) + 4*a*ell*(Δ : ℝ) :=
      add_le_add (low_sum_le_four S c Δ a ell ha0 hmass)
        (high_sum_le_four S c Δ a ell ha0 hell hdensity)
    _ = _ := by ring

end Erdos642.CampaignFe72210bContinuation3.CodegreeLayerCake
