import Mathlib

/-! Exact integer ceiling/floor parameters for the actual regularization construction. -/
namespace Erdos642.CampaignFe72210bContinuation3.RegularizationParameters

/-- The actual number of binary size-halving steps. -/
def layerCount (n : ℕ) : ℕ := Nat.clog 2 n

noncomputable def layerWidth (n : ℕ) (D : ℝ) : ℕ :=
  Nat.floor ((D / 4 - 1) / (layerCount n : ℝ))

/-- The ceiling in the published denominator is retained literally. -/
theorem layerCount_eq_ceil (n : ℕ) :
    layerCount n = Nat.ceil (Real.log (n : ℝ) / Real.log 2) := by
  simpa only [layerCount, Real.logb, Nat.cast_ofNat] using
    (Real.natCeil_logb_natCast 2 n).symm

theorem log_two_gt_half : (1 : ℝ) / 2 < Real.log 2 := by
  linarith [Real.log_two_gt_d9]

/-- Actual integer pigeonhole inputs and the natural-log rounding loss. -/
theorem layerCount_spec (n : ℕ) (hn : 2 ≤ n) :
    1 ≤ layerCount n ∧ n ≤ 2 ^ layerCount n ∧
      0 < Real.log (n : ℝ) ∧ (layerCount n : ℝ) ≤ 4 * Real.log (n : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlognpos : 0 < Real.log (n : ℝ) := hlog2.trans_le hlogn
  let L := Real.log (n : ℝ) / Real.log 2
  have hL : 1 ≤ L := (le_div_iff₀ hlog2).mpr (by simpa [L] using hlogn)
  have hceil : (layerCount n : ℝ) < L + 1 := by
    rw [layerCount_eq_ceil]
    exact Nat.ceil_lt_add_one (show 0 ≤ L from (by norm_num : (0 : ℝ) ≤ 1).trans hL)
  have hml : (layerCount n : ℝ) ≤ 2 * L := by linarith
  have hLid : L * Real.log 2 = Real.log (n : ℝ) := div_mul_cancel₀ _ hlog2.ne'
  have hmul := mul_le_mul_of_nonneg_right hml hlog2.le
  have hmnonneg : (0 : ℝ) ≤ layerCount n := by positivity
  have hupper : (layerCount n : ℝ) ≤ 4 * Real.log (n : ℝ) := by
    nlinarith [log_two_gt_half]
  refine ⟨?_, Nat.le_pow_clog (by decide) n, hlognpos, hupper⟩
  exact Nat.clog_pos (by decide) (by omega)

/-- Integer matching indices and actual minimum-degree scale, with no graph premise. -/
theorem rounded_layer_spec (n : ℕ) (D : ℝ) (hn : 2 ≤ n) (hD : 8 ≤ D) :
    1 + layerCount n * layerWidth n D ≤ Nat.ceil (D / 4) ∧
      1 ≤ layerWidth n D + 1 ∧
      D / (100 * Real.log (n : ℝ)) ≤ ((layerWidth n D + 1 : ℕ) : ℝ) / 3 := by
  obtain ⟨hm, _, hlog, hupper⟩ := layerCount_spec n hn
  have hmpos : (0 : ℝ) < layerCount n := by exact_mod_cast (by omega : 0 < layerCount n)
  have hy : 0 ≤ (D / 4 - 1) / (layerCount n : ℝ) := div_nonneg (by linarith) hmpos.le
  have hfloor := Nat.floor_le hy
  change (layerWidth n D : ℝ) ≤ (D / 4 - 1) / (layerCount n : ℝ) at hfloor
  have hprod := (le_div_iff₀ hmpos).mp hfloor
  have hidx : (1 : ℝ) + (layerCount n : ℝ) * (layerWidth n D : ℝ) ≤ D / 4 := by
    nlinarith
  have hceil : D / 4 ≤ (Nat.ceil (D / 4) : ℝ) := Nat.le_ceil _
  have hidxNat : 1 + layerCount n * layerWidth n D ≤ Nat.ceil (D / 4) := by
    exact_mod_cast hidx.trans hceil
  have hlt := Nat.lt_floor_add_one ((D / 4 - 1) / (layerCount n : ℝ))
  change (D / 4 - 1) / (layerCount n : ℝ) < (layerWidth n D : ℝ) + 1 at hlt
  have hltprod := (div_lt_iff₀ hmpos).mp hlt
  have htpos : (0 : ℝ) ≤ (layerWidth n D : ℝ) + 1 := by positivity
  have hscale := mul_le_mul_of_nonneg_left hupper htpos
  refine ⟨hidxNat, by omega, ?_⟩
  apply (div_le_iff₀ (mul_pos (by norm_num) hlog)).mpr
  push_cast
  nlinarith

/-- The positive small-degree branch is paid by an actual single edge. -/
theorem small_degree_scale (n : ℕ) (D : ℝ) (hn : 2 ≤ n) (hD : D ≤ 8) :
    D / (100 * Real.log (n : ℝ)) ≤ 1 := by
  have hlogn : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlog : 0 < Real.log (n : ℝ) := lt_trans (by norm_num : (0 : ℝ) < 1 / 2)
    (log_two_gt_half.trans_le hlogn)
  apply (div_le_iff₀ (mul_pos (by norm_num) hlog)).mpr
  nlinarith [log_two_gt_half]

end Erdos642.CampaignFe72210bContinuation3.RegularizationParameters
