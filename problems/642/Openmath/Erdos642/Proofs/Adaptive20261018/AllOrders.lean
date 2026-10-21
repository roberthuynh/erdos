import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.AllOrdersDensity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos642.Adaptive20261018.AllOrders
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3
universe u

noncomputable def psi (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (2 * (n : ℝ)) ^ 5 /
    Real.log (Real.log (Real.exp (Real.exp 1) + (n : ℝ)))

theorem denominator_ge_one (n : ℕ) :
    1 ≤ Real.log (Real.log (Real.exp (Real.exp 1) + (n : ℝ))) := by
  have hinner : Real.exp 1 ≤ Real.log (Real.exp (Real.exp 1) + (n : ℝ)) := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (le_add_of_nonneg_right (Nat.cast_nonneg n))
  calc
    1 = Real.log (Real.exp 1) := (Real.log_exp _).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos _) hinner

@[simp] theorem psi_zero : psi 0 = 0 := by simp [psi]

theorem psi_pos (n : ℕ) (hn : 0 < n) : 0 < psi n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos (by linarith)
  have hden : 0 < Real.log (Real.log (Real.exp (Real.exp 1) + (n : ℝ))) :=
    lt_of_lt_of_le (by norm_num) (denominator_ge_one n)
  exact div_pos (mul_pos hnreal (pow_pos hlog _)) hden

theorem psi_nonneg (n : ℕ) : 0 ≤ psi n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact (psi_pos n (Nat.pos_of_ne_zero hn)).le

theorem psi_comparison (n : ℕ) (hn : (2 : ℝ) ≤ n)
    (hexp : Real.exp (Real.exp 1) ≤ (n : ℝ))
    (hlog : (2 : ℝ) ≤ Real.log (n : ℝ)) :
    (n : ℝ) * Real.log (n : ℝ)^5 / (2 * Real.log (Real.log (n : ℝ))) ≤ psi n := by
  have hnpos : (0 : ℝ) < n := by linarith
  have hlpos : 0 < Real.log (n : ℝ) := by linarith
  have hdenpos : 0 < Real.log (Real.log (Real.exp (Real.exp 1) + (n : ℝ))) :=
    lt_of_lt_of_le (by norm_num) (denominator_ge_one n)
  have hsum : Real.exp (Real.exp 1) + (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  have hfirst : Real.log (Real.exp (Real.exp 1) + (n : ℝ)) ≤ 2*Real.log (n : ℝ) := by
    calc
      _ ≤ Real.log ((n : ℝ)^2) := Real.log_le_log (by positivity) hsum
      _ = _ := by rw [Real.log_pow]; norm_num
  have hinnerpos : 0 < Real.log (Real.exp (Real.exp 1) + (n : ℝ)) := by
    apply Real.log_pos
    have hh := Real.exp_pos (Real.exp 1)
    linarith
  have hden : Real.log (Real.log (Real.exp (Real.exp 1) + (n : ℝ))) ≤
      2*Real.log (Real.log (n : ℝ)) := by
    calc
      _ ≤ Real.log (2*Real.log (n : ℝ)) := Real.log_le_log hinnerpos hfirst
      _ = Real.log 2 + Real.log (Real.log (n : ℝ)) :=
        Real.log_mul (by norm_num) hlpos.ne'
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ)<2) hlog]
  have hpow : Real.log (n : ℝ)^5 ≤ Real.log (2*(n : ℝ))^5 :=
    pow_le_pow_left₀ hlpos.le (Real.log_le_log hnpos (by linarith)) 5
  unfold psi
  calc
    _ ≤ (n : ℝ)*Real.log (n : ℝ)^5 /
        Real.log (Real.log (Real.exp (Real.exp 1)+(n : ℝ))) :=
      div_le_div_of_nonneg_left (by positivity) hdenpos hden
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hnpos.le) hdenpos.le

/-- Finite-order completion for any positive scale, with zero-order handled explicitly.
The eventual premise remains visible in this supporting adapter. -/
theorem all_orders_of_eventual (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (hf : ∀ n, 0 < n → 0 < f n) (K : ℝ) (hK : 0 < K) (n0 : ℕ)
    (hevent : ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], n0 ≤ Fintype.card V →
      ¬HasRichCycle G → (G.edgeFinset.card : ℝ) ≤ K * f (Fintype.card V)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬HasRichCycle G →
      (G.edgeFinset.card : ℝ) ≤ C * f (Fintype.card V) := by
  classical
  have hfn (n : ℕ) : 0 ≤ f n := by
    by_cases hn : n = 0
    · simp [hn, hf0]
    · exact (hf n (Nat.pos_of_ne_zero hn)).le
  let B : ℝ := ∑ i ∈ Finset.range n0, (i : ℝ)^2 / f i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (hfn i))
  refine ⟨K+B, add_pos_of_pos_of_nonneg hK hB, ?_⟩
  intro V _ _ G _ ha
  let n := Fintype.card V
  have hnedge : (G.edgeFinset.card : ℝ) ≤ (n : ℝ)^2 := by
    exact_mod_cast AllOrdersDensity.edge_card_le_order_square G
  by_cases hn0 : n = 0
  · have he : G.edgeFinset.card = 0 := by
      have hh := AllOrdersDensity.edge_card_le_order_square G
      change G.edgeFinset.card ≤ n^2 at hh
      simpa [hn0] using hh
    change (G.edgeFinset.card : ℝ) ≤ (K+B)*f n
    simp [he, hn0, hf0]
  · have hnp : 0 < f n := hf n (Nat.pos_of_ne_zero hn0)
    by_cases hlarge : n0 ≤ n
    · exact (hevent V G hlarge ha).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) hnp.le)
    · have hmem : n ∈ Finset.range n0 := Finset.mem_range.mpr (by omega)
      have hs : (n : ℝ)^2 / f n ≤ B :=
        Finset.single_le_sum (fun i _ => div_nonneg (sq_nonneg _) (hfn i)) hmem
      have hbound : (n : ℝ)^2 ≤ B*f n := (div_le_iff₀ hnp).mp hs
      exact hnedge.trans (hbound.trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK.le) hnp.le))

end Erdos642.Adaptive20261018.AllOrders
