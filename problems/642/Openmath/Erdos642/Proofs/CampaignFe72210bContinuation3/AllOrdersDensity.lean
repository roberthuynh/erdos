import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.CutExtractSubtype
import Openmath.Erdos642.Proofs.CampaignFe72210b.IntegrationParameters

/-! Actual eventual-average to all-orders edge-density conversion, at any natural exponent. -/
namespace Erdos642.CampaignFe72210bContinuation3.AllOrdersDensity
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.CutExtraction
universe u

def EventualAvoidingAverage (p : ℕ) (K : ℝ) (n0 : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], n0 ≤ Fintype.card V →
    ¬ HasRichCycle G → graphAverage G ≤ K * (Real.log (Fintype.card V : ℝ)) ^ p

def AllAvoidingEdgeDensity (p : ℕ) (C : ℝ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], ¬ HasRichCycle G →
    (G.edgeFinset.card : ℝ) ≤
      C * (Fintype.card V : ℝ) * (Real.log (2 * (Fintype.card V : ℝ))) ^ p

/-- The actual small-order bound, including order zero. -/
theorem edge_card_le_order_square {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card ≤ (Fintype.card V) ^ 2 :=
  G.card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ 2)

/-- The coefficient is constructed before quantifying all graphs. Order zero,
order one, all other small orders, and exponent zero are included. -/
theorem exists_all_orders_density (p : ℕ) (K : ℝ) (n0 : ℕ)
    (hK : 0 < K) (_hn0 : 3 ≤ n0) (hevent : EventualAvoidingAverage.{u} p K n0) :
    ∃ C : ℝ, 0 < C ∧ AllAvoidingEdgeDensity.{u} p C := by
  let B : ℝ := (n0 : ℝ) / (Real.log 2) ^ p
  let C : ℝ := K + B
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 ≤ B := div_nonneg (Nat.cast_nonneg _) (pow_nonneg hlogtwo.le p)
  have hC : 0 < C := add_pos_of_pos_of_nonneg hK hB
  have hKC : K ≤ C := le_add_of_nonneg_right hB
  have hBC : B ≤ C := le_add_of_nonneg_left hK.le
  have hBcancel : B * (Real.log 2) ^ p = (n0 : ℝ) :=
    div_mul_cancel₀ _ (pow_pos hlogtwo p).ne'
  refine ⟨C, hC, ?_⟩
  intro V _ _ G _ havoid
  let N := Fintype.card V
  change (G.edgeFinset.card : ℝ) ≤ C * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ p
  have heN : G.edgeFinset.card ≤ N ^ 2 := edge_card_le_order_square G
  by_cases hNzero : N = 0
  · have hezero : G.edgeFinset.card = 0 := by simpa [hNzero] using heN
    simp [hNzero, hezero]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hNzero
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hNrealpos : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hlog2N : Real.log 2 ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlog2Npos : 0 < Real.log (2 * (N : ℝ)) := hlogtwo.trans_le hlog2N
    have hlog2Nnonneg : 0 ≤ (Real.log (2 * (N : ℝ))) ^ p :=
      pow_nonneg hlog2Npos.le p
    by_cases hlarge : n0 ≤ N
    · have havg := hevent V G hlarge havoid
      have hidentity : graphAverage G * (N : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
        unfold graphAverage
        rw [degreeVolume_eq_twice_edges]
        exact div_mul_cancel₀ _ hNrealpos.ne'
      have htwo : 2 * (G.edgeFinset.card : ℝ) ≤
          K * (N : ℝ) * (Real.log (N : ℝ)) ^ p := by
        have hh := mul_le_mul_of_nonneg_right havg hNrealpos.le
        nlinarith only [hh, hidentity]
      have hedge : (G.edgeFinset.card : ℝ) ≤
          K * (N : ℝ) * (Real.log (N : ℝ)) ^ p := by
        have he0 : (0 : ℝ) ≤ G.edgeFinset.card := Nat.cast_nonneg _
        nlinarith only [htwo, he0]
      have hlogs : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
        Real.log_le_log hNrealpos (by linarith)
      have hpows := pow_le_pow_left₀ (Real.log_nonneg hNreal) hlogs p
      calc
        _ ≤ K * (N : ℝ) * (Real.log (N : ℝ)) ^ p := hedge
        _ ≤ K * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ p :=
          mul_le_mul_of_nonneg_left hpows (mul_nonneg hK.le hNrealpos.le)
        _ ≤ C * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ p := by gcongr
    · have hsmall : N ≤ n0 := by omega
      have hNbound : (G.edgeFinset.card : ℝ) ≤ (n0 : ℝ) * (N : ℝ) := by
        have hs : N ^ 2 ≤ n0 * N := by simpa only [pow_two] using Nat.mul_le_mul_right N hsmall
        exact_mod_cast heN.trans hs
      have hpows := pow_le_pow_left₀ hlogtwo.le hlog2N p
      calc
        _ ≤ (n0 : ℝ) * (N : ℝ) := hNbound
        _ = B * (N : ℝ) * (Real.log 2) ^ p := by rw [← hBcancel]; ring
        _ ≤ B * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ p :=
          mul_le_mul_of_nonneg_left hpows (mul_nonneg hB hNrealpos.le)
        _ ≤ C * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ p := by gcongr

end Erdos642.CampaignFe72210bContinuation3.AllOrdersDensity
