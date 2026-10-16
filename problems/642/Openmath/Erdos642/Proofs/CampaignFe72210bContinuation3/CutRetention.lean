import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.CutTrace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Ring.Pow

/-! Half-density retention from the actual finite halving charge.

The parameter uses natural logarithms with the explicit base-two conversion.
No logarithmic charge estimate or density-retention conclusion is an input to
the graph extraction theorem.
-/
namespace Erdos642.CampaignFe72210bContinuation3.CutExtraction

noncomputable def lossParameter (n : ℕ) : ℝ :=
  Real.log 2 / (2 * Real.log (n : ℝ))

theorem lossParameter_pos_le_half (n : ℕ) (hn : 2 ≤ n) :
    0 < lossParameter n ∧ lossParameter n ≤ 1 / 2 := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlogs : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) hnreal
  constructor
  · exact div_pos hlogtwo (mul_pos (by norm_num) hlogn)
  · unfold lossParameter
    apply (div_le_iff₀ (mul_pos (by norm_num) hlogn)).mpr
    nlinarith

/-- The integer charge becomes a base-two logarithmic bound by monotonicity
of the actual natural power, followed by the exact logarithm identity. -/
theorem charge_log_le (n r : ℕ) (hcharge : 2 ^ r ≤ n) :
    (r : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
  have hp : (2 : ℝ) ^ r ≤ (n : ℝ) := by exact_mod_cast hcharge
  have hlogs := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) r) hp
  simpa only [Real.log_pow] using hlogs

theorem charge_loss_le_half (n r : ℕ) (hn : 2 ≤ n) (hcharge : 2 ^ r ≤ n) :
    (r : ℝ) * lossParameter n ≤ 1 / 2 := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlogs := charge_log_le n r hcharge
  unfold lossParameter
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos (by norm_num) hlogn)).mpr
  nlinarith

/-- Finite Bernoulli gives the retained half from the derived charge bound. -/
theorem charge_retention (n r : ℕ) (hn : 2 ≤ n) (hcharge : 2 ^ r ≤ n) :
    (1 / 2 : ℝ) ≤ (1 - lossParameter n) ^ r := by
  have hlam := (lossParameter_pos_le_half n hn).2
  have hchargehalf := charge_loss_le_half n r hn hcharge
  have hbernoulli : 1 - (r : ℝ) * lossParameter n ≤
      (1 - lossParameter n) ^ r := by
    simpa only [mul_neg, sub_eq_add_neg] using
      (one_add_mul_le_pow (a := -lossParameter n) (by linarith) r)
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Actual finite cut descent retains at least half the original average and
gives restricted minimum degree at least one quarter the original average. -/
theorem exists_terminal_half_density (S : Finset V) (n : ℕ)
    (hn : 2 ≤ n) (hSn : S.card ≤ n) (hpos : 0 < average G S) :
    ∃ W : Finset V, W ⊆ S ∧ 0 < average G W ∧
      Terminal G (lossParameter n) W ∧
      average G S / 2 ≤ average G W ∧
      ∀ x ∈ W, average G S / 4 ≤ (restrictedDegree G W x : ℝ) := by
  obtain ⟨hlampos, hlamhalf⟩ := lossParameter_pos_le_half n hn
  obtain ⟨W, hWS, r, hWpos, hterm, hret, hcharge⟩ :=
    exists_terminal_with_charge G S (lossParameter n) hpos hlampos hlamhalf
  have hWcard : 1 ≤ W.card := by
    have hc := average_pos_card G W hWpos
    omega
  have hcharge' : 2 ^ r ≤ n := by
    calc
      2 ^ r = 2 ^ r * 1 := by simp
      _ ≤ 2 ^ r * W.card := Nat.mul_le_mul_left _ hWcard
      _ ≤ S.card := hcharge
      _ ≤ n := hSn
  have hhalf : average G S / 2 ≤ average G W := by
    have hb := mul_le_mul_of_nonneg_right (charge_retention n r hn hcharge') hpos.le
    nlinarith
  refine ⟨W, hWS, hWpos, hterm, hhalf, ?_⟩
  intro x hx
  have hdeg := hterm.1 x hx
  linarith

end Erdos642.CampaignFe72210bContinuation3.CutExtraction
