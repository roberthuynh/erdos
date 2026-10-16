import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.LocalAvoidanceMoment

/-! Explicit log(2 minDegree)^8 normalization of authentic-P8 local fourth returns. -/
namespace Erdos642.CampaignFe72210bContinuation3.LocalAvoidanceMomentNormalized
open Erdos642.CampaignFe72210b
open LocalAvoidanceMoment
universe u

noncomputable def logFactor : ℝ := 2+Real.log 10100/Real.log 2
noncomputable def baseConstant (C : ℝ) : ℝ := 1/(Real.log 2)^8+C*logFactor^8
noncomputable def momentConstant (C : ℝ) : ℝ := 80001*baseConstant C

theorem log_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)

theorem momentConstant_lower (C : ℝ) (hC : 0 ≤ C) :
    1/(Real.log (2 : ℝ))^8 ≤ momentConstant C := by
  have hbase : 1/(Real.log (2 : ℝ))^8 ≤ baseConstant C := by
    unfold baseConstant
    have hh : 0 ≤ C*logFactor^8 := by positivity
    linarith
  have h0 : 0 ≤ baseConstant C := le_trans (by positivity) hbase
  unfold momentConstant
  nlinarith

theorem local_log_bound (d : ℝ) (hd : 1 ≤ d) (Δ : ℕ) (hΔ : 1 ≤ Δ)
    (hmax : (Δ : ℝ) ≤ 100*d) :
    Real.log (2*((Δ : ℝ)+(Δ : ℝ)^2)) ≤ logFactor*Real.log (2*d) := by
  have hdp : 0 < d := by linarith
  have hΔp : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have hΔ0 : 0 ≤ (Δ : ℝ) := Nat.cast_nonneg _
  have hsquare : (Δ : ℝ)^2 ≤ 10000*d^2 := by
    have hh := pow_le_pow_left₀ hΔ0 hmax 2
    norm_num [mul_pow] at hh
    exact hh
  have hlinear : (Δ : ℝ) ≤ 100*d^2 := by nlinarith
  have hcap : 2*((Δ : ℝ)+(Δ : ℝ)^2) ≤ 10100*(2*d)^2 := by nlinarith
  have hlog := Real.log_le_log
    (show 0 < 2*((Δ : ℝ)+(Δ : ℝ)^2) by positivity) hcap
  rw [Real.log_mul (by norm_num : (10100 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlow : Real.log (2 : ℝ) ≤ Real.log (2*d) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h10100 : 0 ≤ Real.log (10100 : ℝ) := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hlow (div_nonneg h10100 log_two_pos.le)
  rw [div_mul_cancel₀ _ (ne_of_gt log_two_pos)] at hh
  unfold logFactor
  nlinarith only [hlog,hh]

theorem coefficient_bound (C d : ℝ) (hC : 0 ≤ C) (hd : 1 ≤ d)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hmax : (Δ : ℝ) ≤ 100*d) :
    coefficient C Δ ≤ baseConstant C*Real.log (2*d)^8 := by
  have hdp : 0 < d := by linarith
  have hΔp : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have hl0 : 0 ≤ Real.log (2*((Δ : ℝ)+(Δ : ℝ)^2)) := Real.log_nonneg (by nlinarith)
  have hpow := pow_le_pow_left₀ hl0 (local_log_bound d hd Δ hΔ hmax) 8
  rw [mul_pow] at hpow
  have hm := mul_le_mul_of_nonneg_left hpow hC
  have hlow : Real.log (2 : ℝ) ≤ Real.log (2*d) := Real.log_le_log (by norm_num) (by linarith)
  have hpowlo := pow_le_pow_left₀ log_two_pos.le hlow 8
  have hlogpow : 0 < (Real.log (2 : ℝ))^8 := pow_pos log_two_pos _
  have hone : (1 : ℝ) ≤ (1/(Real.log (2 : ℝ))^8)*Real.log (2*d)^8 := by
    have hh : (1 : ℝ) ≤ Real.log (2*d)^8/(Real.log (2 : ℝ))^8 :=
      (le_div_iff₀ hlogpow).mpr (by simpa only [one_mul] using hpowlo)
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
  unfold coefficient baseConstant
  nlinarith only [hm,hone]

theorem raw_bound_normalized (C d : ℝ) (hC : 0 ≤ C) (hd : 1 ≤ d)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hmax : (Δ : ℝ) ≤ 100*d) :
    1/d^2+8*coefficient C Δ*(Δ : ℝ)^2/d^4 ≤
      momentConstant C*Real.log (2*d)^8/d^2 := by
  have hdp : 0 < d := by linarith
  have ha := coefficient_ge_one C hC Δ
  have ha0 : 0 ≤ coefficient C Δ := by linarith
  have hΔ0 : 0 ≤ (Δ : ℝ) := Nat.cast_nonneg _
  have hs : (Δ : ℝ)^2 ≤ 10000*d^2 := by
    have hh := pow_le_pow_left₀ hΔ0 hmax 2
    norm_num [mul_pow] at hh
    exact hh
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 8*coefficient C Δ by positivity)
  have hc := coefficient_bound C d hC hd Δ hΔ hmax
  have hc' := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 80001)
  have hnum : 1+80000*coefficient C Δ ≤ momentConstant C*Real.log (2*d)^8 := by
    unfold momentConstant
    nlinarith only [ha,hc']
  apply (le_div_iff₀ (sq_pos_of_pos hdp)).mpr
  have he : (1/d^2+8*coefficient C Δ*(Δ : ℝ)^2/d^4)*d^2 =
      1+8*coefficient C Δ*(Δ : ℝ)^2/d^2 := by field_simp [ne_of_gt hdp]
  rw [he]
  have hfrac : 8*coefficient C Δ*(Δ : ℝ)^2/d^2 ≤ 80000*coefficient C Δ := by
    apply (div_le_iff₀ (sq_pos_of_pos hdp)).mpr
    nlinarith only [hm]
  exact (add_le_add (show (1 : ℝ) ≤ 1 from le_rfl) hfrac).trans hnum

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Uniform actual normalized moment; authentic all-graph P8 remains external. -/
theorem graph_fourth_return_normalized (C : ℝ) (hC : 0 ≤ C) (hP8 : AllAvoidingP8.{u} C)
    (havoid : ¬ HasRichCycle G) (hbip : G.IsBipartite)
    (hd : 1 ≤ G.minDegree) (hratio : G.maxDegree ≤ 100*G.minDegree) (v : V) :
    (graphTransition G^4) v v ≤
      momentConstant C*Real.log (2*(G.minDegree : ℝ))^8/(G.minDegree : ℝ)^2 := by
  have hd' : (1 : ℝ) ≤ (G.minDegree : ℝ) := by exact_mod_cast hd
  have hdp : 0 < (G.minDegree : ℝ) := by linarith
  have hΔ : 1 ≤ G.maxDegree := hd.trans ((G.minDegree_le_degree v).trans (G.degree_le_maxDegree v))
  have hmax : (G.maxDegree : ℝ) ≤ 100*(G.minDegree : ℝ) := by exact_mod_cast hratio
  have hh := graph_fourth_return_from_P8 G C hC hP8 havoid hbip (G.minDegree : ℝ) hdp
    (fun x => by exact_mod_cast G.minDegree_le_degree x) G.maxDegree hΔ (G.degree_le_maxDegree) v
  exact hh.trans (raw_bound_normalized C (G.minDegree : ℝ) hC hd' G.maxDegree hΔ hmax)
end Erdos642.CampaignFe72210bContinuation3.LocalAvoidanceMomentNormalized
