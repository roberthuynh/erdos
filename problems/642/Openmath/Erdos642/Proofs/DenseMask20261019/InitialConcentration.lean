import Openmath.Attempt6.PublicBernoulli
import Openmath.Erdos642.Proofs.DenseMask20261019.Sampling

/-! Initial iid sampled size and degrees at every original center. -/
noncomputable section
namespace Erdos642.DenseMask20261019.InitialConcentration
open MeasureTheory ProbabilityTheory Finset Real SimpleGraph
open OAI.ErdosGallai.Sampling
open Erdos642.CampaignFe72210bContinuation3.CutExtraction
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def GoodSample (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (d D : ℝ) (a : V → Bool) : Prop :=
  ((sampleVertices a).card : ℝ) ≤ 6*(p : ℝ)*Fintype.card V/5 ∧
  (∀ v, (p : ℝ)*d/2 ≤ (restrictedDegree G (sampleVertices a) v : ℝ)) ∧
  (∀ v, (restrictedDegree G (sampleVertices a) v : ℝ) ≤ 2*D*((p : ℝ)*d))

private lemma size_tail (p : unitInterval) :
    (sampleMeasure V p).real
      {a | 6*(p : ℝ)*Fintype.card V/5 < ((sampleVertices a).card : ℝ)} ≤
    exp (-(p : ℝ)*Fintype.card V/100) := by
  have hi := sampleIndicator_indep (V := V) p
  have hInt : Integrable (fun a => exp ((1/10 : ℝ)*
      (∑ v ∈ (Finset.univ : Finset V), sampleIndicator v) a)) (sampleMeasure V p) :=
    hi.integrable_exp_mul_sum sampleIndicator_measurable (fun i _ =>
      integrable_exp_mul_of_mem_Icc (sampleIndicator_measurable i).aemeasurable
        (ae_of_all _ (indicator_mem_Icc (sampleIndicator_values i))))
  have hb := measure_ge_le_exp_mul_mgf
    (X := ∑ v ∈ (Finset.univ : Finset V), sampleIndicator v)
    (6*(p : ℝ)*Fintype.card V/5) (by norm_num : (0 : ℝ) ≤ 1/10) hInt
  have hm := mgf_indicator_sum_bound (Finset.univ : Finset V)
    sampleIndicator_measurable hi sampleIndicator_values (p : ℝ) (1/10)
    (sampleIndicator_integral p)
  have he : exp (1/10 : ℝ) ≤ 111/100 := by
    have h := (abs_le.mp (abs_exp_sub_one_sub_id_le (by norm_num : |(1/10 : ℝ)| ≤ 1))).2
    linarith
  have hmul := mul_le_mul_of_nonneg_left he
    (mul_nonneg (Nat.cast_nonneg (Fintype.card V)) p.property.1)
  calc
    _ ≤ (sampleMeasure V p).real
        {a | 6*(p : ℝ)*Fintype.card V/5 ≤ (∑ v ∈ (Finset.univ : Finset V), sampleIndicator v) a} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro a ha
      change 6*(p : ℝ)*Fintype.card V/5 < ((sampleVertices a).card : ℝ) at ha
      change 6*(p : ℝ)*Fintype.card V/5 ≤ (∑ v ∈ (Finset.univ : Finset V), sampleIndicator v) a
      simpa only [Finset.sum_apply, sampleIndicator_sum, Finset.univ_inter] using ha.le
    _ ≤ _ := hb
    _ ≤ exp (-(1/10 : ℝ)*(6*(p : ℝ)*Fintype.card V/5)) *
        exp ((Fintype.card V : ℝ)*(p : ℝ)*(exp (1/10 : ℝ)-1)) := by
      simpa only [Finset.card_univ] using mul_le_mul_of_nonneg_left hm (exp_pos _).le
    _ ≤ _ := by
      rw [← exp_add]
      apply exp_le_exp.mpr
      nlinarith [hmul]

private lemma degree_sample (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (a : V → Bool) :
    restrictedDegree G (sampleVertices a) v = (G.neighborFinset v ∩ sampleVertices a).card := by
  unfold restrictedDegree
  congr 1
  ext x
  simp [and_comm]

private lemma numerical_budget (n : ℕ) (hn : 1 ≤ n) (rho : ℝ)
    (hr : 1000000*log (2*n) ≤ rho) :
    (1+2*(n : ℝ))*exp (-rho/100) ≤ 1/(2*(n : ℝ)^4) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl : 0 ≤ log (2*n) := log_nonneg (by linarith)
  have he : 6*(n : ℝ)^5 ≤ exp (rho/100) := by
    calc
      _ ≤ (2*(n : ℝ))^6 := by
        have h := mul_le_mul_of_nonneg_right
          (show (6 : ℝ) ≤ 64*n by linarith) (pow_nonneg hn0.le 5)
        nlinarith only [h]
      _ = exp (6*log (2*n)) := by
        rw [show (6 : ℝ)*log (2*n) = (6 : ℕ)*log (2*n) by norm_num,
          exp_nat_mul, exp_log (by positivity)]
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  have h3 : (1+2*(n : ℝ))*exp (-rho/100) ≤ 3*n*exp (-rho/100) := by
    exact mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le
  refine h3.trans ?_
  rw [show -rho/100 = -(rho/100) by ring, exp_neg]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*(n : ℝ)^4)).mpr
  have hx := exp_pos (rho/100)
  have hi : exp (rho/100)*(exp (rho/100))⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
  have hm := mul_le_mul_of_nonneg_right he (inv_nonneg.mpr hx.le)
  nlinarith only [hm,hi]

/-- Actual initial sample failure is at most 1/(2 n^4), with all degree
bounds quantified over original centers, including unsampled vertices. -/
theorem bad_goodSample_probability (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (d D : ℝ) (hn : 1 ≤ Fintype.card V)
    (hd : 0 ≤ d) (_hD : 1 ≤ D)
    (hlo : ∀ v, d ≤ (G.degree v : ℝ))
    (hhi : ∀ v, (G.degree v : ℝ) ≤ D*d)
    (hr : 1000000*log (2*Fintype.card V) ≤ (p : ℝ)*d) :
    (sampleMeasure V p).real {a | ¬ GoodSample G p d D a} ≤
      1/(2*(Fintype.card V : ℝ)^4) := by
  let rho := (p : ℝ)*d
  have hrho : 0 ≤ rho := mul_nonneg p.property.1 hd
  have hdN : d ≤ Fintype.card V := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
    exact (hlo v).trans (by exact_mod_cast (G.degree_lt_card_verts v).le)
  have hpdN : rho ≤ (p : ℝ)*Fintype.card V :=
    mul_le_mul_of_nonneg_left hdN p.property.1
  let BS : Set (V → Bool) := {a | 6*(p : ℝ)*Fintype.card V/5 < ((sampleVertices a).card : ℝ)}
  let BL : V → Set (V → Bool) := fun v =>
    {a | (restrictedDegree G (sampleVertices a) v : ℝ) < rho/2}
  let BU : V → Set (V → Bool) := fun v =>
    {a | 2*D*rho < (restrictedDegree G (sampleVertices a) v : ℝ)}
  have hS : (sampleMeasure V p).real BS ≤ exp (-rho/100) := by
    exact (size_tail p).trans (exp_le_exp.mpr (by linarith))
  have hL : ∀ v, (sampleMeasure V p).real (BL v) ≤ exp (-rho/100) := by
    intro v
    have hpdeg : rho ≤ (p : ℝ)*(G.degree v : ℝ) := mul_le_mul_of_nonneg_left (hlo v) p.property.1
    have ht := sample_card_lower_tail p (G.neighborFinset v)
    simp only [G.card_neighborFinset_eq_degree] at ht
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (ht.trans ?_)
    · intro a ha
      change (restrictedDegree G (sampleVertices a) v : ℝ) < rho/2 at ha
      rw [degree_sample] at ha
      change ((G.neighborFinset v ∩ sampleVertices a).card : ℝ) ≤ (p : ℝ)*(G.degree v : ℝ)/2
      linarith
    · apply exp_le_exp.mpr
      linarith
  have hU : ∀ v, (sampleMeasure V p).real (BU v) ≤ exp (-rho/100) := by
    intro v
    have hpdeg : rho ≤ (p : ℝ)*(G.degree v : ℝ) := mul_le_mul_of_nonneg_left (hlo v) p.property.1
    have hpmax := mul_le_mul_of_nonneg_left (hhi v) p.property.1
    have ht := sample_card_upper_tail p (G.neighborFinset v)
    simp only [G.card_neighborFinset_eq_degree] at ht
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (ht.trans ?_)
    · intro a ha
      change 2*D*rho < (restrictedDegree G (sampleVertices a) v : ℝ) at ha
      rw [degree_sample] at ha
      change 2*(p : ℝ)*(G.degree v : ℝ) ≤ ((G.neighborFinset v ∩ sampleVertices a).card : ℝ)
      dsimp [rho] at ha
      nlinarith
    · apply exp_le_exp.mpr
      linarith
  have hbad : {a | ¬ GoodSample G p d D a} = BS ∪ (⋃ v, BL v) ∪ (⋃ v, BU v) := by
    ext a
    simp only [GoodSample, BS, BL, BU, rho, Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion]
    simp only [not_and_or, not_forall, not_le]
    tauto
  rw [hbad]
  have hb := measureReal_union_le (μ := sampleMeasure V p) (BS ∪ ⋃ v, BL v) (⋃ v, BU v)
  have hb' := measureReal_union_le (μ := sampleMeasure V p) BS (⋃ v, BL v)
  have hl := measureReal_iUnion_fintype_le (μ := sampleMeasure V p) BL
  have hu := measureReal_iUnion_fintype_le (μ := sampleMeasure V p) BU
  have hls : (∑ v, (sampleMeasure V p).real (BL v)) ≤ Fintype.card V*exp (-rho/100) := by
    calc
      _ ≤ ∑ _v : V, exp (-rho/100) := Finset.sum_le_sum (fun v _ => hL v)
      _ = _ := by simp
  have hus : (∑ v, (sampleMeasure V p).real (BU v)) ≤ Fintype.card V*exp (-rho/100) := by
    calc
      _ ≤ ∑ _v : V, exp (-rho/100) := Finset.sum_le_sum (fun v _ => hU v)
      _ = _ := by simp
  have hbudget := numerical_budget (Fintype.card V) hn rho hr
  nlinarith

end Erdos642.DenseMask20261019.InitialConcentration
