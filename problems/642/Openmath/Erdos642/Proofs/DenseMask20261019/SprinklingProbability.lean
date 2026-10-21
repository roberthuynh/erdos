import Openmath.Attempt6.PublicBernoulli

/-! Actual fixed-set and original-matching sprinkler failure probabilities. -/
noncomputable section
namespace Erdos642.DenseMask20261019.SprinklingProbability
open MeasureTheory ProbabilityTheory Finset Real SimpleGraph
open OAI.ErdosGallai.Sampling
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem count_lower_tail (r : unitInterval) (S : Finset V) (a : ℝ)
    (ha : 0 ≤ a) (hmean : 11*a/50 ≤ (r : ℝ)*S.card) :
    (sampleMeasure V r).real {z | ((S ∩ sampleVertices z).card : ℝ) ≤ a/5} ≤
      exp (-a/2000) := by
  have hi := sampleIndicator_indep (V := V) r
  have hInt : Integrable (fun z => exp ((-1/10 : ℝ)*(∑ v ∈ S, sampleIndicator v) z))
      (sampleMeasure V r) := hi.integrable_exp_mul_sum sampleIndicator_measurable
    (fun i _ => integrable_exp_mul_of_mem_Icc (sampleIndicator_measurable i).aemeasurable
      (ae_of_all _ (indicator_mem_Icc (sampleIndicator_values i))))
  have hb := measure_le_le_exp_mul_mgf (X := ∑ v ∈ S, sampleIndicator v)
    (a/5) (by norm_num : (-1/10 : ℝ) ≤ 0) hInt
  have hm := mgf_indicator_sum_bound S sampleIndicator_measurable hi sampleIndicator_values
    (r : ℝ) (-1/10) (sampleIndicator_integral r)
  have he : exp (-1/10 : ℝ) ≤ 200/221 := by
    rw [show (-1/10 : ℝ) = -(1/10) by ring, exp_neg]
    apply (inv_le_comm₀ (exp_pos _) (by norm_num : (0 : ℝ) < 200/221)).mpr
    have h := quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/10)
    norm_num at *
    linarith
  have hx := mul_le_mul_of_nonneg_left he
    (mul_nonneg (Nat.cast_nonneg S.card) r.property.1)
  have hscalar : -(-1/10 : ℝ)*(a/5) +
      (S.card : ℝ)*(r : ℝ)*(exp (-1/10 : ℝ)-1) ≤ -a/2000 := by nlinarith
  simpa only [Finset.sum_apply, sampleIndicator_sum] using
    (hb.trans ((mul_le_mul_of_nonneg_left hm (exp_pos _).le).trans (by
      rw [← exp_add]
      exact exp_le_exp.mpr hscalar)))

private lemma matching_supports_disjoint (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) : Pairwise fun e f : M.edgeSet => Disjoint e.val.toFinset f.val.toFinset := by
  intro e f hef
  apply Finset.disjoint_left.mpr
  intro x hxe hxf
  obtain ⟨y,he⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hxe)
  obtain ⟨z,hf⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hxf)
  have hy : M.Adj x y := by simpa only [he, SimpleGraph.Subgraph.mem_edgeSet] using e.property
  have hz : M.Adj x z := by simpa only [hf, SimpleGraph.Subgraph.mem_edgeSet] using f.property
  have hyz := hM.eq_of_adj_left hy hz
  apply hef
  apply Subtype.ext
  rw [he,hf,hyz]

/-- Disjoint actual matching edges give independent two-vertex hit events. -/
theorem matching_no_hit (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    (r : unitInterval) :
    (sampleMeasure V r).real {z | ∀ e ∈ M.edgeSet, ¬ e.toFinset ⊆ sampleVertices z} ≤
      exp (-(r : ℝ)^2*(M.edgeSet.ncard : ℝ)/2) := by
  classical
  letI : Fintype M.edgeSet := Fintype.ofFinite _
  let S : M.edgeSet → Finset V := fun e => e.val.toFinset
  have hS := matching_supports_disjoint G M hM
  have hs : ∀ e : M.edgeSet, (S e).card = 2 := by
    intro e
    exact Sym2.card_toFinset_of_not_isDiag e.val (G.not_isDiag_of_mem_edgeSet (M.edgeSet_subset e.property))
  have hi := (sample_blocks_independent r S hS).iIndepFun_indicator (β := ℝ) (m := inferInstance)
  have hmeas : ∀ e, Measurable (blockIndicator (S e)) := fun _ => measurable_of_finite _
  have hInt : Integrable (fun z => exp ((-1 : ℝ)*(∑ e ∈ (Finset.univ : Finset M.edgeSet),
      blockIndicator (S e)) z)) (sampleMeasure V r) :=
    hi.integrable_exp_mul_sum hmeas (fun e _ => integrable_exp_mul_of_mem_Icc
      (hmeas e).aemeasurable (ae_of_all _ (indicator_mem_Icc (blockIndicator_values (S e)))))
  have hb := measure_le_le_exp_mul_mgf (X := ∑ e ∈ (Finset.univ : Finset M.edgeSet), blockIndicator (S e))
    0 (by norm_num : (-1 : ℝ) ≤ 0) hInt
  have hm := mgf_indicator_sum_bound (Finset.univ : Finset M.edgeSet) hmeas hi
    (fun e => blockIndicator_values (S e)) ((r : ℝ)^2) (-1) (by
      intro e; rw [blockIndicator_integral,hs])
  have he : exp (-1 : ℝ) ≤ 1/2 := by
    rw [exp_neg]
    apply (inv_le_comm₀ (exp_pos _) (by norm_num : (0 : ℝ) < 1/2)).mpr
    have h := add_one_le_exp (1 : ℝ)
    norm_num at *
    exact h
  have hc : (Fintype.card M.edgeSet : ℝ) = M.edgeSet.ncard := by
    rw [Set.fintypeCard_eq_ncard]
  calc
    _ ≤ (sampleMeasure V r).real {z | (∑ e ∈ (Finset.univ : Finset M.edgeSet), blockIndicator (S e)) z ≤ 0} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro z hz
      change ∀ e ∈ M.edgeSet, ¬ e.toFinset ⊆ sampleVertices z at hz
      change (∑ e ∈ (Finset.univ : Finset M.edgeSet), blockIndicator (S e)) z ≤ 0
      simp only [Finset.sum_apply]
      have hzero : ∀ e : M.edgeSet, blockIndicator (S e) z = 0 := by
        intro e
        exact Set.indicator_of_notMem (hz e.val e.property) _
      simp only [hzero,Finset.sum_const_zero,le_refl]
    _ ≤ _ := hb
    _ ≤ exp (-(-1 : ℝ)*0) *
        exp ((Fintype.card M.edgeSet : ℝ)*(r : ℝ)^2*(exp (-1 : ℝ)-1)) := by
      simpa only [Finset.card_univ] using mul_le_mul_of_nonneg_left hm (exp_pos _).le
    _ ≤ _ := by
      rw [← exp_add, hc]
      apply exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left he
        (mul_nonneg (Nat.cast_nonneg M.edgeSet.ncard) (sq_nonneg (r : ℝ)))
      nlinarith

theorem matching_no_hit_adj (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    (r : unitInterval) :
    (sampleMeasure V r).real {z | ∀ u v, M.Adj u v →
      ¬ (u ∈ sampleVertices z ∧ v ∈ sampleVertices z)} ≤
      exp (-(r : ℝ)^2*(M.edgeSet.ncard : ℝ)/2) := by
  have he : {z | ∀ u v, M.Adj u v → ¬ (u ∈ sampleVertices z ∧ v ∈ sampleVertices z)} =
      {z | ∀ e ∈ M.edgeSet, ¬ e.toFinset ⊆ sampleVertices z} := by
    ext z
    have hp (u v : V) : s(u,v).toFinset ⊆ sampleVertices z ↔
        u ∈ sampleVertices z ∧ v ∈ sampleVertices z := by
      constructor
      · intro h
        exact ⟨h (Sym2.mem_toFinset.mpr (by simp)), h (Sym2.mem_toFinset.mpr (by simp))⟩
      · rintro ⟨hu,hv⟩ x hx
        rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hx) with rfl | rfl
        · exact hu
        · exact hv
    constructor
    · intro h e
      refine Sym2.inductionOn e (fun u v => ?_)
      intro huv
      simpa only [hp] using h u v huv
    · intro h u v huv
      simpa only [hp] using h s(u,v) huv
  rw [he]
  exact matching_no_hit G M hM r

end Erdos642.DenseMask20261019.SprinklingProbability
