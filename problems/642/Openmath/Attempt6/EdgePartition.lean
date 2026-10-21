import Openmath.Attempt6.WellExpandingSeed
import Openmath.Attempt6.PublicBernoulli
import Mathlib

/-!
Actual original-edge sampling for CJMM Section7.3. A Bool coordinate is assigned
to each unordered vertex pair, and the sampled graph retains only original edges.
For a fixed seed, crossing columns of distinct outside vertices are disjoint.
-/

namespace Erdos585.Attempt6.EdgePartition

open SimpleGraph Finset MeasureTheory ProbabilityTheory Real
open RobustCore WellExpandingSeed OAI.ErdosGallai.Sampling

variable {V : Type*} [Fintype V] [DecidableEq V]

def sampledGraph (G : SimpleGraph V) (omega : Sym2 V → Bool) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ omega s(a,b) = true
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro a h; exact h.1.ne rfl⟩

theorem sampledGraph_le (G : SimpleGraph V) (omega : Sym2 V → Bool) :
    sampledGraph G omega ≤ G := fun _ _ h => h.1

/-- Actual original edges in a single crossing column. -/
noncomputable def columnEdges (G : SimpleGraph V) (U : Finset V) (v : V) :
    Finset (Sym2 V) := by
  classical
  exact (U.filter (G.Adj v)).image (fun u => s(u,v))

theorem columnEdges_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (v : V) : (columnEdges G U v).card = (U.filter (G.Adj v)).card := by
  classical
  have hinj : Function.Injective (fun u : V => s(u,v)) := by
    intro a b h
    rcases Sym2.eq_iff.mp h with h | h
    · exact h.1
    · exact h.1.trans h.2
  have heq : columnEdges G U v = (U.filter (G.Adj v)).image (fun u => s(u,v)) := by
    ext e
    simp [columnEdges]
  rw [heq,Finset.card_image_of_injective _ hinj]

theorem columnEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (v : V) : columnEdges G U v ⊆ G.edgeFinset := by
  classical
  intro e he
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
  simp only [Finset.mem_filter] at hu
  simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hu.2.symm

theorem columnEdges_disjoint (G : SimpleGraph V) (U : Finset V)
    {v w : V} (hv : v ∉ U) (hw : w ∉ U) (hvw : v ≠ w) :
    Disjoint (columnEdges G U v) (columnEdges G U w) := by
  classical
  rw [Finset.disjoint_left]
  intro e hev hew
  obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hev
  obtain ⟨b,hb,heb⟩ := Finset.mem_image.mp hew
  simp only [Finset.mem_filter] at ha hb
  have h := hea.trans heb.symm
  rcases Sym2.eq_iff.mp h with h | h
  · exact hvw h.2
  · exact hw (h.1 ▸ ha.1)

theorem columnEdges_pairwise (G : SimpleGraph V) (U : Finset V) :
    Pairwise (fun v w : {v // v ∉ U} =>
      Disjoint (columnEdges G U v.1) (columnEdges G U w.1)) := by
  intro v w hne
  exact columnEdges_disjoint G U v.2 w.2 (fun h => hne (Subtype.ext h))

theorem sampled_external_iff (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V → Bool) (v : V) :
    v ∈ externalNeighbors (sampledGraph G omega) U ↔
      v ∉ U ∧ ¬Disjoint (columnEdges G U v) (sampleVertices omega) := by
  classical
  rw [mem_external]
  constructor
  · rintro ⟨hv,u,hu,hG,hs⟩
    refine ⟨hv,?_⟩
    intro hd
    exact Finset.disjoint_left.mp hd
      (Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,hG.symm⟩,rfl⟩)
      (by simp [sampleVertices,hs])
  · rintro ⟨hv,hn⟩
    have hmeet := Finset.not_disjoint_iff.mp hn
    obtain ⟨e,he,hs⟩ := hmeet
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
    simp only [Finset.mem_filter] at hu
    refine ⟨hv,u,hu.1,hu.2.symm,?_⟩
    simpa [sampleVertices] using hs

/-- Chernoff control of the number of sampled actual edges in one column. -/
theorem column_lower_tail (G : SimpleGraph V) (p : unitInterval) (U : Finset V) (v : V) :
    (sampleMeasure (Sym2 V) p).real
      {omega | (((columnEdges G U v) ∩ sampleVertices omega).card : ℝ) ≤
        (p : ℝ) * (columnEdges G U v).card / 2} ≤
      exp (-(p : ℝ) * (columnEdges G U v).card / 8) :=
  sample_card_lower_tail p (columnEdges G U v)

theorem sample_miss_measure {E : Type*} [Fintype E] [DecidableEq E]
    (p : unitInterval) (S : Finset E) :
    sampleMeasure E p {omega | Disjoint S (sampleVertices omega)} =
      (ENNReal.ofReal (1 - (p : ℝ))) ^ S.card := by
  rw [← ENNReal.ofReal_pow (sub_nonneg.mpr p.property.2)]
  rw [← sample_miss_probability p S]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

/-- Independent miss events for genuinely disjoint coordinate blocks. -/
theorem sample_miss_independent {E I : Type*} [Fintype E] [DecidableEq E]
    (p : unitInterval) (S : I → Finset E)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    iIndepSet (fun i => {omega | Disjoint (S i) (sampleVertices omega)})
      (sampleMeasure E p) := by
  classical
  rw [iIndepSet_iff_meas_biInter (fun _ => MeasurableSet.of_discrete)]
  intro t
  have heq : (⋂ i ∈ t, {omega | Disjoint (S i) (sampleVertices omega)}) =
      {omega | Disjoint (t.biUnion S) (sampleVertices omega)} := by
    ext omega
    simp only [Set.mem_iInter,Set.mem_setOf_eq,Finset.disjoint_left,
      Finset.mem_biUnion]
    aesop
  rw [heq,sample_miss_measure,Finset.card_biUnion]
  · simp_rw [sample_miss_measure]
    exact (Finset.prod_pow_eq_pow_sum t (fun i => (S i).card) _).symm
  · intro i hi j hj hij
    exact hS hij

noncomputable def hitIndicator {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (omega : E → Bool) : ℝ := by
  classical
  exact if Disjoint S (sampleVertices omega) then 0 else 1

theorem hitIndicator_values {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (omega : E → Bool) :
    hitIndicator S omega = 0 ∨ hitIndicator S omega = 1 := by
  classical
  by_cases h : Disjoint S (sampleVertices omega) <;> simp [hitIndicator,h]

theorem hitIndicator_integral {E : Type*} [Fintype E] [DecidableEq E]
    (p : unitInterval) (S : Finset E) :
    ∫ omega, hitIndicator S omega ∂sampleMeasure E p = 1 - (1 - (p : ℝ)) ^ S.card := by
  classical
  have heq : hitIndicator S = fun omega => (1 : ℝ) -
      {omega | Disjoint S (sampleVertices omega)}.indicator (fun _ => (1 : ℝ)) omega := by
    funext omega
    by_cases h : Disjoint S (sampleVertices omega) <;> simp [hitIndicator,h]
  rw [heq,integral_sub (integrable_const _) Integrable.of_finite,
    integral_const,integral_indicator_const _ MeasurableSet.of_discrete,
    sample_miss_probability]
  simp

theorem hitIndicator_independent {E I : Type*} [Fintype E] [DecidableEq E]
    (p : unitInterval) (S : I → Finset E)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    iIndepFun (fun i => hitIndicator (S i)) (sampleMeasure E p) := by
  classical
  have hi := (sample_miss_independent p S hS).iIndepFun_indicator (β := ℝ) (m := inferInstance)
  have hh := hi.comp (fun _ : I => fun x : ℝ => 1 - x)
    (fun _ => (measurable_const.sub measurable_id : Measurable (fun x : ℝ => 1 - x)))
  convert hh using 1
  funext i omega
  by_cases h : Disjoint (S i) (sampleVertices omega) <;>
    simp [hitIndicator,Function.comp_def,h]

/-- A Chernoff lower tail for the number of hit crossing blocks. Independence
comes from actual disjoint edge-coordinate supports. -/
theorem hit_blocks_lower_tail {E I : Type*} [Fintype E] [DecidableEq E]
    (p : unitInterval) (S : I → Finset E)
    (hS : Pairwise fun i j => Disjoint (S i) (S j))
    (d : ℕ) (hd : ∀ i, (S i).card = d) (T : Finset I) :
    (sampleMeasure E p).real {omega | (∑ i ∈ T, hitIndicator (S i) omega) ≤
      (1 - (1 - (p : ℝ)) ^ d) * T.card / 2} ≤
      exp (-(1 - (1 - (p : ℝ)) ^ d) * T.card / 8) := by
  apply bernoulli_sum_lower_tail T (fun _ => measurable_of_finite _)
    (hitIndicator_independent p S hS) (fun i => hitIndicator_values (S i))
    (1 - (1 - (p : ℝ)) ^ d)
  · have hp1 : (1 - (p : ℝ)) ^ d ≤ 1 := pow_le_one₀
      (sub_nonneg.mpr p.property.2) (by linarith [p.property.1])
    linarith
  · intro i
    rw [hitIndicator_integral,hd]

noncomputable def columnDegree (G : SimpleGraph V) (U : Finset V) (v : V) : ℕ :=
  (columnEdges G U v).card

noncomputable def highNeighbors (G : SimpleGraph V) (U : Finset V) (d : ℕ) : Finset V := by
  classical
  exact Uᶜ.filter (fun v => d ≤ columnDegree G U v)

theorem dyadic_pointwise_bound (m a : ℕ) (ha : a < 2 ^ m) :
    a ≤ ∑ i ∈ Finset.range m, if 2 ^ i ≤ a then 2 ^ (i + 1) else 0 := by
  induction m with
  | zero => simpa using ha
  | succ m ih =>
    rw [Finset.sum_range_succ]
    by_cases hsmall : a < 2 ^ m
    · exact (ih hsmall).trans (Nat.le_add_right _ _)
    · rw [if_pos (by omega)]
      exact (Nat.le_of_lt ha).trans (Nat.le_add_left _ _)

/-- Finite dyadic degree summation, including zero columns without a bucket. -/
theorem dyadic_sum_bound {W : Type*} [DecidableEq W]
    (T : Finset W) (f : W → ℕ) (m : ℕ) :
    (∑ v ∈ T.filter (fun v => f v < 2 ^ m), f v) ≤
      ∑ i ∈ Finset.range m, 2 ^ (i + 1) * (T.filter (fun v => 2 ^ i ≤ f v)).card := by
  classical
  calc
    _ ≤ ∑ v ∈ T, ∑ i ∈ Finset.range m, if 2 ^ i ≤ f v then 2 ^ (i + 1) else 0 := by
      calc
        _ ≤ ∑ v ∈ T.filter (fun v => f v < 2 ^ m),
            ∑ i ∈ Finset.range m, if 2 ^ i ≤ f v then 2 ^ (i + 1) else 0 :=
          Finset.sum_le_sum (fun v hv =>
            dyadic_pointwise_bound m (f v) (Finset.mem_filter.mp hv).2)
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (by intros; exact Nat.zero_le _)
    _ = ∑ i ∈ Finset.range m, ∑ v ∈ T, if 2 ^ i ≤ f v then 2 ^ (i + 1) else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter]
      simp [mul_comm]

/-- The actual cut-edge cardinality is bounded by its column-degree sum. -/
theorem cutEdges_card_le_sum (G : SimpleGraph V) (U B : Finset V) :
    (cutEdges G B U).card ≤ ∑ v ∈ B, columnDegree G U v := by
  classical
  unfold cutEdges columnDegree columnEdges
  convert (Finset.card_biUnion_le (s := B)
    (t := fun a => (U.filter (G.Adj a)).image (fun b => s(a,b)))) using 1
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  ext e
  simp only [Finset.mem_image]
  constructor <;> rintro ⟨u,hu,h⟩ <;> refine ⟨u,hu,?_⟩ <;>
    simpa only [Sym2.eq_swap] using h

theorem boundary_after_low_cut (G : SimpleGraph V) (U : Finset V) (d : ℕ) :
    externalNeighbors (G.deleteEdges
      (cutEdges G (Uᶜ.filter (fun v => columnDegree G U v < d)) U)) U ⊆
        highNeighbors G U d := by
  classical
  intro v hv
  obtain ⟨hvU,u,hu,hug⟩ := mem_external.mp hv
  have hdel := SimpleGraph.deleteEdges_adj.mp hug
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_compl.mpr hvU,?_⟩
  by_contra hn
  have hvB : v ∈ Uᶜ.filter (fun v => columnDegree G U v < d) := by simp [hvU]; omega
  have he := mk_mem_cutEdges hvB hu hdel.1.symm
  exact hdel.2 (by simpa only [Finset.mem_coe,Sym2.eq_swap] using he)

/-- The robustness parameter is strictly below the actual graph order. -/
theorem robustness_lt_order (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (hn : 2 ≤ Fintype.card V) (hL : 0 < L) (hepsilon : 0 < epsilon) :
    s < Fintype.card V := by
  classical
  by_contra hs
  have hsn : (Fintype.card V : ℝ) ≤ s := le_of_not_gt hs
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.choice inferInstance
  let U : Finset V := {v}
  let F := cutEdges G U Finset.univ
  have hFcard : F.card ≤ Fintype.card V := by
    have hc := cutEdges_card_le G U Finset.univ (Fintype.card V)
      (fun a ha => (Finset.card_filter_le _ _).trans (by simp))
    simpa [U] using hc
  have hFbudget : (F.card : ℝ) ≤ s * U.card := by
    have hcR : (F.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hFcard
    simpa [U] using hcR.trans hsn
  have hsmall : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3 := by
    have hnR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    simp only [U,Finset.card_singleton,Nat.cast_one]
    linarith
  have hFG := cutEdges_subset G U Finset.univ
  have hr := hG U (by simp [U]) hsmall F (by
    simpa only [Finset.subset_iff,SimpleGraph.mem_edgeFinset] using hFG) hFbudget
  have hzero : externalNeighbors (G.deleteEdges F) U = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hwU,u,hu,huw⟩ := mem_external.mp hw
    have hd := SimpleGraph.deleteEdges_adj.mp huw
    exact hd.2 (mk_mem_cutEdges hu (Finset.mem_univ w) hd.1)
  have hr0 : epsilon / L ^ 2 ≤ 0 := by simpa [hzero,U] using hr
  have hp := div_pos hepsilon (sq_pos_of_pos hL)
  linarith

/-- The rounded dyadic certificate. The top power straddles s within factor
two; the explicit factor two in the conclusion safely handles the floor. -/
theorem dyadic_certificate_at (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (hL : 1 ≤ L) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hs : 0 < s) (m : ℕ) (hm : (m : ℝ) ≤ L)
    (hsm : s < 2 * ((2 : ℕ) ^ m : ℝ))
    (U : Finset V) (hU : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3) :
    ∃ i : ℕ, i ≤ m ∧
      epsilon * s * U.card / (2 * ((2 : ℕ) ^ i : ℝ) * L ^ 2) ≤
        (highNeighbors G U (2 ^ i)).card := by
  classical
  have hLp : 0 < L := by linarith
  have hL2p := sq_pos_of_pos hLp
  by_contra hn
  push_neg at hn
  have hterm : ∀ i ∈ Finset.range m,
      (((2 : ℕ) ^ (i + 1) * (highNeighbors G U (2 ^ i)).card : ℕ) : ℝ) ≤
        epsilon * s * U.card / L ^ 2 := by
    intro i hi
    have hiM : i ≤ m := by have := Finset.mem_range.mp hi; omega
    have hp : (0 : ℝ) < ((2 : ℕ) ^ i : ℝ) := by positivity
    have hb := (lt_div_iff₀ (show 0 < 2 * ((2 : ℕ) ^ i : ℝ) * L ^ 2 by positivity)).mp
      (hn i hiM)
    apply (le_div_iff₀ hL2p).mpr
    push_cast
    rw [pow_succ]
    push_cast at hb ⊢
    nlinarith
  let B := Uᶜ.filter (fun v => columnDegree G U v < 2 ^ m)
  let F := cutEdges G B U
  have hcount : F.card ≤ ∑ i ∈ Finset.range m,
      2 ^ (i + 1) * (highNeighbors G U (2 ^ i)).card := by
    exact (cutEdges_card_le_sum G U B).trans
      (dyadic_sum_bound Uᶜ (columnDegree G U) m)
  have hFbudget : (F.card : ℝ) ≤ s * U.card := by
    have hcR : (F.card : ℝ) ≤ ∑ i ∈ Finset.range m,
        (((2 : ℕ) ^ (i + 1) * (highNeighbors G U (2 ^ i)).card : ℕ) : ℝ) := by
      exact_mod_cast hcount
    have hc := hcR.trans (Finset.sum_le_sum hterm)
    have hc2 : (F.card : ℝ) ≤ (m : ℝ) * (epsilon * s * U.card / L ^ 2) := by
      simpa using hc
    have heL : (m : ℝ) * epsilon ≤ L ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left hepsilon1 (Nat.cast_nonneg m)
      nlinarith [sq_nonneg (L - 1)]
    have hweight : 0 ≤ s * (U.card : ℝ) := by positivity
    have hh := mul_le_mul_of_nonneg_right heL hweight
    have hbound : (m : ℝ) * (epsilon * s * U.card / L ^ 2) ≤ s * U.card := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hL2p).mpr
      convert hh using 1 <;> ring
    exact hc2.trans hbound
  have hlower : epsilon * U.card / L ^ 2 ≤ (highNeighbors G U (2 ^ m)).card := by
    by_cases hUe : U = ∅
    · simp only [hUe,Finset.card_empty,Nat.cast_zero,mul_zero,zero_div]
      positivity
    have hUp : 1 ≤ U.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hUe)
    have hFG := cutEdges_subset G B U
    have hr := hG U hUp hU F (by
      simpa only [Finset.subset_iff,SimpleGraph.mem_edgeFinset] using hFG) hFbudget
    have hc := Finset.card_le_card (boundary_after_low_cut G U (2 ^ m))
    have hcR : ((externalNeighbors (G.deleteEdges F) U).card : ℝ) ≤
        (highNeighbors G U (2 ^ m)).card := by exact_mod_cast hc
    exact hr.trans hcR
  have hmBad := hn m le_rfl
  have hd : (0 : ℝ) < ((2 : ℕ) ^ m : ℝ) := by positivity
  have hb := (lt_div_iff₀ (show 0 < 2 * ((2 : ℕ) ^ m : ℝ) * L ^ 2 by positivity)).mp hmBad
  have hl := (div_le_iff₀ hL2p).mp hlower
  have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  have hcoef := mul_le_mul_of_nonneg_right hsm.le (mul_nonneg hepsilon.le hU0)
  have hscale := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * ((2 : ℕ) ^ m : ℝ) by positivity)
  nlinarith

/-- CJMM7.10 with the safe factor one-half required by the printed dyadic
floor. The index bound and the degree threshold are derived from actual s. -/
theorem dyadic_certificate (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (hn : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hL : 1 ≤ L) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hs : 1 ≤ s) (U : Finset V)
    (hU : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3) :
    ∃ i : ℕ, (i : ℝ) ≤ logTwo s ∧ ((2 : ℕ) ^ i : ℝ) ≤ s ∧
      epsilon * s * U.card / (2 * ((2 : ℕ) ^ i : ℝ) * L ^ 2) ≤
        (highNeighbors G U (2 ^ i)).card := by
  classical
  let q : ℕ := ⌊s⌋₊
  let m : ℕ := Nat.log 2 q
  have hs0 : 0 ≤ s := by linarith
  have hq : 1 ≤ q := by
    apply Nat.le_floor
    norm_num
    exact hs
  have hq0 : q ≠ 0 := by omega
  have hqs : (q : ℝ) ≤ s := Nat.floor_le hs0
  have htop : (2 : ℕ) ^ m ≤ q := Nat.pow_log_le_self 2 hq0
  have hnext : q + 1 ≤ (2 : ℕ) ^ (m + 1) := by
    have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
    exact hh
  have hsm : s < 2 * ((2 : ℕ) ^ m : ℝ) := by
    have hh : s < (q : ℝ) + 1 := Nat.lt_floor_add_one s
    have hnR : (q : ℝ) + 1 ≤ ((2 : ℕ) ^ (m + 1) : ℝ) := by exact_mod_cast hnext
    push_cast at hnR ⊢
    rw [pow_succ] at hnR
    nlinarith
  have htopR : (((2 : ℕ) ^ m : ℕ) : ℝ) ≤ s :=
    (show (((2 : ℕ) ^ m : ℕ) : ℝ) ≤ (q : ℝ) by exact_mod_cast htop).trans hqs
  push_cast at htopR
  have hsn := robustness_lt_order G L epsilon s hG hn (by linarith) hepsilon
  have hlogtop := Real.log_le_log (show (0 : ℝ) < (2 : ℝ) ^ m by positivity)
    (htopR.trans hsn.le)
  have hm : (m : ℝ) ≤ L := by
    have hh : (m : ℝ) ≤ logTwo (Fintype.card V : ℝ) := by
      unfold logTwo
      apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
      push_cast at hlogtop
      rw [Real.log_pow] at hlogtop
      exact hlogtop
    exact hh.trans hlog
  obtain ⟨i,hi,hcert⟩ := dyadic_certificate_at G L epsilon s hG hL hepsilon
    hepsilon1 (by linarith) m hm hsm U hU
  have hdi : (((2 : ℕ) ^ i : ℕ) : ℝ) ≤ s := by
    have hp : (2 : ℕ) ^ i ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hi
    have hpR : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ m := by exact_mod_cast hp
    exact_mod_cast hpR.trans htopR
  refine ⟨i,?_,by exact_mod_cast hdi,hcert⟩
  unfold logTwo
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  push_cast at hdi
  have hh := Real.log_le_log (show (0 : ℝ) < (2 : ℝ) ^ i by positivity) hdi
  push_cast at hh
  rwa [Real.log_pow] at hh

noncomputable def selectedColumn (G : SimpleGraph V) (U : Finset V) (d : ℕ)
    (v : highNeighbors G U d) : Finset (Sym2 V) :=
  Classical.choose (Finset.exists_subset_card_eq
    (Finset.mem_filter.mp v.property).2)

theorem selectedColumn_subset (G : SimpleGraph V) (U : Finset V) (d : ℕ)
    (v : highNeighbors G U d) : selectedColumn G U d v ⊆ columnEdges G U v :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (Finset.mem_filter.mp v.property).2)).1

theorem selectedColumn_card (G : SimpleGraph V) (U : Finset V) (d : ℕ)
    (v : highNeighbors G U d) : (selectedColumn G U d v).card = d :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (Finset.mem_filter.mp v.property).2)).2

theorem selectedColumn_disjoint (G : SimpleGraph V) (U : Finset V) (d : ℕ) :
    Pairwise fun v w : highNeighbors G U d =>
      Disjoint (selectedColumn G U d v) (selectedColumn G U d w) := by
  classical
  intro v w hne
  have hv := Finset.mem_compl.mp (Finset.mem_filter.mp v.property).1
  have hw := Finset.mem_compl.mp (Finset.mem_filter.mp w.property).1
  exact (columnEdges_disjoint G U hv hw (fun h => hne (Subtype.ext h))).mono
    (selectedColumn_subset G U d v) (selectedColumn_subset G U d w)

theorem selected_hits_le_neighbors (G : SimpleGraph V) (U : Finset V) (d : ℕ)
    (omega : Sym2 V → Bool) :
    (∑ v : highNeighbors G U d, hitIndicator (selectedColumn G U d v) omega) ≤
      (externalNeighbors (sampledGraph G omega) U).card := by
  classical
  let T : Finset (highNeighbors G U d) := Finset.univ.filter
    (fun v => ¬Disjoint (selectedColumn G U d v) (sampleVertices omega))
  have hsum : (∑ v : highNeighbors G U d, hitIndicator (selectedColumn G U d v) omega) =
      (T.card : ℝ) := by simp [hitIndicator,T,Finset.sum_ite]
  rw [hsum]
  have hsub : T.image (fun v => v.val) ⊆ externalNeighbors (sampledGraph G omega) U := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    have hhit := (Finset.mem_filter.mp hw).2
    apply (sampled_external_iff G U omega w).mpr
    refine ⟨Finset.mem_compl.mp (Finset.mem_filter.mp w.property).1,?_⟩
    intro hd
    exact hhit (hd.mono_left (selectedColumn_subset G U d w))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
  exact_mod_cast hc

/-- The low-pd branch in actual graph language, with no assumed tail. -/
theorem sampled_neighbors_lower_tail (G : SimpleGraph V) (p : unitInterval)
    (U : Finset V) (d : ℕ) :
    (sampleMeasure (Sym2 V) p).real
      {omega | ((externalNeighbors (sampledGraph G omega) U).card : ℝ) ≤
        (1 - (1 - (p : ℝ)) ^ d) * (highNeighbors G U d).card / 2} ≤
      exp (-(1 - (1 - (p : ℝ)) ^ d) * (highNeighbors G U d).card / 8) := by
  classical
  have ht := hit_blocks_lower_tail p (selectedColumn G U d)
    (selectedColumn_disjoint G U d) d (selectedColumn_card G U d) Finset.univ
  have hsub : {omega | ((externalNeighbors (sampledGraph G omega) U).card : ℝ) ≤
        (1 - (1 - (p : ℝ)) ^ d) * (highNeighbors G U d).card / 2} ⊆
      {omega | (∑ v : highNeighbors G U d, hitIndicator (selectedColumn G U d v) omega) ≤
        (1 - (1 - (p : ℝ)) ^ d) * (highNeighbors G U d).card / 2} := by
    intro omega h
    exact (selected_hits_le_neighbors G U d omega).trans h
  apply (measureReal_mono hsub (measure_ne_top _ _)).trans
  simpa using ht

theorem sampled_column_eq (G : SimpleGraph V) (U : Finset V) (v : V)
    (omega : Sym2 V → Bool) :
    columnEdges (sampledGraph G omega) U v = columnEdges G U v ∩ sampleVertices omega := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
    have hu := Finset.mem_filter.mp hu
    refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr
      ⟨u,Finset.mem_filter.mpr ⟨hu.1,hu.2.1⟩,rfl⟩,?_⟩
    simpa [sampleVertices,Sym2.eq_swap] using hu.2.2
  · intro he
    obtain ⟨he,hs⟩ := Finset.mem_inter.mp he
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
    have hu := Finset.mem_filter.mp hu
    refine Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨hu.1,hu.2,?_⟩,rfl⟩
    simpa [sampleVertices,Sym2.eq_swap] using hs

/-- Each destroyed high-degree external vertex consumes its own disjoint
column of at least d actual deleted edges. -/
theorem highNeighbors_delete_bound (G : SimpleGraph V) (U : Finset V)
    (d : ℕ) (F : Finset (Sym2 V)) :
    d * (highNeighbors G U d).card ≤
      d * (externalNeighbors (G.deleteEdges F) U).card + F.card := by
  classical
  let T := highNeighbors G U d \ externalNeighbors (G.deleteEdges F) U
  have hcol : ∀ v ∈ T, columnEdges G U v ⊆ F := by
    intro v hv e he
    obtain ⟨hvH,hvN⟩ := Finset.mem_sdiff.mp hv
    have hvU := Finset.mem_compl.mp (Finset.mem_filter.mp hvH).1
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
    have hu := Finset.mem_filter.mp hu
    by_contra hnot
    apply hvN
    apply mem_external.mpr
    refine ⟨hvU,u,hu.1,SimpleGraph.deleteEdges_adj.mpr ⟨hu.2.symm,?_⟩⟩
    simpa only [Finset.mem_coe] using hnot
  have hsub : T.biUnion (columnEdges G U) ⊆ F :=
    Finset.biUnion_subset.mpr hcol
  have hdis : (T : Set V).PairwiseDisjoint (columnEdges G U) := by
    intro v hv w hw hne
    have hvH := (Finset.mem_sdiff.mp hv).1
    have hwH := (Finset.mem_sdiff.mp hw).1
    exact columnEdges_disjoint G U
      (Finset.mem_compl.mp (Finset.mem_filter.mp hvH).1)
      (Finset.mem_compl.mp (Finset.mem_filter.mp hwH).1) hne
  have hsize : d * T.card ≤ F.card := by
    calc
      _ = ∑ _v ∈ T, d := by simp [mul_comm]
      _ ≤ ∑ v ∈ T, (columnEdges G U v).card := by
        apply Finset.sum_le_sum
        intro v hv
        exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
      _ = (T.biUnion (columnEdges G U)).card := (Finset.card_biUnion hdis).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hcover : (highNeighbors G U d).card ≤ T.card +
      (externalNeighbors (G.deleteEdges F) U).card := by
    have hsub : highNeighbors G U d ⊆ T ∪ externalNeighbors (G.deleteEdges F) U := by
      intro v hv
      by_cases hn : v ∈ externalNeighbors (G.deleteEdges F) U
      · exact Finset.mem_union_right _ hn
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv,hn⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hh := Nat.mul_le_mul_left d hcover
  rw [Nat.mul_add] at hh
  omega

theorem hitProbability_lower (p : unitInterval) (d : ℕ) (K : ℝ)
    (hK : 0 ≤ K) (hpd : (p : ℝ) * d ≤ K) :
    (p : ℝ) * d / (K + 1) ≤ 1 - (1 - (p : ℝ)) ^ d := by
  have hx : 0 ≤ (p : ℝ) * d := mul_nonneg p.property.1 (Nat.cast_nonneg _)
  have hy : exp (-(p : ℝ) * d) ≤ 1 := by
    simpa using exp_le_exp.mpr (neg_nonpos.mpr hx)
  have hm := mul_le_mul_of_nonneg_left (add_one_le_exp ((p : ℝ) * d))
    (exp_pos (-(p : ℝ) * d)).le
  have heq : exp ((p : ℝ) * d) * exp (-(p : ℝ) * d) = 1 := by
    rw [← exp_add]
    ring_nf
    simp
  rw [mul_comm (exp (-(p : ℝ) * d)) (exp ((p : ℝ) * d)),heq] at hm
  have hbound := mul_le_mul_of_nonneg_right hpd (show 0 ≤ 1 - exp (-(p : ℝ) * d) by linarith)
  have hq : (p : ℝ) * d / (K + 1) ≤ 1 - exp (-(p : ℝ) * d) := by
    apply (div_le_iff₀ (by linarith : 0 < K + 1)).mpr
    nlinarith
  have hmiss := sample_miss_bound p (Finset.univ : Finset (Fin d))
  rw [sample_miss_probability] at hmiss
  simp only [Finset.card_univ,Fintype.card_fin] at hmiss
  linarith

/-- A specified family of deficient columns forces a lower-tail event for
their disjoint union of actual edge coordinates. -/
theorem all_blocks_deficient_tail {E I : Type*} [Fintype E] [DecidableEq E] [DecidableEq I]
    (p : unitInterval) (S : I → Finset E)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) (d : ℕ)
    (hd : ∀ i, (S i).card = d) (T : Finset I) :
    (sampleMeasure E p).real {omega | ∀ i ∈ T,
      (((S i) ∩ sampleVertices omega).card : ℝ) ≤ (p : ℝ) * d / 2} ≤
      exp (-(p : ℝ) * d * T.card / 8) := by
  classical
  have hcard : (T.biUnion S).card = d * T.card := by
    rw [Finset.card_biUnion (by intro i hi j hj hij; exact hS hij)]
    simp [hd,mul_comm]
  have hsub : {omega | ∀ i ∈ T,
      (((S i) ∩ sampleVertices omega).card : ℝ) ≤ (p : ℝ) * d / 2} ⊆
      {omega | (((T.biUnion S) ∩ sampleVertices omega).card : ℝ) ≤
        (p : ℝ) * (T.biUnion S).card / 2} := by
    intro omega homega
    change (((T.biUnion S) ∩ sampleVertices omega).card : ℝ) ≤
      (p : ℝ) * (T.biUnion S).card / 2
    have heq : (T.biUnion S) ∩ sampleVertices omega =
        T.biUnion (fun i => S i ∩ sampleVertices omega) := by ext e; simp; aesop
    have hdj : (T : Set I).PairwiseDisjoint (fun i => S i ∩ sampleVertices omega) := by
      intro i hi j hj hij
      exact (hS hij).mono Finset.inter_subset_left Finset.inter_subset_left
    rw [heq,Finset.card_biUnion hdj]
    push_cast
    have hh := Finset.sum_le_sum homega
    rw [hcard]
    push_cast
    simp only [Finset.sum_const,nsmul_eq_mul] at hh
    nlinarith [hh]
  apply (measureReal_mono hsub (measure_ne_top _ _)).trans
  have ht := sample_card_lower_tail p (T.biUnion S)
  simpa [hcard,mul_assoc] using ht

noncomputable def deficientBlocks {E I : Type*} [Fintype E] [DecidableEq E]
    [DecidableEq I] (p : unitInterval) (S : I → Finset E) (d : ℕ) (T : Finset I)
    (omega : E → Bool) : Finset I := by
  classical
  exact T.filter (fun i => (((S i) ∩ sampleVertices omega).card : ℝ) ≤ (p : ℝ) * d / 2)

/-- High-pd counting tail, obtained from disjoint actual coordinate unions.
No independence of overlapping columns or unsupported binomial law is assumed. -/
theorem many_deficient_blocks_tail {E I : Type*} [Fintype E] [DecidableEq E]
    [DecidableEq I] (p : unitInterval) (S : I → Finset E)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) (d : ℕ)
    (hd : ∀ i, (S i).card = d) (T : Finset I) (t : ℕ) :
    (sampleMeasure E p).real {omega | t ≤ (deficientBlocks p S d T omega).card} ≤
      (2 : ℝ) ^ T.card * exp (-(p : ℝ) * d * t / 8) := by
  classical
  let Ebad : Finset I → Set (E → Bool) := fun A =>
    {omega | ∀ i ∈ A, (((S i) ∩ sampleVertices omega).card : ℝ) ≤ (p : ℝ) * d / 2}
  have hsub : {omega | t ≤ (deficientBlocks p S d T omega).card} ⊆
      ⋃ A ∈ T.powersetCard t, Ebad A := by
    intro omega homega
    obtain ⟨A,hA,hAc⟩ := Finset.exists_subset_card_eq homega
    have hAT : A ⊆ T := hA.trans (Finset.filter_subset _ _)
    refine Set.mem_iUnion.mpr ⟨A,Set.mem_iUnion.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hAT,hAc⟩,?_⟩⟩
    intro i hi
    exact (Finset.mem_filter.mp (hA hi)).2
  have hprob : ∀ A ∈ T.powersetCard t,
      (sampleMeasure E p).real (Ebad A) ≤ exp (-(p : ℝ) * d * t / 8) := by
    intro A hA
    have hc := (Finset.mem_powersetCard.mp hA).2
    simpa [Ebad,hc] using all_blocks_deficient_tail p S hS d hd A
  calc
    _ ≤ (sampleMeasure E p).real (⋃ A ∈ T.powersetCard t, Ebad A) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ A ∈ T.powersetCard t, (sampleMeasure E p).real (Ebad A) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _A ∈ T.powersetCard t, exp (-(p : ℝ) * d * t / 8) := Finset.sum_le_sum hprob
    _ = ((T.powersetCard t).card : ℝ) * exp (-(p : ℝ) * d * t / 8) := by simp
    _ ≤ (2 : ℝ) ^ T.card * exp (-(p : ℝ) * d * t / 8) := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      rw [Finset.card_powersetCard]
      exact_mod_cast Nat.choose_le_two_pow T.card t

theorem high_pd_exponential_bound (p : unitInterval) (d N : ℕ)
    (hpd : 128 ≤ (p : ℝ) * d) :
    (2 : ℝ) ^ N * exp (-(p : ℝ) * d * ((N + 3) / 4 : ℕ) / 8) ≤
      exp (-(p : ℝ) * d * N / 64) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have ht : (N : ℝ) ≤ 4 * (((N + 3) / 4 : ℕ) : ℝ) := by
    have hn : N ≤ 4 * ((N + 3) / 4) := by omega
    exact_mod_cast hn
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hpow : (2 : ℝ) ^ N = exp ((N : ℝ) * Real.log 2) := by
    rw [exp_nat_mul,exp_log (by norm_num)]
  rw [hpow,← exp_add]
  apply exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_left ht (mul_nonneg p.property.1 (Nat.cast_nonneg d))
  have h2 := mul_le_mul_of_nonneg_right hpd hN
  have h3 := mul_le_mul_of_nonneg_left hlog hN
  nlinarith

/-- Probability that fewer than three quarters of the high columns retain
sampled degree at least floor(pd/2). -/
theorem sampled_high_neighbors_tail (G : SimpleGraph V) (p : unitInterval)
    (U : Finset V) (d : ℕ) (hpd : 128 ≤ (p : ℝ) * d) :
    (sampleMeasure (Sym2 V) p).real {omega |
      4 * (highNeighbors (sampledGraph G omega) U ⌊(p : ℝ) * d / 2⌋₊).card <
        3 * (highNeighbors G U d).card} ≤
      exp (-(p : ℝ) * d * (highNeighbors G U d).card / 64) := by
  classical
  let N := (highNeighbors G U d).card
  let S := selectedColumn G U d
  let T : Finset (highNeighbors G U d) := Finset.univ
  have hsub : {omega |
      4 * (highNeighbors (sampledGraph G omega) U ⌊(p : ℝ) * d / 2⌋₊).card < 3 * N} ⊆
      {omega | (N + 3) / 4 ≤ (deficientBlocks p S d T omega).card} := by
    intro omega homega
    let B := deficientBlocks p S d T omega
    let Q : Finset (highNeighbors G U d) := T \ B
    have hQ : Q.image (fun v => v.val) ⊆
        highNeighbors (sampledGraph G omega) U ⌊(p : ℝ) * d / 2⌋₊ := by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hwT,hwB⟩ := Finset.mem_sdiff.mp hw
      have hhit : (p : ℝ) * d / 2 < ((S w ∩ sampleVertices omega).card : ℝ) := by
        by_contra hn
        exact hwB (Finset.mem_filter.mpr ⟨hwT,le_of_not_gt hn⟩)
      have hdeg : ((S w ∩ sampleVertices omega).card : ℝ) ≤
          (columnDegree (sampledGraph G omega) U w : ℝ) := by
        unfold columnDegree
        rw [sampled_column_eq]
        have hsub : S w ∩ sampleVertices omega ⊆ columnEdges G U w ∩ sampleVertices omega := by
          intro e he
          exact Finset.mem_inter.mpr
            ⟨selectedColumn_subset G U d w (Finset.mem_inter.mp he).1,(Finset.mem_inter.mp he).2⟩
        exact_mod_cast Finset.card_le_card hsub
      apply Finset.mem_filter.mpr
      refine ⟨(Finset.mem_filter.mp w.property).1,?_⟩
      exact Nat.floor_le_of_le (hhit.le.trans hdeg)
    have hQc := Finset.card_le_card hQ
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hQc
    have hBT : B ⊆ T := Finset.filter_subset _ _
    have hcard : Q.card + B.card = N := by
      rw [Finset.card_sdiff_of_subset hBT]
      have ht : T.card = N := by simp [T,N]
      have hb := Finset.card_le_card hBT
      omega
    change (N + 3) / 4 ≤ B.card
    change 4 * (highNeighbors (sampledGraph G omega) U ⌊(p : ℝ) * d / 2⌋₊).card < 3 * N at homega
    omega
  have ht := many_deficient_blocks_tail p S (selectedColumn_disjoint G U d) d
    (selectedColumn_card G U d) T ((N + 3) / 4)
  have hT : T.card = N := by simp [T,N]
  rw [hT] at ht
  exact ((measureReal_mono hsub (measure_ne_top _ _)).trans ht).trans
    (high_pd_exponential_bound p d N hpd)

theorem highNeighbors_one (G : SimpleGraph V) (U : Finset V) :
    highNeighbors G U 1 = externalNeighbors G U := by
  classical
  ext v
  rw [mem_external]
  constructor
  · intro hv
    obtain ⟨hvU,hdeg⟩ := Finset.mem_filter.mp hv
    obtain ⟨e,he⟩ := Finset.card_pos.mp hdeg
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
    have hu := Finset.mem_filter.mp hu
    exact ⟨Finset.mem_compl.mp hvU,u,hu.1,hu.2.symm⟩
  · rintro ⟨hvU,u,hu,hug⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_compl.mpr hvU,?_⟩
    apply Finset.card_pos.mpr
    exact ⟨s(u,v),Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,hug.symm⟩,rfl⟩⟩

/-- Strong fixed-seed expansion, valid for every finite deletion set.
Original-edge deletion hypotheses of RobustExpanderAt follow immediately. -/
def SeedRobustAt (H : SimpleGraph V) (L epsilon b : ℝ) (U : Finset V) : Prop :=
  ∀ F : Finset (Sym2 V), (F.card : ℝ) ≤ b * U.card →
    epsilon * U.card / L ^ 2 ≤ (externalNeighbors (H.deleteEdges F) U).card

theorem seedRobust_of_many_neighbors (H : SimpleGraph V) (U : Finset V)
    (L epsilon b : ℝ)
    (hmany : 2 * b * U.card ≤ (externalNeighbors H U).card)
    (htarget : epsilon * U.card / L ^ 2 ≤ b * U.card) :
    SeedRobustAt H L epsilon b U := by
  intro F hF
  have hd := highNeighbors_delete_bound H U 1 F
  rw [highNeighbors_one] at hd
  simp only [one_mul] at hd
  have hdR : ((externalNeighbors H U).card : ℝ) ≤
      (externalNeighbors (H.deleteEdges F) U).card + F.card := by exact_mod_cast hd
  linarith

theorem seedRobust_of_many_high_neighbors (H : SimpleGraph V) (U : Finset V)
    (L epsilon b N : ℝ) (r : ℕ) (hr : 0 < r)
    (hmany : 3 * N ≤ 4 * (highNeighbors H U r).card)
    (hbudget : b * U.card ≤ (r : ℝ) * N / 4)
    (htarget : epsilon * U.card / L ^ 2 ≤ N / 2) :
    SeedRobustAt H L epsilon b U := by
  intro F hF
  have hd := highNeighbors_delete_bound H U r F
  have hdR : (r : ℝ) * (highNeighbors H U r).card ≤
      (r : ℝ) * (externalNeighbors (H.deleteEdges F) U).card + F.card := by exact_mod_cast hd
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hm := mul_le_mul_of_nonneg_left hmany hrR.le
  have hs : N / 2 ≤ ((externalNeighbors (H.deleteEdges F) U).card : ℝ) := by nlinarith
  exact htarget.trans hs

theorem sampled_seed_failure_low (G : SimpleGraph V) (p : unitInterval)
    (U : Finset V) (d : ℕ) (L epsilon b : ℝ)
    (hbudget : 2 * b * U.card ≤
      (1 - (1 - (p : ℝ)) ^ d) * (highNeighbors G U d).card / 2)
    (htarget : epsilon * U.card / L ^ 2 ≤ b * U.card) :
    (sampleMeasure (Sym2 V) p).real
      {omega | ¬SeedRobustAt (sampledGraph G omega) L epsilon b U} ≤
      exp (-(1 - (1 - (p : ℝ)) ^ d) * (highNeighbors G U d).card / 8) := by
  have hsub : {omega | ¬SeedRobustAt (sampledGraph G omega) L epsilon b U} ⊆
      {omega | ((externalNeighbors (sampledGraph G omega) U).card : ℝ) ≤
        (1 - (1 - (p : ℝ)) ^ d) * (highNeighbors G U d).card / 2} := by
    intro omega hn
    by_contra hh
    change ¬((externalNeighbors (sampledGraph G omega) U).card : ℝ) ≤
      (1 - (1 - (p : ℝ)) ^ d) * (highNeighbors G U d).card / 2 at hh
    have hm := (lt_of_not_ge hh).le
    exact hn (seedRobust_of_many_neighbors _ U L epsilon b (hbudget.trans hm) htarget)
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (sampled_neighbors_lower_tail G p U d)

theorem sampled_seed_failure_high (G : SimpleGraph V) (p : unitInterval)
    (U : Finset V) (d : ℕ) (L epsilon b : ℝ)
    (hpd : 128 ≤ (p : ℝ) * d) (hr : 0 < ⌊(p : ℝ) * d / 2⌋₊)
    (hbudget : b * U.card ≤ (⌊(p : ℝ) * d / 2⌋₊ : ℝ) *
      (highNeighbors G U d).card / 4)
    (htarget : epsilon * U.card / L ^ 2 ≤ (highNeighbors G U d).card / 2) :
    (sampleMeasure (Sym2 V) p).real
      {omega | ¬SeedRobustAt (sampledGraph G omega) L epsilon b U} ≤
      exp (-(p : ℝ) * d * (highNeighbors G U d).card / 64) := by
  classical
  have hsub : {omega | ¬SeedRobustAt (sampledGraph G omega) L epsilon b U} ⊆
      {omega | 4 * (highNeighbors (sampledGraph G omega) U ⌊(p : ℝ) * d / 2⌋₊).card <
        3 * (highNeighbors G U d).card} := by
    intro omega hn
    by_contra hh
    change ¬(4 * (highNeighbors (sampledGraph G omega) U ⌊(p : ℝ) * d / 2⌋₊).card <
      3 * (highNeighbors G U d).card) at hh
    have hhN : 3 * (highNeighbors G U d).card ≤
        4 * (highNeighbors (sampledGraph G omega) U ⌊(p : ℝ) * d / 2⌋₊).card := by omega
    have hhR : (3 : ℝ) * (highNeighbors G U d).card ≤
        4 * (highNeighbors (sampledGraph G omega) U ⌊(p : ℝ) * d / 2⌋₊).card := by exact_mod_cast hhN
    exact hn (seedRobust_of_many_high_neighbors _ U L epsilon b _ _ hr hhR hbudget htarget)
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (sampled_high_neighbors_tail G p U d hpd)

set_option maxHeartbeats 2000000

/-- Full fixed-U sampling estimate with fixed inflated numerical constants.
The log powers remain exactly three in the input and two in robustness. -/
theorem fixed_seed_sampling_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (hn : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hL : 1 ≤ L) (hp : 0 < (p : ℝ)) (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon ≤ 1) (hs : 1 ≤ s)
    (hstrong : 1048576 * L ^ 3 ≤ epsilon * (p : ℝ) * s)
    (U : Finset V) (hU : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3) :
    (sampleMeasure (Sym2 V) p).real {omega |
      ¬SeedRobustAt (sampledGraph G omega) L (epsilon / 4)
        (epsilon * (p : ℝ) * s / (1048576 * L ^ 2)) U} ≤
      exp (-epsilon * (p : ℝ) * s * U.card / (32768 * L ^ 2)) := by
  classical
  have hLp : 0 < L := by linarith
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hL2p := sq_pos_of_pos hLp
  have hsp : 0 < s := by linarith
  obtain ⟨i,hiLog,hdi,hcert⟩ := dyadic_certificate G L epsilon s hG hn hlog hL
    hepsilon hepsilon1 hs U hU
  let d : ℕ := 2 ^ i
  let N : ℝ := (highNeighbors G U d).card
  let A : ℝ := epsilon * (p : ℝ) * s * U.card / L ^ 2
  let b : ℝ := epsilon * (p : ℝ) * s / (1048576 * L ^ 2)
  have hd : (0 : ℝ) < d := by dsimp [d]; positivity
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbu : b * U.card = A / 1048576 := by dsimp [b,A]; ring
  have hc : epsilon * s * U.card ≤ 2 * (d : ℝ) * N * L ^ 2 := by
    have hcertD : epsilon * s * U.card / (2 * (d : ℝ) * L ^ 2) ≤ N := by
      dsimp [d,N]
      exact_mod_cast hcert
    have hh := (div_le_iff₀ (show 0 < 2 * (d : ℝ) * L ^ 2 by positivity)).mp hcertD
    nlinarith only [hh]
  have hAN : A ≤ 2 * ((p : ℝ) * d) * N := by
    apply (div_le_iff₀ hL2p).mpr
    have hh := mul_le_mul_of_nonneg_left hc hp.le
    convert hh using 1 <;> ring
  have htargetN : (epsilon / 4) * U.card / L ^ 2 ≤ N / 2 := by
    have hds : (d : ℝ) ≤ s := by exact_mod_cast hdi
    have hh := mul_le_mul_of_nonneg_right hds (show 0 ≤ 2 * N * L ^ 2 by positivity)
    have hscaled : epsilon * U.card * s ≤ (2 * N * L ^ 2) * s := by nlinarith [hc,hh]
    have hcancel := le_of_mul_le_mul_right hscaled hsp
    apply (div_le_iff₀ hL2p).mpr
    nlinarith
  have hb1 : 1 ≤ b := by
    have hh := mul_le_mul_of_nonneg_left hL (show 0 ≤ 1048576 * L ^ 2 by positivity)
    have hbase : 1048576 * L ^ 2 ≤ epsilon * (p : ℝ) * s := by nlinarith [hh,hstrong]
    exact (le_div_iff₀ (show 0 < 1048576 * L ^ 2 by positivity)).mpr (by simpa using hbase)
  have htargetB : (epsilon / 4) * U.card / L ^ 2 ≤ b * U.card := by
    have hcoef : epsilon / (4 * L ^ 2) ≤ b := by
      apply le_trans _ hb1
      apply (div_le_iff₀ (show 0 < 4 * L ^ 2 by positivity)).mpr
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hcoef (show (0 : ℝ) ≤ U.card by positivity)
    calc
      _ = epsilon / (4 * L ^ 2) * U.card := by ring
      _ ≤ _ := hh
  by_cases hpd : (p : ℝ) * d ≤ 512
  · let q : ℝ := 1 - (1 - (p : ℝ)) ^ d
    have hq := hitProbability_lower p d 512 (by norm_num) hpd
    have hq0 : 0 ≤ q := by dsimp [q]; linarith [div_nonneg (mul_nonneg hp.le (Nat.cast_nonneg d)) (by norm_num : (0 : ℝ) ≤ 513)]
    have hpq : (p : ℝ) * d ≤ 1024 * q := by dsimp [q] at hq0 ⊢; nlinarith only [hq,hq0]
    have hh := mul_le_mul_of_nonneg_right hpq hN
    have hAq : A ≤ 2048 * q * N := by nlinarith only [hAN,hh]
    have hbudget : 2 * b * U.card ≤ q * N / 2 := by
      rw [mul_assoc,hbu]
      nlinarith only [hAq,mul_nonneg hq0 hN]
    have ht := sampled_seed_failure_low G p U d L (epsilon / 4) b hbudget htargetB
    apply ht.trans
    apply exp_le_exp.mpr
    change -q * N / 8 ≤ -epsilon * (p : ℝ) * s * U.card / (32768 * L ^ 2)
    have heq : -epsilon * (p : ℝ) * s * U.card / (32768 * L ^ 2) = -A / 32768 := by dsimp [A]; ring
    rw [heq]
    nlinarith only [hAq,mul_nonneg hq0 hN]
  · have hpd128 : 128 ≤ (p : ℝ) * d := by linarith
    let r : ℕ := ⌊(p : ℝ) * d / 2⌋₊
    have hr : (p : ℝ) * d / 4 ≤ (r : ℝ) := by
      have hh : (p : ℝ) * d / 2 < (r : ℝ) + 1 := Nat.lt_floor_add_one _
      linarith
    have hrp : 0 < r := by
      have hh : (0 : ℝ) < r := by nlinarith only [hr,hpd128]
      exact_mod_cast hh
    have hbudget : b * U.card ≤ (r : ℝ) * N / 4 := by
      rw [hbu]
      have hh := mul_le_mul_of_nonneg_right hr hN
      nlinarith only [hAN,hh,hA]
    have ht := sampled_seed_failure_high G p U d L (epsilon / 4) b hpd128 hrp hbudget htargetN
    apply ht.trans
    apply exp_le_exp.mpr
    change -(p : ℝ) * d * N / 64 ≤ -epsilon * (p : ℝ) * s * U.card / (32768 * L ^ 2)
    have heq : -epsilon * (p : ℝ) * s * U.card / (32768 * L ^ 2) = -A / 32768 := by dsimp [A]; ring
    rw [heq]
    nlinarith only [hAN,hA]

theorem seed_entropy_sum_bound (n : ℕ) (hn : 2 ≤ n) :
    (∑ u ∈ Finset.Icc 1 n, ((u + 1 : ℕ) : ℝ) * (n : ℝ) ^ (3 * u) *
      exp (-8 * (u : ℝ) * Real.log n)) ≤ 2 / (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hexp : exp (-3 * Real.log (n : ℝ)) = ((n : ℝ) ^ 3)⁻¹ := by
    have hh : exp (3 * Real.log (n : ℝ)) = (n : ℝ) ^ 3 := by
      calc
        _ = exp (Real.log (n : ℝ)) ^ 3 := by simpa using exp_nat_mul (Real.log (n : ℝ)) 3
        _ = _ := by rw [exp_log hnp]
    rw [show -3 * Real.log (n : ℝ) = -(3 * Real.log (n : ℝ)) by ring,exp_neg,hh]
  have hterm : ∀ u ∈ Finset.Icc 1 n,
      ((u + 1 : ℕ) : ℝ) * (n : ℝ) ^ (3 * u) * exp (-8 * (u : ℝ) * Real.log n) ≤
        2 / (n : ℝ) ^ 2 := by
    intro u hu
    obtain ⟨hu1,hun⟩ := Finset.mem_Icc.mp hu
    have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu1
    have hunR : (u : ℝ) ≤ n := by exact_mod_cast hun
    have hpow : (n : ℝ) ^ (3 * u) = exp ((3 * u : ℕ) * Real.log n) := by
      rw [exp_nat_mul,exp_log hnp]
    have heq : (n : ℝ) ^ (3 * u) * exp (-8 * (u : ℝ) * Real.log n) =
        exp (-5 * (u : ℝ) * Real.log n) := by
      rw [hpow,← exp_add]
      congr 1
      push_cast
      ring
    have hh : exp (-5 * (u : ℝ) * Real.log n) ≤ exp (-3 * Real.log n) := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right huR hlog]
    calc
      _ = ((u + 1 : ℕ) : ℝ) * exp (-5 * (u : ℝ) * Real.log n) := by rw [mul_assoc,heq]
      _ ≤ ((u + 1 : ℕ) : ℝ) * exp (-3 * Real.log n) :=
        mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)
      _ ≤ (2 * (n : ℝ)) * exp (-3 * Real.log n) := by
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        push_cast
        linarith
      _ = 2 / (n : ℝ) ^ 2 := by rw [hexp]; field_simp <;> ring
  calc
    _ ≤ ∑ _u ∈ Finset.Icc 1 n, 2 / (n : ℝ) ^ 2 := Finset.sum_le_sum hterm
    _ = 2 / (n : ℝ) := by
      have hc : (Finset.Icc 1 n).card = n := by simp
      simp only [Finset.sum_const,nsmul_eq_mul,hc]
      field_simp

                                                                         
                                                                                
theorem sampled_robust_expander_failure (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (hn : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hL : 1 ≤ L) (hp : 0 < (p : ℝ)) (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon ≤ 1) (hs : 1 ≤ s)
    (hstrong : 1048576 * L ^ 3 ≤ epsilon * (p : ℝ) * s) :
    (sampleMeasure (Sym2 V) p).real {omega |
      ¬RobustExpanderAt (sampledGraph G omega) L (epsilon / 4)
        (epsilon * (p : ℝ) * s / (1048576 * L ^ 2))} ≤
      2 / (Fintype.card V : ℝ) := by
  classical
  let n := Fintype.card V
  let b := epsilon * (p : ℝ) * s / (1048576 * L ^ 2)
  let P : Finset V → Prop := fun U => (U.card : ℝ) ≤ 2 * (n : ℝ) / 3
  let E : Finset V → Finset (Sym2 V) → Set (Sym2 V → Bool) := fun U _ =>
    {omega | ¬SeedRobustAt (sampledGraph G omega) L (epsilon / 4) b U}
  have hLp : 0 < L := by linarith
  have hlog2p : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogn : Real.log (n : ℝ) ≤ L := by
    have hh := (div_le_iff₀ hlog2p).mp hlog
    have hm := mul_le_mul_of_nonneg_left hlog2 hLp.le
    dsimp [n]
    unfold logTwo at hlog
    linarith
  have hcoef : 8 * Real.log (n : ℝ) ≤ epsilon * (p : ℝ) * s / (32768 * L ^ 2) := by
    have hc : 32 * L ≤ epsilon * (p : ℝ) * s / (32768 * L ^ 2) := by
      apply (le_div_iff₀ (show 0 < 32768 * L ^ 2 by positivity)).mpr
      nlinarith only [hstrong]
    linarith
  have hlocal : ∀ U F, U.Nonempty → P U → F ⊆ G.edgeFinset → F.card ≤ U.card →
      (sampleMeasure (Sym2 V) p).real (E U F) ≤ exp (-8 * (U.card : ℝ) * Real.log n) := by
    intro U F hUne hUsmall hFG hF
    have ht := fixed_seed_sampling_bound G p L epsilon s hG hn hlog hL hp hepsilon
      hepsilon1 hs hstrong U hUsmall
    apply ht.trans
    apply exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hcoef (show (0 : ℝ) ≤ U.card by positivity)
    calc
      _ = -(epsilon * (p : ℝ) * s / (32768 * L ^ 2) * U.card) := by ring
      _ ≤ -(8 * Real.log (n : ℝ) * U.card) := neg_le_neg hh
      _ = _ := by ring
  have hunion := SampledReachability.all_seed_deletion_union_bound G (by omega : 1 ≤ n)
    P E (fun u => exp (-8 * (u : ℝ) * Real.log n)) (fun _ => (exp_pos _).le) hlocal
  have hsub : {omega |
      ¬RobustExpanderAt (sampledGraph G omega) L (epsilon / 4) b} ⊆
      {omega | ∃ U F, U.Nonempty ∧ P U ∧ F ⊆ G.edgeFinset ∧ F.card ≤ U.card ∧
        omega ∈ E U F} := by
    intro omega hnG
    by_contra hnseed
    apply hnG
    intro U hUp hUsmall F hFH hFbudget
    have hseed : SeedRobustAt (sampledGraph G omega) L (epsilon / 4) b U := by
      by_contra hbad
      apply hnseed
      refine ⟨U,∅,Finset.card_pos.mp hUp,hUsmall,Finset.empty_subset _,by simp,?_⟩
      exact hbad
    exact hseed F hFbudget
  exact ((measureReal_mono hsub (measure_ne_top _ _)).trans hunion).trans
    (seed_entropy_sum_bound n hn)

noncomputable def partitionProbability (k : ℕ) [NeZero k] : unitInterval := by
  have hk : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  exact ⟨(k : ℝ)⁻¹,inv_nonneg.mpr hk.le,(inv_le_one₀ hk).mpr hk1⟩

theorem uniform_color_mask_law (k : ℕ) [NeZero k] (i : Fin k) :
    ((PMF.uniformOfFintype (Fin k)).toMeasure).map (fun c => decide (c = i)) =
      bernoulliMeasure true false (partitionProbability k) := by
  classical
  let mu := ((PMF.uniformOfFintype (Fin k)).toMeasure).map (fun c => decide (c = i))
  have htrue : mu {true} = bernoulliMeasure true false (partitionProbability k) {true} := by
    suffices hreal : (mu {true}).toReal =
        (bernoulliMeasure true false (partitionProbability k) {true}).toReal by
      rcases (ENNReal.toReal_eq_toReal_iff _ _).mp hreal with hh | hh | hh
      · exact hh
      · exact False.elim (measure_ne_top _ _ hh.2)
      · exact False.elim (measure_ne_top _ _ hh.1)
    change mu.real {true} = (bernoulliMeasure true false (partitionProbability k)).real {true}
    rw [bernoulliMeasure_real_apply_of_mem_of_notMem _ MeasurableSet.of_discrete (by simp) (by simp)]
    change (mu {true}).toReal = _
    dsimp [mu]
    rw [Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
    have heq : Set.preimage (fun c : Fin k => decide (c = i)) {true} = {i} := by ext c; simp
    rw [heq,PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,PMF.uniformOfFintype_apply]
    simp [partitionProbability]
  apply Measure.ext_of_singleton
  intro x
  cases x with
  | true => exact htrue
  | false =>
    have heq : ({false} : Set Bool) = ({true} : Set Bool)ᶜ := by ext x; cases x <;> simp
    rw [heq,measure_compl MeasurableSet.of_discrete (measure_ne_top _ _),
      measure_compl MeasurableSet.of_discrete (measure_ne_top _ _)]
    change mu Set.univ - mu {true} = _
    rw [htrue]
    dsimp [mu]
    rw [Measure.map_apply (measurable_of_finite _) MeasurableSet.univ]
    simp only [Set.preimage_univ,measure_univ]

noncomputable def colorMeasure (E : Type*) [Fintype E] (k : ℕ) [NeZero k] :
    Measure (E → Fin k) := Measure.pi (fun _ : E => (PMF.uniformOfFintype (Fin k)).toMeasure)

instance colorMeasure_probability (E : Type*) [Fintype E] (k : ℕ) [NeZero k] :
    IsProbabilityMeasure (colorMeasure E k) := by unfold colorMeasure; infer_instance

def colorMask {E : Type*} {k : ℕ} (i : Fin k) (color : E → Fin k) (e : E) : Bool :=
  decide (color e = i)

theorem colorMask_law {E : Type*} [Fintype E] (k : ℕ) [NeZero k] (i : Fin k) :
    (colorMeasure E k).map (colorMask i) = sampleMeasure E (partitionProbability k) := by
  unfold colorMeasure colorMask sampleMeasure
  rw [Measure.pi_map_pi (f := fun _ : E => fun c : Fin k => decide (c = i))
    (μ := fun _ : E => (PMF.uniformOfFintype (Fin k)).toMeasure)
    (fun _ => (measurable_of_finite _).aemeasurable)]
  simp_rw [uniform_color_mask_law]

def colorGraph (G : SimpleGraph V) {k : ℕ} (color : Sym2 V → Fin k) (i : Fin k) :
    SimpleGraph V := sampledGraph G (colorMask i color)

theorem colorGraph_le (G : SimpleGraph V) {k : ℕ} (color : Sym2 V → Fin k) (i : Fin k) :
    colorGraph G color i ≤ G := sampledGraph_le _ _

theorem colorGraph_edge_disjoint (G : SimpleGraph V) {k : ℕ} (color : Sym2 V → Fin k)
    {i j : Fin k} (hij : i ≠ j) (a b : V) :
    ¬((colorGraph G color i).Adj a b ∧ (colorGraph G color j).Adj a b) := by
  rintro ⟨hi,hj⟩
  have hi : color s(a,b) = i := by simpa [colorGraph,sampledGraph,colorMask] using hi.2
  have hj : color s(a,b) = j := by simpa [colorGraph,sampledGraph,colorMask] using hj.2
  exact hij (hi.symm.trans hj)

theorem colorGraph_edge_cover (G : SimpleGraph V) {k : ℕ} (color : Sym2 V → Fin k)
    {a b : V} (hab : G.Adj a b) : ∃ i, (colorGraph G color i).Adj a b := by
  refine ⟨color s(a,b),hab,?_⟩
  simp [colorGraph,sampledGraph,colorMask]

/-- CJMM7.9 with fixed inflated constants, preserving the logarithmic powers.
The witness is an actual spanning edge partition of the original graph. -/
theorem edge_partition_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 1 ≤ k) (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (hn : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hL : 1 ≤ L) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hs : 1 ≤ s)
    (hstrong : 1048576 * L ^ 3 ≤ epsilon * s / (k : ℝ)) :
    ∃ H : Fin k → SimpleGraph V,
      (∀ i, H i ≤ G) ∧
      (∀ i j, i ≠ j → ∀ a b, ¬((H i).Adj a b ∧ (H j).Adj a b)) ∧
      (∀ a b, G.Adj a b → ∃ i, (H i).Adj a b) ∧
      (∀ i, RobustExpanderAt (H i) L (epsilon / 4)
        (epsilon * s / (1048576 * (k : ℝ) * L ^ 2))) := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hLp : 0 < L := by linarith
  have hsp : 0 < s := by linarith
  let p := partitionProbability k
  let mu := colorMeasure (Sym2 V) k
  let b := epsilon * s / (1048576 * (k : ℝ) * L ^ 2)
  let E : Fin k → Set (Sym2 V → Fin k) := fun i =>
    {color | ¬RobustExpanderAt (colorGraph G color i) L (epsilon / 4) b}
  have hp : 0 < (p : ℝ) := inv_pos.mpr hkR
  have hstrongP : 1048576 * L ^ 3 ≤ epsilon * (p : ℝ) * s := by
    dsimp [p,partitionProbability]
    convert hstrong using 1 <;> ring
  have hbudget : epsilon * (p : ℝ) * s / (1048576 * L ^ 2) = b := by
    dsimp [p,partitionProbability,b]
    field_simp
  have hprob : ∀ i : Fin k, mu.real (E i) ≤ 2 / (Fintype.card V : ℝ) := by
    intro i
    have ht := sampled_robust_expander_failure G p L epsilon s hG hn hlog hL hp
      hepsilon hepsilon1 hs hstrongP
    rw [hbudget] at ht
    have heq : mu.real (E i) = (sampleMeasure (Sym2 V) p).real
        {omega | ¬RobustExpanderAt (sampledGraph G omega) L (epsilon / 4) b} := by
      rw [← colorMask_law k i]
      unfold Measure.real
      rw [Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
      rfl
    rw [heq]
    exact ht
  have hkn : 2 * (k : ℝ) < Fintype.card V := by
    have hL3 : 1 ≤ L ^ 3 := by nlinarith [sq_nonneg (L - 1)]
    have hlarge : (2 : ℝ) < epsilon * s / (k : ℝ) := by nlinarith only [hstrong,hL3]
    have heps := mul_le_mul_of_nonneg_right hepsilon1 (div_nonneg hsp.le hkR.le)
    have hepsnorm : epsilon * s / (k : ℝ) ≤ s / (k : ℝ) := by
      simpa only [mul_div_assoc,one_mul] using heps
    have hsk : (2 : ℝ) < s / (k : ℝ) := hlarge.trans_le hepsnorm
    have h2k : 2 * (k : ℝ) < s := (lt_div_iff₀ hkR).mp hsk
    exact h2k.trans (robustness_lt_order G L epsilon s hG hn hLp hepsilon)
  have hsum : (∑ i : Fin k, mu.real (E i)) < 1 := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hprob i)
    have hsR : (∑ i : Fin k, mu.real (E i)) ≤ (k : ℝ) * (2 / (Fintype.card V : ℝ)) := by
      simpa using hh
    have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
    have hsmall : (k : ℝ) * (2 / (Fintype.card V : ℝ)) < 1 := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hnR).mpr
      nlinarith only [hkn]
    exact hsR.trans_lt hsmall
  obtain ⟨color,hcolor⟩ := exists_avoiding_finite_events (μ := mu) Finset.univ E hsum
  refine ⟨colorGraph G color,?_,?_,?_,?_⟩
  · exact colorGraph_le G color
  · intro i j hij a b
    exact colorGraph_edge_disjoint G color hij a b
  · intro a b hab
    exact colorGraph_edge_cover G color hab
  · intro i
    exact not_not.mp (hcolor i (Finset.mem_univ i))

theorem disjoint_of_no_common_adj (H K : SimpleGraph V)
    (h : ∀ a b, ¬(H.Adj a b ∧ K.Adj a b)) : Disjoint H K := by
  apply disjoint_iff_inf_le.mpr
  intro a b hab
  exact h a b hab

                                                                             
                                                                             
theorem edge_partition_exists_lattice (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 1 ≤ k) (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (hn : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hL : 1 ≤ L) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hs : 1 ≤ s)
    (hstrong : 1048576 * L ^ 3 ≤ epsilon * s / (k : ℝ)) :
    ∃ H : Fin k → SimpleGraph V, (∀ i, H i ≤ G) ∧
      Pairwise (fun i j => Disjoint (H i) (H j)) ∧ (⨆ i, H i) = G ∧
      (∀ i, RobustExpanderAt (H i) L (epsilon / 4)
        (epsilon * s / (1048576 * (k : ℝ) * L ^ 2))) := by
  obtain ⟨H,hle,hdis,hcover,hrob⟩ := edge_partition_exists G k hk L epsilon s hG
    hn hlog hL hepsilon hepsilon1 hs hstrong
  refine ⟨H,hle,?_,?_,hrob⟩
  · intro i j hij
    exact disjoint_of_no_common_adj (H i) (H j) (hdis i j hij)
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · rintro ⟨i,hi⟩
      exact hle i hi
    · exact hcover a b

end Erdos585.Attempt6.EdgePartition
