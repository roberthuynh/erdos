import Openmath.Attempt6.ReachabilityAlternative

/-!
Finite fresh-layer assembly for public CJMM (Advances in Mathematics 469 (2025),
Lemma 7.12, equations (5)--(8)). Histories are genuine finite product measures.
No union bound over possible adaptive balls is used.
-/

namespace Erdos585.Attempt6.ReservoirGrowth

open MeasureTheory ProbabilityTheory Real Finset
open RobustCore Reachability SampledReachability OAI.ErdosGallai.Sampling

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two independent Bernoulli layers have this union density. -/
def unionDensity (p q : unitInterval) : unitInterval :=
  ⟨1 - (1 - (p : ℝ)) * (1 - (q : ℝ)), by
    constructor
    · nlinarith [p.property.1, p.property.2, q.property.1, q.property.2]
    · nlinarith [p.property.1, p.property.2, q.property.1, q.property.2]⟩

                                                
def sampleUnion (z : (V → Bool) × (V → Bool)) : V → Bool :=
  fun v => z.1 v || z.2 v

theorem sampleVertices_union (z : (V → Bool) × (V → Bool)) :
    sampleVertices (sampleUnion z) = sampleVertices z.1 ∪ sampleVertices z.2 := by
  ext v
  simp [sampleVertices, sampleUnion, Bool.or_eq_true]

                                                                                  
theorem bernoulli_union_law (p q : unitInterval) :
    ((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
      (fun z : Bool × Bool => z.1 || z.2) = bernoulliMeasure true false (unionDensity p q) := by
  let μ := (bernoulliMeasure true false p).prod (bernoulliMeasure true false q)
  have hfalse : μ.real {z | (z.1 || z.2) = false} = (1 - (p : ℝ)) * (1 - (q : ℝ)) := by
    have heq : {z : Bool × Bool | (z.1 || z.2) = false} = ({false} : Set Bool) ×ˢ {false} := by
      ext z
      rcases z with ⟨x,y⟩
      cases x <;> cases y <;> simp
    rw [heq, Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
    change (bernoulliMeasure true false p).real {false} *
      (bernoulliMeasure true false q).real {false} = _
    rw [bernoulliMeasure_real_apply_of_notMem_of_mem p (by simp) (by simp) (by simp),
      bernoulliMeasure_real_apply_of_notMem_of_mem q (by simp) (by simp) (by simp)]
  apply Measure.ext_of_measureReal_singleton
  intro b
  change (μ.map (fun z : Bool × Bool => z.1 || z.2)).real {b} = _
  rw [Measure.real, Measure.map_apply (measurable_of_finite _) (by measurability)]
  change μ.real {z | (z.1 || z.2) = b} = _
  cases b
  · rw [hfalse, bernoulliMeasure_real_apply_of_notMem_of_mem _ (by simp) (by simp) (by simp)]
    simp [unionDensity]
  · have heq : {z : Bool × Bool | (z.1 || z.2) = true} = {z | (z.1 || z.2) = false}ᶜ := by
      ext z
      rcases z with ⟨x,y⟩
      cases x <;> cases y <;> simp
    rw [heq, measureReal_compl (by measurability), hfalse]
    rw [bernoulliMeasure_real_apply_of_mem_of_notMem _ (by simp) (by simp) (by simp)]
    simp [μ, unionDensity]

/-- The union of actual independent vertex samples is an exact Bernoulli sample. -/
theorem sample_union_law (p q : unitInterval) :
    ((sampleMeasure V p).prod (sampleMeasure V q)).map sampleUnion =
      sampleMeasure V (unionDensity p q) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow Bool Bool V
  have he := (measurePreserving_arrowProdEquivProdArrow Bool Bool V
    (fun _ => bernoulliMeasure true false p) (fun _ => bernoulliMeasure true false q)).symm.map_eq
  change ((Measure.pi fun _ : V => bernoulliMeasure true false p).prod
    (Measure.pi fun _ : V => bernoulliMeasure true false q)).map sampleUnion = _
  let f := fun x : V → Bool × Bool => fun v => (x v).1 || (x v).2
  have hfun : f ∘ e.symm = sampleUnion := rfl
  rw [← hfun, ← Measure.map_map (measurable_of_finite _) e.symm.measurable, he]
  dsimp [f]
  rw [Measure.pi_map_pi (f := fun _ : V => fun z : Bool × Bool => z.1 || z.2)
    (fun _ => (measurable_of_finite _).aemeasurable)]
  simp_rw [bernoulli_union_law]
  rfl

universe u

/-- A finite history of n independent small layers, in chronological order. -/
def History (V : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => History V n × (V → Bool)

instance historyFintype (n : ℕ) : Fintype (History V n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (History V n × (V → Bool)))

instance historyMeasurableSpace (n : ℕ) : MeasurableSpace (History V n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSpace PUnit)
  | succ n ih => exact @Prod.instMeasurableSpace _ _ ih inferInstance

instance historyMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (History V n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSingletonClass PUnit)
  | succ n ih => exact @Prod.instMeasurableSingletonClass _ _ _ _ ih inferInstance

noncomputable def historyMeasure (q : unitInterval) : (n : ℕ) → Measure (History V n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => (historyMeasure q n).prod (sampleMeasure V q)

instance historyMeasure_probability (q : unitInterval) (n : ℕ) :
    IsProbabilityMeasure (historyMeasure (V := V) q n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | succ n ih => exact inferInstanceAs
      (IsProbabilityMeasure ((historyMeasure (V := V) q n).prod (sampleMeasure V q)))

/-- The actual union of all already exposed layers. -/
noncomputable def historyVertices : (n : ℕ) → History V n → Finset V
  | 0, _ => ∅
  | n + 1, h => historyVertices n h.1 ∪ sampleVertices h.2

                                              
def historySample : (n : ℕ) → History V n → (V → Bool)
  | 0, _ => fun _ => false
  | n + 1, h => sampleUnion (historySample n h.1, h.2)

noncomputable def historyDensity (q : unitInterval) : ℕ → unitInterval
  | 0 => 0
  | n + 1 => unionDensity (historyDensity q n) q

theorem historyVertices_sample (n : ℕ) (h : History V n) :
    historyVertices n h = sampleVertices (historySample n h) := by
  induction n with
  | zero => simp [historyVertices, historySample, sampleVertices]
  | succ n ih =>
    change historyVertices n h.1 ∪ sampleVertices h.2 = _
    rw [ih h.1, historySample, sampleVertices_union]

/-- Exact law of all layers, obtained by induction through independent products. -/
theorem history_union_law (q : unitInterval) :
    ∀ n, (historyMeasure (V := V) q n).map (historySample n) =
      sampleMeasure V (historyDensity q n) := by
  intro n
  induction n with
  | zero =>
    change (Measure.dirac (PUnit.unit : History V 0)).map (fun _ => fun _ : V => false) =
      sampleMeasure V 0
    rw [Measure.map_dirac]
    simp only [sampleMeasure, bernoulliMeasure_zero]
    apply (Measure.pi_eq fun S hS => ?_).symm
    simp only [Measure.dirac_apply]
    by_cases h : ∀ v : V, false ∈ S v
    · simp [Set.mem_pi, h]
    · have hn : (fun _ : V => false) ∉ Set.univ.pi S := by simpa using h
      rw [Set.indicator_of_notMem hn]
      symm
      obtain ⟨v,hv⟩ := not_forall.mp h
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      simp [hv]
  | succ n ih =>
    change ((historyMeasure (V := V) q n).prod (sampleMeasure V q)).map
      (sampleUnion ∘ Prod.map (historySample n) id) = _
    rw [← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
      ← Measure.map_prod_map _ _ (measurable_of_finite _) measurable_id,
      ih, Measure.map_id, sample_union_law]
    rfl

/-- One further independent layer, with arbitrary terminal density. -/
def terminalSample (n : ℕ) (z : History V n × (V → Bool)) : V → Bool :=
  sampleUnion (historySample n z.1,z.2)

theorem terminal_sample_law (q d : unitInterval) (n : ℕ) :
    ((historyMeasure (V := V) q n).prod (sampleMeasure V d)).map (terminalSample n) =
      sampleMeasure V (unionDensity (historyDensity q n) d) := by
  change ((historyMeasure (V := V) q n).prod (sampleMeasure V d)).map
    (sampleUnion ∘ Prod.map (historySample n) id) = _
  rw [← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    ← Measure.map_prod_map _ _ (measurable_of_finite _) measurable_id,
    history_union_law, Measure.map_id, sample_union_law]

/-- An independent top-up makes a lower-density sample have exactly density p. -/
noncomputable def augmentationDensity (p p₀ : unitInterval) (hle : (p₀ : ℝ) ≤ p)
    (hlt : (p₀ : ℝ) < 1) : unitInterval :=
  ⟨((p : ℝ) - p₀) / (1 - (p₀ : ℝ)), by
    have hden : 0 < 1 - (p₀ : ℝ) := by linarith
    constructor
    · exact div_nonneg (sub_nonneg.mpr hle) hden.le
    · apply (div_le_iff₀ hden).mpr
      linarith [p.property.2]⟩

theorem union_augmentationDensity (p p₀ : unitInterval) (hle : (p₀ : ℝ) ≤ p)
    (hlt : (p₀ : ℝ) < 1) :
    unionDensity p₀ (augmentationDensity p p₀ hle hlt) = p := by
  apply Subtype.ext
  dsimp [unionDensity, augmentationDensity]
  have hden : 1 - (p₀ : ℝ) ≠ 0 := by linarith
  field_simp
  ring

/-- The final literal sample consists of the chronological layers, terminal
layer, and independent top-up. -/
def finalSample (n : ℕ) (z : (History V n × (V → Bool)) × (V → Bool)) : V → Bool :=
  sampleUnion (terminalSample n z.1,z.2)

theorem final_sample_law (q d p : unitInterval) (n : ℕ)
    (hle : (unionDensity (historyDensity q n) d : ℝ) ≤ p)
    (hlt : (unionDensity (historyDensity q n) d : ℝ) < 1) :
    (((historyMeasure (V := V) q n).prod (sampleMeasure V d)).prod
      (sampleMeasure V (augmentationDensity p (unionDensity (historyDensity q n) d) hle hlt))).map
        (finalSample n) = sampleMeasure V p := by
  change (((historyMeasure (V := V) q n).prod (sampleMeasure V d)).prod _).map
    (sampleUnion ∘ Prod.map (terminalSample n) id) = _
  rw [← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    ← Measure.map_prod_map _ _ (measurable_of_finite _) measurable_id,
    terminal_sample_law, Measure.map_id, sample_union_law, union_augmentationDensity]

/-- Changing one sampled vertex changes a fixed-set sample count by at most one. -/
theorem sample_count_coordinate (S : Finset V) :
    BoundedDifferences.CoordinateBound
      (fun ω => ((S ∩ sampleVertices ω).card : ℝ)) (fun _ => 1) := by
  intro i ω η h
  have hsub : S ∩ sampleVertices ω ⊆ insert i (S ∩ sampleVertices η) := by
    intro v hv
    by_cases hvi : v = i
    · exact Finset.mem_insert.mpr (Or.inl hvi)
    · apply Finset.mem_insert.mpr
      right
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, by
        simpa [sampleVertices, h v hvi] using (Finset.mem_inter.mp hv).2⟩
  have hsub2 : S ∩ sampleVertices η ⊆ insert i (S ∩ sampleVertices ω) := by
    intro v hv
    by_cases hvi : v = i
    · exact Finset.mem_insert.mpr (Or.inl hvi)
    · apply Finset.mem_insert.mpr
      right
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, by
        simpa [sampleVertices, h v hvi] using (Finset.mem_inter.mp hv).2⟩
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have h2 := (Finset.card_le_card hsub2).trans (Finset.card_insert_le _ _)
  have h1R : ((S ∩ sampleVertices ω).card : ℝ) ≤ (S ∩ sampleVertices η).card + 1 := by
    exact_mod_cast h1
  have h2R : ((S ∩ sampleVertices η).card : ℝ) ≤ (S ∩ sampleVertices ω).card + 1 := by
    exact_mod_cast h2
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

theorem sample_count_mean (q : unitInterval) (S : Finset V) :
    (∫ ω, ((S ∩ sampleVertices ω).card : ℝ) ∂sampleMeasure V q) = (q : ℝ) * S.card := by
  simpa using sample_weight_integral q S (fun _ => (1 : ℝ))

/-- An explicit near-mean lower tail. The weaker quadratic-in-p exponent is
sufficient for the well-expanding seed budget in Lemma 7.12. -/
theorem sample_count_lower_tail (q : unitInterval) (S : Finset V) (x : ℝ) (hx : 0 ≤ x) :
    (sampleMeasure V q).real
      {ω | ((S ∩ sampleVertices ω).card : ℝ) ≤ (q : ℝ) * S.card - x} ≤
      exp (-x ^ 2 / (2 * (Fintype.card V : ℝ))) := by
  have h := BoundedDifferences.lower_tail q
    (fun ω => ((S ∩ sampleVertices ω).card : ℝ)) (fun _ => 1)
    (by intro i; norm_num) (sample_count_coordinate S) hx
  simpa [sample_count_mean] using h

/-- Matching explicit near-mean upper tail for the final p-sample. -/
theorem sample_count_upper_tail (q : unitInterval) (S : Finset V) (x : ℝ) (hx : 0 ≤ x) :
    (sampleMeasure V q).real
      {ω | (q : ℝ) * S.card + x ≤ ((S ∩ sampleVertices ω).card : ℝ)} ≤
      exp (-x ^ 2 / (2 * (Fintype.card V : ℝ))) := by
  have hc : BoundedDifferences.CoordinateBound
      (fun ω => -((S ∩ sampleVertices ω).card : ℝ)) (fun _ => 1) := by
    intro i ω η h
    have hh := sample_count_coordinate S i η ω (fun j hj => (h j hj).symm)
    convert hh using 1
    congr 1
    ring
  have h := BoundedDifferences.lower_tail q
    (fun ω => -((S ∩ sampleVertices ω).card : ℝ)) (fun _ => 1)
    (by intro i; norm_num) hc hx
  rw [integral_neg, sample_count_mean] at h
  have heq : {ω | -((S ∩ sampleVertices ω).card : ℝ) ≤ -((q : ℝ) * S.card) - x} =
      {ω | (q : ℝ) * S.card + x ≤ ((S ∩ sampleVertices ω).card : ℝ)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hh <;> linarith
  rw [heq] at h
  simpa using h

theorem unionDensity_le_add (p q : unitInterval) :
    (unionDensity p q : ℝ) ≤ (p : ℝ) + q := by
  dsimp [unionDensity]
  nlinarith [mul_nonneg p.property.1 q.property.1]

theorem historyDensity_le (q : unitInterval) :
    ∀ n, (historyDensity q n : ℝ) ≤ (n : ℝ) * q := by
  intro n
  induction n with
  | zero => simp [historyDensity]
  | succ n ih =>
    have h := unionDensity_le_add (historyDensity q n) q
    change (unionDensity (historyDensity q n) q : ℝ) ≤ _
    push_cast
    linarith

/-- Explicit small-layer density; the independent terminal layer uses 4p/5. -/
noncomputable def smallLayerDensity (p : unitInterval) (n : ℕ) : unitInterval :=
  ⟨(p : ℝ) / (6 * ((n : ℝ) + 1)), by
    have hp0 := p.property.1
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hden : 0 < 6 * ((n : ℝ) + 1) := by positivity
    constructor
    · positivity
    · apply (div_le_iff₀ hden).mpr
      linarith [p.property.2]⟩

theorem small_layer_total (p : unitInterval) (n : ℕ) :
    (n : ℝ) * (smallLayerDensity p n : ℝ) ≤ (p : ℝ) / 5 := by
  have hp0 := p.property.1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  change (n : ℝ) * ((p : ℝ) / (6 * ((n : ℝ) + 1))) ≤ _
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < 6 * ((n : ℝ) + 1))).mpr
  nlinarith [mul_nonneg hn0 hp0]

/-- The constructed small layers and terminal layer leave room for the top-up. -/
theorem small_layer_density_budget (p d : unitInterval) (n : ℕ)
    (hd : (d : ℝ) = 4 * (p : ℝ) / 5) :
    (unionDensity (historyDensity (smallLayerDensity p n) n) d : ℝ) ≤ p := by
  have h1 := unionDensity_le_add (historyDensity (smallLayerDensity p n) n) d
  have h2 := historyDensity_le (smallLayerDensity p n) n
  have h3 := small_layer_total p n
  linarith

/-- The simple density retains the source lower bound whenever the total
number of path steps does not exceed L to the fourth. -/
theorem small_layer_density_ge (p : unitInterval) (n : ℕ) (L : ℝ)
    (hL : 0 < L) (hn : (n : ℝ) + 1 ≤ L ^ 4) :
    (p : ℝ) / (6 * L ^ 4) ≤ (smallLayerDensity p n : ℝ) := by
  change (p : ℝ) / (6 * L ^ 4) ≤ (p : ℝ) / (6 * ((n : ℝ) + 1))
  apply div_le_div_of_nonneg_left p.property.1 (by positivity)
  linarith

/-- A transparent logarithmic condition pays for all multiplicative growth. -/
theorem scalar_growth_budget (N B n : ℕ) (hN : 0 < N) (hB : 1 ≤ B)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hlog : log N ≤ (n : ℝ) * a / 2) :
    2 * (N : ℝ) / 3 ≤ (1 + a) ^ n * B := by
  have hapos : 0 < 1 + a := by linarith
  have hloglower : a / 2 ≤ log (1 + a) := by
    apply le_trans _ (le_log_one_add_of_nonneg ha)
    apply (le_div_iff₀ (by positivity : 0 < a + 2)).mpr
    nlinarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ) ≤ (1 + a) ^ n := by
    rw [← exp_log hNpos, ← exp_log (pow_pos hapos n), log_pow]
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hloglower (Nat.cast_nonneg n)]
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hmul := mul_le_mul_of_nonneg_left hBR (pow_nonneg hapos.le n)
  nlinarith

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The initial ball has one original-edge step and uses no random layer. -/
noncomputable def historyBall (U : Finset V) (n : ℕ) (h : History V n) : Finset V :=
  exposedBall G U (historyVertices n h) (n + 1)

/-- Exposed paths survive enlarging the reservoir and increasing the radius. -/
theorem exposedBall_mono (U : Finset V) {Q R : Finset V} (hQR : Q ⊆ R)
    {r s : ℕ} (hrs : r ≤ s) : exposedBall G U Q r ⊆ exposedBall G U R s := by
  intro v hv
  obtain ⟨u,hu,w,hw,hs⟩ := (mem_exposedBall G U Q r v).mp hv
  apply (mem_exposedBall G U R s v).mpr
  refine ⟨u,hu,w,hw.trans hrs,?_⟩
  intro x hx
  rcases hs x hx with hstart | hend | hQ
  · exact Or.inl hstart
  · exact Or.inr (Or.inl hend)
  · exact Or.inr (Or.inr (hQR hQ))

theorem historyBall_subset_next (U : Finset V) (n : ℕ) (h : History V (n + 1)) :
    historyBall G U n h.1 ⊆ historyBall G U (n + 1) h := by
  apply exposedBall_mono G U (Finset.subset_union_left) (by omega)

theorem historyBall_initial_subset (U : Finset V) :
    ∀ n (h : History V n), exposedBall G U ∅ 1 ⊆ historyBall G U n h := by
  intro n h
  exact exposedBall_mono G U (Finset.empty_subset _) (by omega)

/-- Literal fresh-layer boundary growth enters the next actual history ball. -/
theorem history_hit_subset_new (U : Finset V) (n : ℕ) (h : History V (n + 1)) :
    sampledHitBoundary G (historyBall G U n h.1) (sampleVertices h.2) ⊆
      historyBall G U (n + 1) h \ historyBall G U n h.1 := by
  exact hit_boundary_subset_new_exposed_ball G U (historyVertices n h.1)
    (sampleVertices h.2) (n + 1)

/-- A history is bad if one of its own fresh transitions fails before saturation. -/
noncomputable def badHistory (U : Finset V) (a T : ℝ) : (n : ℕ) → History V n → Prop
  | 0, _ => False
  | n + 1, h => badHistory U a T n h.1 ∨
      ((historyBall G U n h.1).card < T ∧
        ((historyBall G U (n + 1) h \ historyBall G U n h.1).card : ℝ) <
          a * (historyBall G U n h.1).card)

/-- The exact deterministic growth conclusion on each successful trajectory. -/
theorem good_history_growth (U : Finset V) (a T : ℝ) (ha : 0 ≤ a) :
    ∀ n (h : History V n), ¬badHistory G U a T n h →
      min T ((1 + a) ^ n * (exposedBall G U ∅ 1).card) ≤
        (historyBall G U n h).card := by
  intro n
  induction n with
  | zero =>
    intro h _
    simpa [historyBall, historyVertices] using
      (min_le_right T ((exposedBall G U ∅ 1).card : ℝ))
  | succ n ih =>
    intro h hgood
    have hnot := not_or.mp hgood
    have hi := ih h.1 hnot.1
    by_cases hlarge : T ≤ ((historyBall G U n h.1).card : ℝ)
    · exact (min_le_left _ _).trans (hlarge.trans (by
        exact_mod_cast Finset.card_le_card (historyBall_subset_next G U n h)))
    · have hsmall : ((historyBall G U n h.1).card : ℝ) < T := lt_of_not_ge hlarge
      have hinc : a * (historyBall G U n h.1).card ≤
          ((historyBall G U (n + 1) h \ historyBall G U n h.1).card : ℝ) := by
        exact le_of_not_gt (fun hx => hnot.2 ⟨hsmall,hx⟩)
      have hcard := Finset.card_sdiff_add_card_eq_card (historyBall_subset_next G U n h)
      have hcR : ((historyBall G U (n + 1) h).card : ℝ) =
          ((historyBall G U (n + 1) h \ historyBall G U n h.1).card : ℝ) +
            (historyBall G U n h.1).card := by exact_mod_cast hcard.symm
      have hp : (1 + a) ^ n * (exposedBall G U ∅ 1).card ≤
          (historyBall G U n h.1).card := by
        rcases le_total T ((1 + a) ^ n * (exposedBall G U ∅ 1).card) with hx | hx
        · rw [min_eq_left hx] at hi
          exact False.elim (hlarge hi)
        · simpa only [min_eq_right hx] using hi
      apply (min_le_right _ _).trans
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ 1 + a)]

/-- Uniform fixed-ball estimates integrate over the past, and add only once per
fresh layer. No enumeration of possible W occurs in this theorem. -/
theorem bad_history_probability (U : Finset V) (q : unitInterval) (a T b : ℝ)
    (hb : 0 ≤ b)
    (hfixed : ∀ W : Finset V, exposedBall G U ∅ 1 ⊆ W → (W.card : ℝ) < T →
      (sampleMeasure V q).real
        {ω | ((sampledHitBoundary G W (sampleVertices ω)).card : ℝ) < a * W.card} ≤ b) :
    ∀ n, (historyMeasure (V := V) q n).real {h | badHistory G U a T n h} ≤ n * b := by
  intro n
  induction n with
  | zero => simp [historyMeasure, badHistory]
  | succ n ih =>
    let E : Set (History V n × (V → Bool)) :=
      {z | (historyBall G U n z.1).card < T ∧
        ((historyBall G U (n + 1) z \ historyBall G U n z.1).card : ℝ) <
          a * (historyBall G U n z.1).card}
    have hE : ((historyMeasure (V := V) q n).prod (sampleMeasure V q)).real E ≤ b := by
      apply fresh_sample_adaptive_failure_bound (historyMeasure (V := V) q n) q
        (fun h => {ω | (historyBall G U n h).card < T ∧
          ((historyBall G U (n + 1) (h,ω) \ historyBall G U n h).card : ℝ) <
            a * (historyBall G U n h).card}) b hb
      intro h
      by_cases hsmall : ((historyBall G U n h).card : ℝ) < T
      · apply le_trans _ (hfixed (historyBall G U n h) (historyBall_initial_subset G U n h) hsmall)
        apply measureReal_mono _ (measure_ne_top _ _)
        intro ω hω
        have hc : ((sampledHitBoundary G (historyBall G U n h) (sampleVertices ω)).card : ℝ) ≤
            ((historyBall G U (n + 1) (h,ω) \ historyBall G U n h).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (history_hit_subset_new G U n (h,ω))
        exact lt_of_le_of_lt hc hω.2
      · simpa [hsmall] using hb
    have heq : {h : History V (n + 1) | badHistory G U a T (n + 1) h} =
        ({h | badHistory G U a T n h} ×ˢ Set.univ) ∪ E := by
      ext h
      constructor
      · intro hh
        rcases hh with hp | hstep
        · exact Or.inl ⟨hp,Set.mem_univ _⟩
        · exact Or.inr hstep
      · intro hh
        rcases hh with hp | hstep
        · exact Or.inl hp.1
        · exact Or.inr hstep
    rw [heq]
    change ((historyMeasure (V := V) q n).prod (sampleMeasure V q)).real _ ≤ _
    have hprev : ((historyMeasure (V := V) q n).prod (sampleMeasure V q)).real
        ({h | badHistory G U a T n h} ×ˢ Set.univ) ≤ n * b := by
      simpa [Measure.real, Measure.prod_prod] using ih
    have hu := measureReal_union_le (μ := (historyMeasure (V := V) q n).prod (sampleMeasure V q))
      ({h | badHistory G U a T n h} ×ˢ Set.univ) E
    push_cast
    linarith

/-- Once the explicit growth budget reaches T, the probability of a smaller
actual final exposed ball is at most the sum of the fresh-layer failures. -/
theorem history_ball_small_probability (U : Finset V) (q : unitInterval) (a T b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ)
    (hbudget : T ≤ (1 + a) ^ n * (exposedBall G U ∅ 1).card)
    (hfixed : ∀ W : Finset V, exposedBall G U ∅ 1 ⊆ W → (W.card : ℝ) < T →
      (sampleMeasure V q).real
        {ω | ((sampledHitBoundary G W (sampleVertices ω)).card : ℝ) < a * W.card} ≤ b) :
    (historyMeasure (V := V) q n).real
      {h | ((historyBall G U n h).card : ℝ) < T} ≤ n * b := by
  apply le_trans _ (bad_history_probability G U q a T b hb hfixed n)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro h hsmall
  by_contra hgood
  have hg := good_history_growth G U a T ha n h hgood
  rw [min_eq_left hbudget] at hg
  exact (not_lt_of_ge hg) hsmall

/-- The checked structural alternative supplies a history-uniform bound using
only the initial ball as a deterministic lower bound on every adaptive ball. -/
theorem actual_history_ball_small_probability
    (L epsilon s : ℝ) (hL : 1 ≤ L) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset)
    (hB : 1 ≤ (exposedBall (G.deleteEdges F) U ∅ 1).card)
    (hF : (F.card : ℝ) ≤ s * (exposedBall (G.deleteEdges F) U ∅ 1).card / 4)
    (r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hs : 20 * (r : ℝ) * t ≤ s)
    (q : unitInterval) (hratio : 5 * (r : ℝ) ≤ 4 * (q : ℝ) * t)
    (hqr : (1 / 6 : ℝ) ≤ (q : ℝ) * r) (n : ℕ)
    (hbudget : 2 * (Fintype.card V : ℝ) / 3 ≤
      (1 + epsilon / (32 * L ^ 2)) ^ n * (exposedBall (G.deleteEdges F) U ∅ 1).card) :
    (historyMeasure (V := V) q n).real
      {h | ((historyBall (G.deleteEdges F) U n h).card : ℝ) < 2 * (Fintype.card V : ℝ) / 3} ≤
      n * (exp (-(q : ℝ) * epsilon * (exposedBall (G.deleteEdges F) U ∅ 1).card /
          (160 * (r : ℝ) * L ^ 2)) +
        exp (-epsilon ^ 2 * (exposedBall (G.deleteEdges F) U ∅ 1).card /
          (8192 * (t : ℝ) ^ 2 * L ^ 4))) := by
  apply history_ball_small_probability (G.deleteEdges F) U q
    (epsilon / (32 * L ^ 2)) (2 * (Fintype.card V : ℝ) / 3) _ (by positivity)
    (by positivity) n hbudget
  intro W hBW hWsmall
  have hcard := Finset.card_le_card hBW
  have hcardR : ((exposedBall (G.deleteEdges F) U ∅ 1).card : ℝ) ≤ W.card := by
    exact_mod_cast hcard
  have hs0 : 0 ≤ s := (by positivity : 0 ≤ 20 * (r : ℝ) * t).trans hs
  have hFW : (F.card : ℝ) ≤ s * W.card / 4 := by
    have hm := mul_le_mul_of_nonneg_left hcardR hs0
    linarith
  have hstep := ReachabilityAlternative.one_step_boundary_growth G L epsilon s hL heps heps1 hG
    W (by omega) hWsmall.le F hFG hFW r t hr ht hs q hratio hqr
  have hevent : {ω | ((sampledHitBoundary (G.deleteEdges F) W (sampleVertices ω)).card : ℝ) <
      epsilon / (32 * L ^ 2) * W.card} =
      {ω | ((sampledHitBoundary (G.deleteEdges F) W (sampleVertices ω)).card : ℝ) <
        epsilon * W.card / (32 * L ^ 2)} := by
    congr 1
    ext ω
    congr 1 <;> ring
  rw [hevent]
  apply hstep.trans
  apply add_le_add
  · apply exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hcardR (mul_nonneg q.property.1 heps.le)]
  · apply exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hcardR (sq_nonneg epsilon)]

/-- A terminal fresh layer hits a strict majority-sized fraction of the ambient
order whenever the earlier exposed ball has reached two thirds. -/
theorem terminal_ball_lower_tail (U : Finset V) (q d p : unitInterval) (n : ℕ)
    (hd : (d : ℝ) = 4 * (p : ℝ) / 5) :
    ((historyMeasure (V := V) q n).prod (sampleMeasure V d)).real
      {z | 2 * (Fintype.card V : ℝ) / 3 ≤ (historyBall G U n z.1).card ∧
        ((historyBall G U n z.1 ∩ sampleVertices z.2).card : ℝ) ≤
          31 * (p : ℝ) * Fintype.card V / 60} ≤
      exp (-((p : ℝ) * Fintype.card V / 60) ^ 2 / (2 * (Fintype.card V : ℝ))) := by
  have hp0 := p.property.1
  apply fresh_sample_adaptive_failure_bound (historyMeasure (V := V) q n) d
    (fun h => {ω | 2 * (Fintype.card V : ℝ) / 3 ≤ (historyBall G U n h).card ∧
      ((historyBall G U n h ∩ sampleVertices ω).card : ℝ) ≤
        31 * (p : ℝ) * Fintype.card V / 60}) _ (exp_pos _).le
  intro h
  by_cases hlarge : 2 * (Fintype.card V : ℝ) / 3 ≤ (historyBall G U n h).card
  · have hmean : 31 * (p : ℝ) * Fintype.card V / 60 +
        (p : ℝ) * Fintype.card V / 60 ≤
        ∫ ω, ((historyBall G U n h ∩ sampleVertices ω).card : ℝ) ∂sampleMeasure V d := by
      rw [sample_count_mean, hd]
      nlinarith [mul_le_mul_of_nonneg_left hlarge p.property.1]
    have ht := BoundedDifferences.lower_tail_of_mean_ge d
      (fun ω => ((historyBall G U n h ∩ sampleVertices ω).card : ℝ)) (fun _ => 1)
      (by intro i; norm_num) (sample_count_coordinate _) (by positivity) hmean
    simpa [hlarge] using ht
  · simpa [hlarge] using (exp_pos
      (-((p : ℝ) * Fintype.card V / 60) ^ 2 / (2 * (Fintype.card V : ℝ)))).le

/-- Literal reservoir paths survive enlarging the final reservoir. -/
theorem reservoirBall_mono_sample (U : Finset V) {Q R : Finset V} (hQR : Q ⊆ R) (r : ℕ) :
    reservoirBall G U Q r ⊆ reservoirBall G U R r := by
  intro v hv
  obtain ⟨hvQ,u,hu,w,hw,hs⟩ := mem_reservoirBall.mp hv
  exact mem_reservoirBall.mpr ⟨hQR hvQ,u,hu,w,hw,fun x hx => (hs x hx).imp_right (fun hxQ => hQR hxQ)⟩

/-- Every terminal-layer endpoint has an actual original-edge reservoir path
inside the exact-p augmented sample. -/
theorem terminal_ball_subset_final (U : Finset V) (n : ℕ)
    (z : (History V n × (V → Bool)) × (V → Bool)) :
    historyBall G U n z.1.1 ∩ sampleVertices z.1.2 ⊆
      reservoirBall G U (sampleVertices (finalSample n z)) (n + 1) := by
  apply (exposedBall_inter_subset_reservoirBall G U (historyVertices n z.1.1)
    (sampleVertices z.1.2) (n + 1)).trans
  apply reservoirBall_mono_sample G U _ (n + 1)
  rw [finalSample, sampleVertices_union, terminalSample, sampleVertices_union,
    ← historyVertices_sample]
  exact Finset.subset_union_left

/-- Finite quantitative Lemma-7.12 assembly. The displayed one-step estimates
are integrated over independent histories, and the final sample has exact law p.
The next theorem discharges its fixed-W premise with the actual graph theorem. -/
theorem reservoir_majority_from_history_bound
    (U : Finset V) (q d p : unitInterval) (n : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : (d : ℝ) = 4 * (p : ℝ) / 5)
    (hle : (unionDensity (historyDensity q n) d : ℝ) ≤ p)
    (hlt : (unionDensity (historyDensity q n) d : ℝ) < 1)
    (hbudget : 2 * (Fintype.card V : ℝ) / 3 ≤
      (1 + a) ^ n * (exposedBall G U ∅ 1).card)
    (hhistory : (historyMeasure (V := V) q n).real
      {h | ((historyBall G U n h).card : ℝ) < 2 * (Fintype.card V : ℝ) / 3} ≤ n * b) :
    (sampleMeasure V p).real
      {ω | ((reservoirBall G U (sampleVertices ω) (n + 1)).card : ℝ) ≤
        (sampleVertices ω).card / (2 : ℝ)} ≤
      n * b + 2 * exp (-((p : ℝ) * Fintype.card V / 60) ^ 2 /
        (2 * (Fintype.card V : ℝ))) := by
  have hp0 := p.property.1
  have hmeas : Measurable (finalSample (V := V) n) := measurable_of_finite _
  let r := augmentationDensity p (unionDensity (historyDensity q n) d) hle hlt
  let η := (historyMeasure (V := V) q n).prod (sampleMeasure V d)
  let μ := η.prod (sampleMeasure V r)
  let c := exp (-((p : ℝ) * Fintype.card V / 60) ^ 2 / (2 * (Fintype.card V : ℝ)))
  let A : Set (History V n) :=
    {h | ((historyBall G U n h).card : ℝ) < 2 * (Fintype.card V : ℝ) / 3}
  let B : Set (History V n × (V → Bool)) :=
    {z | 2 * (Fintype.card V : ℝ) / 3 ≤ (historyBall G U n z.1).card ∧
      ((historyBall G U n z.1 ∩ sampleVertices z.2).card : ℝ) ≤
        31 * (p : ℝ) * Fintype.card V / 60}
  let C : Set ((History V n × (V → Bool)) × (V → Bool)) :=
    {z | 61 * (p : ℝ) * Fintype.card V / 60 ≤ (sampleVertices (finalSample n z)).card}
  have hlaw : μ.map (finalSample n) = sampleMeasure V p := final_sample_law q d p n hle hlt
  have hA : μ.real ((A ×ˢ Set.univ) ×ˢ Set.univ) ≤ n * b := by
    simpa [μ,η,Measure.real,Measure.prod_prod] using
      hhistory
  have hB : μ.real (B ×ˢ Set.univ) ≤ c := by
    simpa [μ,η,Measure.real,Measure.prod_prod,c] using terminal_ball_lower_tail G U q d p n hd
  have hC : μ.real C ≤ c := by
    have ht := sample_count_upper_tail p (Finset.univ : Finset V)
      ((p : ℝ) * Fintype.card V / 60) (by positivity)
    have heq : {ω : V → Bool | (p : ℝ) * (Finset.univ : Finset V).card +
        (p : ℝ) * Fintype.card V / 60 ≤ ((Finset.univ ∩ sampleVertices ω).card : ℝ)} =
        {ω | 61 * (p : ℝ) * Fintype.card V / 60 ≤ (sampleVertices ω).card} := by
      simp only [Finset.card_univ,Finset.univ_inter]
      congr 1
      ext ω
      congr 1 <;> ring
    rw [heq, ← hlaw] at ht
    change ((μ.map (finalSample n)) _).toReal ≤ _ at ht
    rw [Measure.map_apply hmeas (by measurability)] at ht
    exact ht
  have hsub : {z | ((reservoirBall G U (sampleVertices (finalSample n z)) (n + 1)).card : ℝ) ≤
        (sampleVertices (finalSample n z)).card / (2 : ℝ)} ⊆
      ((A ×ˢ Set.univ) ×ˢ Set.univ) ∪ (B ×ˢ Set.univ) ∪ C := by
    intro z hz
    by_cases hAin : z.1.1 ∈ A
    · exact Or.inl (Or.inl ⟨⟨hAin,Set.mem_univ _⟩,Set.mem_univ _⟩)
    by_cases hBin : z.1 ∈ B
    · exact Or.inl (Or.inr ⟨hBin,Set.mem_univ _⟩)
    by_cases hCin : z ∈ C
    · exact Or.inr hCin
    have hlarge : 2 * (Fintype.card V : ℝ) / 3 ≤ (historyBall G U n z.1.1).card :=
      le_of_not_gt hAin
    have hhits : 31 * (p : ℝ) * Fintype.card V / 60 <
        ((historyBall G U n z.1.1 ∩ sampleVertices z.1.2).card : ℝ) :=
      lt_of_not_ge (fun hx => hBin ⟨hlarge,hx⟩)
    have hsize : ((sampleVertices (finalSample n z)).card : ℝ) <
        61 * (p : ℝ) * Fintype.card V / 60 := lt_of_not_ge hCin
    have hpath : ((historyBall G U n z.1.1 ∩ sampleVertices z.1.2).card : ℝ) ≤
        (reservoirBall G U (sampleVertices (finalSample n z)) (n + 1)).card := by
      exact_mod_cast Finset.card_le_card (terminal_ball_subset_final G U n z)
    change ((reservoirBall G U (sampleVertices (finalSample n z)) (n + 1)).card : ℝ) ≤
      (sampleVertices (finalSample n z)).card / (2 : ℝ) at hz
    have hpN : 0 ≤ (p : ℝ) * Fintype.card V := by positivity
    exact False.elim (by nlinarith)
  rw [← hlaw]
  change ((μ.map (finalSample n)) _).toReal ≤ _
  rw [Measure.map_apply hmeas (by measurability)]
  apply (measureReal_mono hsub (measure_ne_top _ _)).trans
  have hu1 := measureReal_union_le (μ := μ) ((A ×ˢ Set.univ) ×ˢ Set.univ) (B ×ˢ Set.univ)
  have hu2 := measureReal_union_le (μ := μ)
    (((A ×ˢ Set.univ) ×ˢ Set.univ) ∪ (B ×ˢ Set.univ)) C
  change _ ≤ n * b + 2 * c
  linarith

/-- Actual finite sampled-reservoir majority theorem. Its only hypotheses are
robust expansion, an affordable deletion set, and explicit scalar layer/growth
budgets. All graph alternatives, adaptive histories, independence, final sample
law, and original-edge path witnesses are constructed in the proof. -/
theorem sampled_reservoir_majority
    (L epsilon s : ℝ) (hL : 1 ≤ L) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset)
    (hB : 1 ≤ (exposedBall (G.deleteEdges F) U ∅ 1).card)
    (hF : (F.card : ℝ) ≤ s * (exposedBall (G.deleteEdges F) U ∅ 1).card / 4)
    (r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hs : 20 * (r : ℝ) * t ≤ s)
    (q d p : unitInterval) (hratio : 5 * (r : ℝ) ≤ 4 * (q : ℝ) * t)
    (hqr : (1 / 6 : ℝ) ≤ (q : ℝ) * r) (n : ℕ)
    (hd : (d : ℝ) = 4 * (p : ℝ) / 5)
    (hle : (unionDensity (historyDensity q n) d : ℝ) ≤ p)
    (hlt : (unionDensity (historyDensity q n) d : ℝ) < 1)
    (hbudget : 2 * (Fintype.card V : ℝ) / 3 ≤
      (1 + epsilon / (32 * L ^ 2)) ^ n * (exposedBall (G.deleteEdges F) U ∅ 1).card) :
    (sampleMeasure V p).real
      {ω | ((reservoirBall (G.deleteEdges F) U (sampleVertices ω) (n + 1)).card : ℝ) ≤
        (sampleVertices ω).card / (2 : ℝ)} ≤
      n * (exp (-(q : ℝ) * epsilon * (exposedBall (G.deleteEdges F) U ∅ 1).card /
          (160 * (r : ℝ) * L ^ 2)) +
        exp (-epsilon ^ 2 * (exposedBall (G.deleteEdges F) U ∅ 1).card /
          (8192 * (t : ℝ) ^ 2 * L ^ 4))) +
        2 * exp (-((p : ℝ) * Fintype.card V / 60) ^ 2 /
          (2 * (Fintype.card V : ℝ))) := by
  apply reservoir_majority_from_history_bound (G.deleteEdges F) U q d p n
    (epsilon / (32 * L ^ 2)) _ (by positivity) (by positivity) hd hle hlt hbudget
  exact actual_history_ball_small_probability G L epsilon s hL heps heps1 hG
    U F hFG hB hF r t hr ht hs q hratio hqr n hbudget

/-- Source-parameter supplier with concrete independent layer densities.
Only the transparent finite log-growth inequality remains in place of
sufficiently-large-n notation. The reservoir-budget hypothesis is the one used
by CJMM Lemma 7.2 and dominates the repaired natural rounding constants. -/
theorem source_parameter_reservoir_majority
    (p : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hL : 16 ≤ L)
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hs : ((p : ℝ)⁻¹) ^ 4 * L ^ 30 ≤ s)
    (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset)
    (hB : 1 ≤ (exposedBall (G.deleteEdges F) U ∅ 1).card)
    (hF : (F.card : ℝ) ≤ s * (exposedBall (G.deleteEdges F) U ∅ 1).card / 4)
    (n : ℕ) (hn : (n : ℝ) + 1 ≤ L ^ 4)
    (hlog : log (Fintype.card V) ≤ (n : ℝ) * (epsilon / (32 * L ^ 2)) / 2) :
    (sampleMeasure V p).real
      {ω | ((reservoirBall (G.deleteEdges F) U (sampleVertices ω) (n + 1)).card : ℝ) ≤
        (sampleVertices ω).card / (2 : ℝ)} ≤
      2 * n * exp (-epsilon ^ 2 * (p : ℝ) ^ 4 *
        (exposedBall (G.deleteEdges F) U ∅ 1).card / (32768 * L ^ 22)) +
        2 * exp (-((p : ℝ) * Fintype.card V / 60) ^ 2 /
          (2 * (Fintype.card V : ℝ))) := by
  let q := smallLayerDensity p n
  let d : unitInterval := ⟨4 * (p : ℝ) / 5, by
    constructor
    · positivity
    · nlinarith [p.property.2]⟩
  let a := epsilon / (32 * L ^ 2)
  let b := 2 * exp (-epsilon ^ 2 * (p : ℝ) ^ 4 *
    (exposedBall (G.deleteEdges F) U ∅ 1).card / (32768 * L ^ 22))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity : 0 < 32 * L ^ 2)).mpr
    nlinarith [sq_nonneg (L - 1)]
  have hN : 0 < Fintype.card V := by
    have hc := Finset.card_le_univ (exposedBall (G.deleteEdges F) U ∅ 1)
    omega
  have hbudget := scalar_growth_budget (Fintype.card V)
    (exposedBall (G.deleteEdges F) U ∅ 1).card n hN hB a ha ha1 hlog
  have hle := small_layer_density_budget p d n rfl
  have hlt : (unionDensity (historyDensity q n) d : ℝ) < 1 := hle.trans_lt hp1
  have hfixed : ∀ W : Finset V, exposedBall (G.deleteEdges F) U ∅ 1 ⊆ W →
      (W.card : ℝ) < 2 * (Fintype.card V : ℝ) / 3 →
      (sampleMeasure V q).real
        {ω | ((sampledHitBoundary (G.deleteEdges F) W (sampleVertices ω)).card : ℝ) <
          a * W.card} ≤ b := by
    intro W hBW hWsmall
    have hcard := Finset.card_le_card hBW
    have hcardR : ((exposedBall (G.deleteEdges F) U ∅ 1).card : ℝ) ≤ W.card := by
      exact_mod_cast hcard
    have hs0 : 0 ≤ s := (by positivity : 0 ≤ ((p : ℝ)⁻¹) ^ 4 * L ^ 30).trans hs
    have hFW : (F.card : ℝ) ≤ s * W.card / 4 := by
      have hm := mul_le_mul_of_nonneg_left hcardR hs0
      linarith
    have hstep := ReachabilityAlternative.reservoir_budget_one_step_growth G p q L epsilon s
      hp hL heps heps1 (small_layer_density_ge p n L (by linarith) hn) hs hG
      W (by omega) hWsmall.le F hFG hFW
    have hevent : {ω | ((sampledHitBoundary (G.deleteEdges F) W (sampleVertices ω)).card : ℝ) <
        a * W.card} = {ω | ((sampledHitBoundary (G.deleteEdges F) W (sampleVertices ω)).card : ℝ) <
          epsilon * W.card / (32 * L ^ 2)} := by
      dsimp [a]
      congr 1
      ext ω
      congr 1 <;> ring
    rw [hevent]
    apply hstep.trans
    dsimp [b]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hcardR
      (mul_nonneg (sq_nonneg epsilon) (pow_nonneg hp.le 4))]
  have hhistory := history_ball_small_probability (G.deleteEdges F) U q a
    (2 * (Fintype.card V : ℝ) / 3) b ha (by dsimp [b]; positivity) n hbudget hfixed
  have hmain := reservoir_majority_from_history_bound (G.deleteEdges F) U q d p n a b
    ha (by dsimp [b]; positivity) rfl hle hlt hbudget hhistory
  convert hmain using 1
  dsimp [b]
  ring

/-- Deleting one original edge can remove at most one external neighbor of a
fixed set. The proof injects each lost outside vertex into a distinct deleted
crossing edge. -/
theorem externalNeighbors_delete_card (U : Finset V) (F : Finset (Sym2 V)) :
    (externalNeighbors G U).card ≤ (externalNeighbors (G.deleteEdges F) U).card + F.card := by
  classical
  let D := externalNeighbors G U \ externalNeighbors (G.deleteEdges F) U
  have hex (v : {v // v ∈ D}) : ∃ u : V, u ∈ U ∧ G.Adj u v ∧ s(u,v.val) ∈ F := by
    have hvG := (Finset.mem_sdiff.mp v.property).1
    have hvJ := (Finset.mem_sdiff.mp v.property).2
    obtain ⟨hvout,u,hu,hGuv⟩ := (show v.val ∉ U ∧ ∃ u ∈ U, G.Adj u v.val from by
      simpa only [externalNeighbors,Finset.mem_filter,Finset.mem_compl] using hvG)
    refine ⟨u,hu,hGuv,?_⟩
    by_contra he
    apply hvJ
    simp only [externalNeighbors,Finset.mem_filter,Finset.mem_compl]
    exact ⟨hvout,u,hu,SimpleGraph.deleteEdges_adj.mpr ⟨hGuv,he⟩⟩
  let f : {v // v ∈ D} → {e // e ∈ F} := fun v =>
    ⟨s(Classical.choose (hex v),v.val),(Classical.choose_spec (hex v)).2.2⟩
  have hf : Function.Injective f := by
    intro v w heq
    have he : s(Classical.choose (hex v),v.val) = s(Classical.choose (hex w),w.val) :=
      congrArg Subtype.val heq
    apply Subtype.ext
    rcases Sym2.eq_iff.mp he with h | h
    · exact h.2
    · have hvG := (Finset.mem_sdiff.mp v.property).1
      have hvout : v.val ∉ U := by
        have hvtuple : v.val ∉ U ∧ ∃ u ∈ U, G.Adj u v.val := by
          simpa only [externalNeighbors,Finset.mem_filter,Finset.mem_compl] using hvG
        exact hvtuple.1
      exact False.elim (hvout (h.2.symm ▸ (Classical.choose_spec (hex w)).1))
  have hD : D.card ≤ F.card := by
    simpa using Fintype.card_le_of_injective f hf
  have hsub : externalNeighbors G U ⊆ externalNeighbors (G.deleteEdges F) U ∪ D := by
    intro v hv
    by_cases h : v ∈ externalNeighbors (G.deleteEdges F) U
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv,h⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

theorem seed_subset_exposedBall_one (U : Finset V) : U ⊆ exposedBall G U ∅ 1 := by
  intro u hu
  apply (mem_exposedBall G U ∅ 1 u).mpr
  exact ⟨u,hu,SimpleGraph.Walk.nil,by simp,by simp⟩

theorem neighbors_subset_exposedBall_one (U : Finset V) :
    externalNeighbors G U ⊆ exposedBall G U ∅ 1 := by
  intro v hv
  obtain ⟨hvout,u,hu,huv⟩ := (show v ∉ U ∧ ∃ u ∈ U, G.Adj u v from by
    simpa only [externalNeighbors,Finset.mem_filter,Finset.mem_compl] using hv)
  apply (mem_exposedBall G U ∅ 1 v).mpr
  exact ⟨u,hu,SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil,by simp,by simp⟩

/-- The source well-expansion threshold supplies the large deterministic first
ball even after every allowed original-edge deletion. -/
theorem well_expanding_initial_ball (p : unitInterval) (L : ℝ) (U : Finset V)
    (hW : WellExpandingAt G p L U) (F : Finset (Sym2 V)) (hF : F.card ≤ U.card)
    (hscale : 2 ≤ ((p : ℝ)⁻¹) ^ 4 * L ^ 24) :
    (U.card : ℝ) * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 / 2 ≤
      (exposedBall (G.deleteEdges F) U ∅ 1).card := by
  have hdel := externalNeighbors_delete_card G U F
  have hdelR : ((externalNeighbors G U).card : ℝ) ≤
      (externalNeighbors (G.deleteEdges F) U).card + F.card := by exact_mod_cast hdel
  have hFR : (F.card : ℝ) ≤ U.card := by exact_mod_cast hF
  have hball : ((externalNeighbors (G.deleteEdges F) U).card : ℝ) ≤
      (exposedBall (G.deleteEdges F) U ∅ 1).card := by
    exact_mod_cast Finset.card_le_card (neighbors_subset_exposedBall_one (G.deleteEdges F) U)
  have hscaled := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg U.card)
  dsimp [WellExpandingAt] at hW
  nlinarith

                                                                           
                                                                            
                                                      
theorem well_expanding_reservoir_majority
    (p : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hL : 16 ≤ L)
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hs : ((p : ℝ)⁻¹) ^ 4 * L ^ 30 ≤ s)
    (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (hU : U.Nonempty) (hW : WellExpandingAt G p L U)
    (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset) (hF : F.card ≤ U.card)
    (n : ℕ) (hn : (n : ℝ) + 1 ≤ L ^ 4)
    (hlog : log (Fintype.card V) ≤ (n : ℝ) * (epsilon / (32 * L ^ 2)) / 2) :
    (sampleMeasure V p).real
      {ω | ((reservoirBall (G.deleteEdges F) U (sampleVertices ω) (n + 1)).card : ℝ) ≤
        (sampleVertices ω).card / (2 : ℝ)} ≤
      2 * ((n : ℝ) + 1) * exp (-epsilon ^ 2 * U.card * L ^ 2 / 65536) := by
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hip : 1 ≤ (p : ℝ)⁻¹ := (one_le_inv₀ hp).mpr p.property.2
  have hip4 : (1 : ℝ) ≤ ((p : ℝ)⁻¹) ^ 4 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hip 4
  have hL24 : 2 ≤ L ^ 24 := by
    have hpow := pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 24)
    nlinarith [sq_nonneg (L - 16)]
  have hL30 : 4 ≤ L ^ 30 := by
    have hpow := pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 30)
    nlinarith [sq_nonneg (L - 16)]
  have hscale : 2 ≤ ((p : ℝ)⁻¹) ^ 4 * L ^ 24 := by
    nlinarith [mul_le_mul_of_nonneg_right hip4 (by positivity : 0 ≤ L ^ 24)]
  have hs4 : 4 ≤ s := by
    have hh := mul_le_mul_of_nonneg_right hip4 (by positivity : 0 ≤ L ^ 30)
    nlinarith
  have hUball := Finset.card_le_card (seed_subset_exposedBall_one (G.deleteEdges F) U)
  have hB : 1 ≤ (exposedBall (G.deleteEdges F) U ∅ 1).card := by
    have := hU.card_pos
    omega
  have hFbudget : (F.card : ℝ) ≤ s * (exposedBall (G.deleteEdges F) U ∅ 1).card / 4 := by
    have hFR : (F.card : ℝ) ≤ U.card := by exact_mod_cast hF
    have hUBR : (U.card : ℝ) ≤ (exposedBall (G.deleteEdges F) U ∅ 1).card := by
      exact_mod_cast hUball
    have hm := mul_le_mul_of_nonneg_right hs4
      (Nat.cast_nonneg (exposedBall (G.deleteEdges F) U ∅ 1).card)
    nlinarith
  have hmain := source_parameter_reservoir_majority G p L epsilon s hp hp1 hL heps heps1
    hs hG U F hFG hB hFbudget n hn hlog
  have hBlarge := well_expanding_initial_ball G p L U hW F hF hscale
  have hA : epsilon ^ 2 * U.card * L ^ 2 / 65536 ≤
      epsilon ^ 2 * (p : ℝ) ^ 4 * (exposedBall (G.deleteEdges F) U ∅ 1).card /
        (32768 * L ^ 22) := by
    calc
      _ = epsilon ^ 2 * (p : ℝ) ^ 4 *
          ((U.card : ℝ) * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 / 2) / (32768 * L ^ 22) := by
        field_simp
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hBlarge (by positivity)) (by positivity)
  have hNpos : (0 : ℝ) < Fintype.card V := by
    have hc := Finset.card_le_univ U
    exact_mod_cast (show 0 < Fintype.card V by have := hU.card_pos; omega)
  have hWorder : (U.card : ℝ) * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ Fintype.card V := by
    exact hW.trans (by exact_mod_cast Finset.card_le_univ (externalNeighbors G U))
  have hcancel : (p : ℝ) ^ 4 * ((U.card : ℝ) * ((p : ℝ)⁻¹) ^ 4 * L ^ 24) =
      (U.card : ℝ) * L ^ 24 := by
    field_simp
  have hUL : (U.card : ℝ) * L ^ 24 ≤ (p : ℝ) ^ 4 * Fintype.card V := by
    have hm := mul_le_mul_of_nonneg_left hWorder (pow_nonneg hp.le 4)
    simpa only [hcancel] using hm
  have hp4 : (p : ℝ) ^ 4 ≤ (p : ℝ) ^ 2 := by
    have hp2 : (p : ℝ) ^ 2 ≤ 1 := pow_le_one₀ p.property.1 p.property.2
    have hm := mul_nonneg (sq_nonneg (p : ℝ)) (sub_nonneg.mpr hp2)
    nlinarith only [hm]
  have hLpow := pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 24)
  have hsmall : (U.card : ℝ) * L ^ 2 ≤ (p : ℝ) ^ 2 * Fintype.card V :=
    ((mul_le_mul_of_nonneg_left hLpow (Nat.cast_nonneg U.card)).trans hUL).trans
      (mul_le_mul_of_nonneg_right hp4 (Nat.cast_nonneg _))
  have heps2 : epsilon ^ 2 ≤ 1 := by nlinarith only [heps,heps1]
  have hnum : epsilon ^ 2 * U.card * L ^ 2 ≤ (p : ℝ) ^ 2 * Fintype.card V := by
    have hm := mul_le_mul_of_nonneg_right heps2
      (show 0 ≤ (U.card : ℝ) * L ^ 2 by positivity)
    nlinarith only [hm,hsmall]
  have hC : epsilon ^ 2 * U.card * L ^ 2 / 65536 ≤
      ((p : ℝ) * Fintype.card V / 60) ^ 2 / (2 * (Fintype.card V : ℝ)) := by
    have heq : ((p : ℝ) * Fintype.card V / 60) ^ 2 / (2 * (Fintype.card V : ℝ)) =
        (p : ℝ) ^ 2 * Fintype.card V / 7200 := by
      field_simp
      ring
    rw [heq]
    exact div_le_div₀ (by positivity) hnum (by norm_num) (by norm_num)
  have hAe := exp_le_exp.mpr (neg_le_neg hA)
  have hCe := exp_le_exp.mpr (neg_le_neg hC)
  have hsum := add_le_add
    (mul_le_mul_of_nonneg_left hAe (by positivity : 0 ≤ 2 * (n : ℝ)))
    (mul_le_mul_of_nonneg_left hCe (by norm_num : (0 : ℝ) ≤ 2))
  apply hmain.trans
  convert hsum using 1 <;> simp only [neg_div,neg_mul] <;> ring

/-- Enough fresh transitions for the source radius, leaving at least one step
for the unrestricted endpoint and using less than L to the fourth steps. -/
noncomputable def growthSteps (L : ℝ) : ℕ := ⌊L ^ 4 / 2⌋₊

theorem growthSteps_parameters (N : ℕ) (L epsilon : ℝ)
    (hL : 16 ≤ L) (heps : 0 < epsilon) (hlarge : 256 ≤ epsilon * L)
    (hlog : log N ≤ L) :
    ((growthSteps L : ℝ) + 1 ≤ L ^ 4) ∧
      log N ≤ (growthSteps L : ℝ) * (epsilon / (32 * L ^ 2)) / 2 := by
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL4 : 4 ≤ L ^ 4 := by
    have hh := pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 4)
    nlinarith only [hh,hL,sq_nonneg (L - 16)]
  have hup : (growthSteps L : ℝ) ≤ L ^ 4 / 2 := Nat.floor_le (by positivity)
  have hlo : L ^ 4 / 4 ≤ (growthSteps L : ℝ) := by
    have hh := Nat.lt_floor_add_one (L ^ 4 / 2)
    change L ^ 4 / 2 < (growthSteps L : ℝ) + 1 at hh
    linarith
  constructor
  · linarith
  · apply hlog.trans
    have heq : (growthSteps L : ℝ) * (epsilon / (32 * L ^ 2)) / 2 =
        ((growthSteps L : ℝ) * epsilon) / (64 * L ^ 2) := by ring
    rw [heq]
    apply (le_div_iff₀ (by positivity : 0 < 64 * L ^ 2)).mpr
    have hm1 := mul_le_mul_of_nonneg_right hlarge (pow_nonneg hLp.le 3)
    have hm2 := mul_le_mul_of_nonneg_left hlo heps.le
    nlinarith only [hm1,hm2]

/-- Fully explicit logarithmic fixed-pair supplier. The original-edge radius
is at most L to the fourth, and failure is at most 2 L^4 times the source
exp(-constant * epsilon^2 * |U| * L^2) bound. -/
theorem well_expanding_reservoir_logarithmic
    (p : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hL : 16 ≤ L)
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hlarge : 256 ≤ epsilon * L) (hlog : log (Fintype.card V) ≤ L)
    (hs : ((p : ℝ)⁻¹) ^ 4 * L ^ 30 ≤ s)
    (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (hU : U.Nonempty) (hW : WellExpandingAt G p L U)
    (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset) (hF : F.card ≤ U.card) :
    (growthSteps L : ℝ) + 1 ≤ L ^ 4 ∧
      (sampleMeasure V p).real
        {ω | ((reservoirBall (G.deleteEdges F) U (sampleVertices ω) (growthSteps L + 1)).card : ℝ) ≤
          (sampleVertices ω).card / (2 : ℝ)} ≤
        2 * L ^ 4 * exp (-epsilon ^ 2 * U.card * L ^ 2 / 65536) := by
  obtain ⟨hn,hbudget⟩ := growthSteps_parameters (Fintype.card V) L epsilon hL heps hlarge hlog
  refine ⟨hn,?_⟩
  apply (well_expanding_reservoir_majority G p L epsilon s hp hp1 hL heps heps1 hs hG
    U hU hW F hFG hF (growthSteps L) hn hbudget).trans
  apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
  linarith

/-- The edge-partition piece budget pays for all natural rounding constants. -/
theorem weak_budget_pays_source_budget (p : unitInterval) (L : ℝ)
    (hp : 0 < (p : ℝ)) (hL : 16 ≤ L) :
    80 * ((p : ℝ)⁻¹) ^ 3 * L ^ 13 ≤ 20 * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 := by
  have hL1 : 1 ≤ L := by linarith
  have hpow := pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 11)
  have hbig : 4 * (p : ℝ) ≤ L ^ 11 := by
    nlinarith only [hpow,hL,p.property.2]
  calc
    _ = (4 * (p : ℝ)) * (20 * ((p : ℝ)⁻¹) ^ 4 * L ^ 13) := by
      field_simp
      ring
    _ ≤ L ^ 11 * (20 * ((p : ℝ)⁻¹) ^ 4 * L ^ 13) :=
      mul_le_mul_of_nonneg_right hbig (by positivity)
    _ = _ := by ring

/-- Concrete-layer fixed-pair adapter under the edge-partition piece budget. -/
theorem source_parameter_reservoir_majority_weak_budget
    (p : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hL : 16 ≤ L)
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hs : 20 * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ s)
    (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset)
    (hB : 1 ≤ (exposedBall (G.deleteEdges F) U ∅ 1).card)
    (hF : (F.card : ℝ) ≤ s * (exposedBall (G.deleteEdges F) U ∅ 1).card / 4)
    (n : ℕ) (hn : (n : ℝ) + 1 ≤ L ^ 4)
    (hlog : log (Fintype.card V) ≤ (n : ℝ) * (epsilon / (32 * L ^ 2)) / 2) :
    (sampleMeasure V p).real
      {ω | ((reservoirBall (G.deleteEdges F) U (sampleVertices ω) (n + 1)).card : ℝ) ≤
        (sampleVertices ω).card / (2 : ℝ)} ≤
      2 * n * exp (-epsilon ^ 2 * (p : ℝ) ^ 4 *
        (exposedBall (G.deleteEdges F) U ∅ 1).card / (32768 * L ^ 22)) +
        2 * exp (-((p : ℝ) * Fintype.card V / 60) ^ 2 /
          (2 * (Fintype.card V : ℝ))) := by
  let q := smallLayerDensity p n
  let d : unitInterval := ⟨4 * (p : ℝ) / 5, by
    constructor
    · positivity
    · nlinarith [p.property.2]⟩
  let a := epsilon / (32 * L ^ 2)
  let b := 2 * exp (-epsilon ^ 2 * (p : ℝ) ^ 4 *
    (exposedBall (G.deleteEdges F) U ∅ 1).card / (32768 * L ^ 22))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity : 0 < 32 * L ^ 2)).mpr
    nlinarith [sq_nonneg (L - 1)]
  have hN : 0 < Fintype.card V := by
    have hc := Finset.card_le_univ (exposedBall (G.deleteEdges F) U ∅ 1)
    omega
  have hbudget := scalar_growth_budget (Fintype.card V)
    (exposedBall (G.deleteEdges F) U ∅ 1).card n hN hB a ha ha1 hlog
  have hle := small_layer_density_budget p d n rfl
  have hlt : (unionDensity (historyDensity q n) d : ℝ) < 1 := hle.trans_lt hp1
  have hfixed : ∀ W : Finset V, exposedBall (G.deleteEdges F) U ∅ 1 ⊆ W →
      (W.card : ℝ) < 2 * (Fintype.card V : ℝ) / 3 →
      (sampleMeasure V q).real
        {ω | ((sampledHitBoundary (G.deleteEdges F) W (sampleVertices ω)).card : ℝ) <
          a * W.card} ≤ b := by
    intro W hBW hWsmall
    have hcard := Finset.card_le_card hBW
    have hcardR : ((exposedBall (G.deleteEdges F) U ∅ 1).card : ℝ) ≤ W.card := by
      exact_mod_cast hcard
    have hs0 : 0 ≤ s := (by positivity : 0 ≤ 20 * ((p : ℝ)⁻¹) ^ 4 * L ^ 24).trans hs
    have hFW : (F.card : ℝ) ≤ s * W.card / 4 := by
      have hm := mul_le_mul_of_nonneg_left hcardR hs0
      linarith
    have hstep := ReachabilityAlternative.source_one_step_boundary_growth G p q L epsilon s
      hp hL heps heps1 (small_layer_density_ge p n L (by linarith) hn)
      ((weak_budget_pays_source_budget p L hp hL).trans hs) hG
      W (by omega) hWsmall.le F hFG hFW
    have hevent : {ω | ((sampledHitBoundary (G.deleteEdges F) W (sampleVertices ω)).card : ℝ) <
        a * W.card} = {ω | ((sampledHitBoundary (G.deleteEdges F) W (sampleVertices ω)).card : ℝ) <
          epsilon * W.card / (32 * L ^ 2)} := by
      dsimp [a]
      congr 1
      ext ω
      congr 1 <;> ring
    rw [hevent]
    apply hstep.trans
    dsimp [b]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hcardR
      (mul_nonneg (sq_nonneg epsilon) (pow_nonneg hp.le 4))]
  have hhistory := history_ball_small_probability (G.deleteEdges F) U q a
    (2 * (Fintype.card V : ℝ) / 3) b ha (by dsimp [b]; positivity) n hbudget hfixed
  have hmain := reservoir_majority_from_history_bound (G.deleteEdges F) U q d p n a b
    ha (by dsimp [b]; positivity) rfl hle hlt hbudget hhistory
  convert hmain using 1
  dsimp [b]
  ring


/-- Actual well-seed adapter under the edge-partition piece budget. -/
theorem well_expanding_reservoir_majority_weak_budget
    (p : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hL : 16 ≤ L)
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hs : 20 * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ s)
    (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (hU : U.Nonempty) (hW : WellExpandingAt G p L U)
    (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset) (hF : F.card ≤ U.card)
    (n : ℕ) (hn : (n : ℝ) + 1 ≤ L ^ 4)
    (hlog : log (Fintype.card V) ≤ (n : ℝ) * (epsilon / (32 * L ^ 2)) / 2) :
    (sampleMeasure V p).real
      {ω | ((reservoirBall (G.deleteEdges F) U (sampleVertices ω) (n + 1)).card : ℝ) ≤
        (sampleVertices ω).card / (2 : ℝ)} ≤
      2 * ((n : ℝ) + 1) * exp (-epsilon ^ 2 * U.card * L ^ 2 / 65536) := by
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hip : 1 ≤ (p : ℝ)⁻¹ := (one_le_inv₀ hp).mpr p.property.2
  have hip4 : (1 : ℝ) ≤ ((p : ℝ)⁻¹) ^ 4 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hip 4
  have hL24 : 2 ≤ L ^ 24 := by
    have hpow := pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 24)
    nlinarith [sq_nonneg (L - 16)]
  have hL30 : 4 ≤ L ^ 30 := by
    have hpow := pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 30)
    nlinarith [sq_nonneg (L - 16)]
  have hscale : 2 ≤ ((p : ℝ)⁻¹) ^ 4 * L ^ 24 := by
    nlinarith [mul_le_mul_of_nonneg_right hip4 (by positivity : 0 ≤ L ^ 24)]
  have hs4 : 4 ≤ s := by nlinarith only [hs,hscale]
  have hUball := Finset.card_le_card (seed_subset_exposedBall_one (G.deleteEdges F) U)
  have hB : 1 ≤ (exposedBall (G.deleteEdges F) U ∅ 1).card := by
    have := hU.card_pos
    omega
  have hFbudget : (F.card : ℝ) ≤ s * (exposedBall (G.deleteEdges F) U ∅ 1).card / 4 := by
    have hFR : (F.card : ℝ) ≤ U.card := by exact_mod_cast hF
    have hUBR : (U.card : ℝ) ≤ (exposedBall (G.deleteEdges F) U ∅ 1).card := by
      exact_mod_cast hUball
    have hm := mul_le_mul_of_nonneg_right hs4
      (Nat.cast_nonneg (exposedBall (G.deleteEdges F) U ∅ 1).card)
    nlinarith
  have hmain := source_parameter_reservoir_majority_weak_budget G p L epsilon s hp hp1 hL heps heps1
    hs hG U F hFG hB hFbudget n hn hlog
  have hBlarge := well_expanding_initial_ball G p L U hW F hF hscale
  have hA : epsilon ^ 2 * U.card * L ^ 2 / 65536 ≤
      epsilon ^ 2 * (p : ℝ) ^ 4 * (exposedBall (G.deleteEdges F) U ∅ 1).card /
        (32768 * L ^ 22) := by
    calc
      _ = epsilon ^ 2 * (p : ℝ) ^ 4 *
          ((U.card : ℝ) * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 / 2) / (32768 * L ^ 22) := by
        field_simp
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hBlarge (by positivity)) (by positivity)
  have hNpos : (0 : ℝ) < Fintype.card V := by
    have hc := Finset.card_le_univ U
    exact_mod_cast (show 0 < Fintype.card V by have := hU.card_pos; omega)
  have hWorder : (U.card : ℝ) * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ Fintype.card V := by
    exact hW.trans (by exact_mod_cast Finset.card_le_univ (externalNeighbors G U))
  have hcancel : (p : ℝ) ^ 4 * ((U.card : ℝ) * ((p : ℝ)⁻¹) ^ 4 * L ^ 24) =
      (U.card : ℝ) * L ^ 24 := by
    field_simp
  have hUL : (U.card : ℝ) * L ^ 24 ≤ (p : ℝ) ^ 4 * Fintype.card V := by
    have hm := mul_le_mul_of_nonneg_left hWorder (pow_nonneg hp.le 4)
    simpa only [hcancel] using hm
  have hp4 : (p : ℝ) ^ 4 ≤ (p : ℝ) ^ 2 := by
    have hp2 : (p : ℝ) ^ 2 ≤ 1 := pow_le_one₀ p.property.1 p.property.2
    have hm := mul_nonneg (sq_nonneg (p : ℝ)) (sub_nonneg.mpr hp2)
    nlinarith only [hm]
  have hLpow := pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 24)
  have hsmall : (U.card : ℝ) * L ^ 2 ≤ (p : ℝ) ^ 2 * Fintype.card V :=
    ((mul_le_mul_of_nonneg_left hLpow (Nat.cast_nonneg U.card)).trans hUL).trans
      (mul_le_mul_of_nonneg_right hp4 (Nat.cast_nonneg _))
  have heps2 : epsilon ^ 2 ≤ 1 := by nlinarith only [heps,heps1]
  have hnum : epsilon ^ 2 * U.card * L ^ 2 ≤ (p : ℝ) ^ 2 * Fintype.card V := by
    have hm := mul_le_mul_of_nonneg_right heps2
      (show 0 ≤ (U.card : ℝ) * L ^ 2 by positivity)
    nlinarith only [hm,hsmall]
  have hC : epsilon ^ 2 * U.card * L ^ 2 / 65536 ≤
      ((p : ℝ) * Fintype.card V / 60) ^ 2 / (2 * (Fintype.card V : ℝ)) := by
    have heq : ((p : ℝ) * Fintype.card V / 60) ^ 2 / (2 * (Fintype.card V : ℝ)) =
        (p : ℝ) ^ 2 * Fintype.card V / 7200 := by
      field_simp
      ring
    rw [heq]
    exact div_le_div₀ (by positivity) hnum (by norm_num) (by norm_num)
  have hAe := exp_le_exp.mpr (neg_le_neg hA)
  have hCe := exp_le_exp.mpr (neg_le_neg hC)
  have hsum := add_le_add
    (mul_le_mul_of_nonneg_left hAe (by positivity : 0 ≤ 2 * (n : ℝ)))
    (mul_le_mul_of_nonneg_left hCe (by norm_num : (0 : ℝ) ≤ 2))
  apply hmain.trans
  convert hsum using 1 <;> simp only [neg_div,neg_mul] <;> ring


/-- Logarithmic fixed-pair adapter under the edge-partition piece budget. -/
theorem well_expanding_reservoir_logarithmic_weak_budget
    (p : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hL : 16 ≤ L)
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hlarge : 256 ≤ epsilon * L) (hlog : log (Fintype.card V) ≤ L)
    (hs : 20 * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ s)
    (hG : RobustExpanderAt G L epsilon s)
    (U : Finset V) (hU : U.Nonempty) (hW : WellExpandingAt G p L U)
    (F : Finset (Sym2 V)) (hFG : F ⊆ G.edgeFinset) (hF : F.card ≤ U.card) :
    (growthSteps L : ℝ) + 1 ≤ L ^ 4 ∧
      (sampleMeasure V p).real
        {ω | ((reservoirBall (G.deleteEdges F) U (sampleVertices ω) (growthSteps L + 1)).card : ℝ) ≤
          (sampleVertices ω).card / (2 : ℝ)} ≤
        2 * L ^ 4 * exp (-epsilon ^ 2 * U.card * L ^ 2 / 65536) := by
  obtain ⟨hn,hbudget⟩ := growthSteps_parameters (Fintype.card V) L epsilon hL heps hlarge hlog
  refine ⟨hn,?_⟩
  apply (well_expanding_reservoir_majority_weak_budget G p L epsilon s hp hp1 hL heps heps1 hs hG
    U hU hW F hFG hF (growthSteps L) hn hbudget).trans
  apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
  linarith

end Erdos585.Attempt6.ReservoirGrowth
