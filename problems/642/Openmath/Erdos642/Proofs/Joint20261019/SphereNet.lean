import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Data.Nat.Find

namespace Erdos642.Joint20261019.SphereNet
open Metric Set Module MeasureTheory
open scoped ENNReal Topology

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open scoped Function in
/-- Volume packing at arbitrary scale, with no coordinate-dependent entropy. -/
theorem packing_bound (s : Finset E) (δ : ℝ) (hδ : 0 < δ)
    (hs : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ ‖x-y‖) :
    (s.card : ℝ) ≤ (1+2/δ)^finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let a := δ/2
  let b := 1+δ/2
  have ha : 0<a := by dsimp [a]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  let U := ⋃ x ∈ s, ball (x : E) a
  have hdis : Set.Pairwise (s : Set E) (Disjoint on fun x => ball (x : E) a) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    simpa [a] using hsep x hx y hy hxy
  have hsub : U ⊆ ball (0 : E) b := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    simpa [b,dist_zero_right,a,add_comm] using add_le_add_left (hs x hx) a
  have hi : (s.card : ℝ≥0∞)*ENNReal.ofReal (a^finrank ℝ E)*μ (ball 0 1) ≤
      ENNReal.ofReal (b^finrank ℝ E)*μ (ball 0 1) := calc
    _ = μ U := by
      rw [show U=⋃x∈s,ball (x:E) a from rfl, measure_biUnion_finset hdis fun _ _ => measurableSet_ball]
      simp only [μ.addHaar_ball_of_pos _ ha,Finset.sum_const,nsmul_eq_mul,mul_assoc]
    _ ≤ μ (ball (0:E) b) := measure_mono hsub
    _ = _ := μ.addHaar_ball_of_pos _ hb
  have hj : (s.card : ℝ≥0∞)*ENNReal.ofReal (a^finrank ℝ E) ≤ ENNReal.ofReal (b^finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 hi
  have hk : (s.card : ℝ)*a^finrank ℝ E ≤ b^finrank ℝ E := by
    have hh := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hb.le _) hj
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal (pow_nonneg ha.le _)] using hh
  have hratio : b/a=1+2/δ := by dsimp [a,b]; field_simp; ring
  calc
    _ ≤ b^finrank ℝ E/a^finrank ℝ E := (le_div_iff₀ (pow_pos ha _)).mpr hk
    _ = (b/a)^finrank ℝ E := (div_pow _ _ _).symm
    _ = _ := by rw [hratio]

                                                                                      
theorem exists_net (δ : ℝ) (hδ : 0<δ) :
    ∃ W : Finset E, (∀ w∈W, ‖w‖=1) ∧
      (∀ v:E, ‖v‖=1 → ∃ w∈W, ‖v-w‖≤δ) ∧
      (W.card : ℝ) ≤ (1+2/δ)^finrank ℝ E := by
  classical
  let P : ℕ → Prop := fun n => ∃ W:Finset E, W.card=n ∧ (∀ w∈W, ‖w‖=1) ∧
    ∀ x∈W, ∀ y∈W, x≠y → δ≤‖x-y‖
  let B := ⌈(1+2/δ)^finrank ℝ E⌉₊
  have hP0 : P 0 := ⟨∅,by simp⟩
  have hmax := Nat.findGreatest_spec (P:=P) (Nat.zero_le B) hP0
  obtain ⟨W,hcard,hunit,hsep⟩ := hmax
  have hbound := packing_bound W δ hδ (fun x hx => (hunit x hx).le) hsep
  refine ⟨W,hunit,?_,hbound⟩
  intro v hv
  by_contra! hfar
  have hvnot : v∉W := by
    intro hvW
    have hh := hfar v hvW
    simp at hh
    linarith
  have hunit' : ∀ w∈insert v W, ‖w‖=1 := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|hw
    · exact hv
    · exact hunit w hw
  have hsep' : ∀ x∈insert v W, ∀ y∈insert v W, x≠y → δ≤‖x-y‖ := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with hxeq|hxW
    · subst x
      rcases Finset.mem_insert.mp hy with rfl|hy
      · exact (hxy rfl).elim
      · exact (hfar y hy).le
    · rcases Finset.mem_insert.mp hy with hyeq|hyW
      · subst y
        simpa [norm_sub_rev] using (hfar x hxW).le
      · exact hsep x hxW y hyW hxy
  have hnewbound := packing_bound (insert v W) δ hδ (fun x hx => (hunit' x hx).le) hsep'
  have hnatbound : (insert v W).card ≤ B := by
    exact_mod_cast hnewbound.trans (Nat.le_ceil _)
  have hnew : P (insert v W).card := ⟨insert v W,rfl,hunit',hsep'⟩
  have hh := Nat.le_findGreatest hnatbound hnew
  rw [Finset.card_insert_of_notMem hvnot,hcard] at hh
  omega

/-- Resolution μ/32 costs only a fixed base to the dimension. -/
theorem exists_mu_net (μ : ℝ) (hμ : 0<μ) (hμ1 : μ≤1) :
    ∃ W : Finset E, (∀ w∈W, ‖w‖=1) ∧
      (∀ v:E, ‖v‖=1 → ∃ w∈W, ‖v-w‖≤μ/32) ∧
      (W.card : ℝ) ≤ (65/μ)^finrank ℝ E := by
  obtain ⟨W,hw,hcover,hcard⟩ := exists_net (E:=E) (μ/32) (by positivity)
  refine ⟨W,hw,hcover,hcard.trans ?_⟩
  apply pow_le_pow_left₀ (by positivity)
  apply (le_div_iff₀ hμ).mpr
  field_simp
  nlinarith

end
end Erdos642.Joint20261019.SphereNet
