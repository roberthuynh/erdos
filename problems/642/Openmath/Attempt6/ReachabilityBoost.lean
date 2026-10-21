import Openmath.Attempt6.UniformReachability
import Openmath.Attempt6.EdgePartition

namespace Erdos585.Attempt6.ReachabilityBoost
open SimpleGraph MeasureTheory Real
open RobustCore Reachability SampledReachability UniformReachability
open OAI.ErdosGallai.Sampling

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem reachable_mono_budget (G : SimpleGraph V) (Q : Finset V) (r : ℕ)
    {a b : ℝ} (hab : a ≤ b) (h : ReservoirReachableAt G Q r b) :
    ReservoirReachableAt G Q r a := by
  classical
  intro U hU F hFG hF
  apply h U hU F hFG
  exact hF.trans (mul_le_mul_of_nonneg_right hab (by positivity))

theorem edge_family_failure_bound (G : SimpleGraph V) {k : ℕ}
    (H : Fin k → SimpleGraph V) [∀ i, DecidableRel (H i).Adj] (hHG : ∀ i, H i ≤ G)
    (hdisj : Pairwise fun i j => Disjoint (H i).edgeFinset (H j).edgeFinset)
    (hk : 0 < k) (p : unitInterval) (r : ℕ) (a b : ℝ)
    (hpiece : ∀ i, (sampleMeasure V p).real
      {omega | ¬ ReservoirReachableAt (H i) (sampleVertices omega) r a} ≤ b) :
    (sampleMeasure V p).real
      {omega | ¬ ReservoirReachableAt G (sampleVertices omega) r ((k : ℝ) * a)} ≤
        (k : ℝ) * b := by
  classical
  let E : Fin k → Set (V → Bool) := fun i =>
    {omega | ¬ ReservoirReachableAt (H i) (sampleVertices omega) r a}
  have hsub : {omega | ¬ ReservoirReachableAt G (sampleVertices omega) r ((k : ℝ) * a)}
      ⊆ ⋃ i, E i := by
    intro omega hbad
    by_contra hnone
    have hall : ∀ i, ReservoirReachableAt (H i) (sampleVertices omega) r a := by
      intro i
      by_contra hi
      exact hnone (Set.mem_iUnion.mpr ⟨i, hi⟩)
    exact hbad (uniform_reachability_of_edge_disjoint_family G H hHG hdisj
      (sampleVertices omega) r a hk hall)
  calc
    _ ≤ (sampleMeasure V p).real (⋃ i, E i) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i, (sampleMeasure V p).real (E i) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _i : Fin k, b := Finset.sum_le_sum (fun i _ => hpiece i)
    _ = (k : ℝ) * b := by simp

theorem weak_piece_failure (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hL : (10 : ℝ) ^ 30 ≤ L) (heps : (1 / 128 : ℝ) ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hN : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hs : 20 * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ s)
    (hG : RobustExpanderAt G L epsilon s) :
    (sampleMeasure V p).real {omega | ¬ ReservoirReachableAt G
      (sampleVertices omega) ⌊L ^ 4⌋₊ ((p : ℝ) ^ 4 / (1536 * L ^ 27))} ≤
        1 / (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hg := uniform_arbitrary_good_probability_floor G p L epsilon s
    hp hp1 hL heps heps1 hN hlog hs hG
  let A : Set (V → Bool) := {omega | ReservoirReachableAt G
    (sampleVertices omega) ⌊L ^ 4⌋₊ ((p : ℝ) ^ 4 / (1536 * L ^ 27))}
  have hgood : 1 - 1 / (Fintype.card V : ℝ) ^ 2 ≤ (sampleMeasure V p).real A := by
    apply hg.trans
    apply measureReal_mono _ (measure_ne_top _ _)
    intro omega ho U hU F hFG hF
    apply ho U hU F (by
      intro e he
      simpa only [SimpleGraph.mem_edgeFinset] using hFG he)
    convert hF using 1 <;> ring
  change (sampleMeasure V p).real Aᶜ ≤ _
  rw [measureReal_compl MeasurableSet.of_discrete, probReal_univ]
  linarith

theorem boosted_failure_of_partition (G : SimpleGraph V) {k : ℕ}
    (H : Fin k → SimpleGraph V) [∀ i, DecidableRel (H i).Adj] (hHG : ∀ i, H i ≤ G)
    (hdisj : Pairwise fun i j => Disjoint (H i).edgeFinset (H j).edgeFinset)
    (hk : 0 < k) (p : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hL : (10 : ℝ) ^ 30 ≤ L) (heps : (1 / 128 : ℝ) ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hN : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hs : 20 * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ s)
    (hH : ∀ i, RobustExpanderAt (H i) L epsilon s) :
    (sampleMeasure V p).real {omega | ¬ ReservoirReachableAt G
      (sampleVertices omega) ⌊L ^ 4⌋₊ ((k : ℝ) * ((p : ℝ) ^ 4 / (1536 * L ^ 27)))} ≤
        (k : ℝ) / (Fintype.card V : ℝ) ^ 2 := by
  classical
  simpa only [mul_one_div] using edge_family_failure_bound G H hHG hdisj hk p
    ⌊L ^ 4⌋₊ ((p : ℝ) ^ 4 / (1536 * L ^ 27)) (1 / (Fintype.card V : ℝ) ^ 2)
    (fun i => weak_piece_failure (H i) p L epsilon s hp hp1 hL heps heps1 hN hlog hs (hH i))

theorem partition_scalar_budgets (p L s : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hL : (10 : ℝ) ^ 30 ≤ L) (hs : p⁻¹ ^ 4 * L ^ 30 ≤ s) :
    let k := ⌊p ^ 4 * s / L ^ 30⌋₊
    0 < k ∧ (k : ℝ) ≤ s ∧
      1048576 * L ^ 3 ≤ (1 / 32 : ℝ) * s / k ∧
      20 * p⁻¹ ^ 4 * L ^ 24 ≤
        ((1 / 32 : ℝ) * s / (1048576 * (k : ℝ) * L ^ 2)) ∧
      p ^ 8 * s / L ^ 60 ≤ (k : ℝ) * (p ^ 4 / (1536 * L ^ 27)) := by
  dsimp only
  let k := ⌊p ^ 4 * s / L ^ 30⌋₊
  have hL1 : 1 ≤ L := by norm_num at hL; linarith
  have hLp : 0 < L := by linarith
  have hsp : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hp4 : p ^ 4 ≤ 1 := pow_le_one₀ hp.le hp1
  have hsprod : L ^ 30 ≤ p ^ 4 * s := by
    calc
      L ^ 30 = p ^ 4 * (p⁻¹ ^ 4 * L ^ 30) := by field_simp
      _ ≤ p ^ 4 * s := mul_le_mul_of_nonneg_left hs (by positivity)
  have hx1 : 1 ≤ p ^ 4 * s / L ^ 30 := (le_div_iff₀ (by positivity)).mpr (by simpa using hsprod)
  have hk1 : 1 ≤ k := Nat.le_floor (by simpa using hx1)
  have hkp : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkfloor : (k : ℝ) ≤ p ^ 4 * s / L ^ 30 := Nat.floor_le (by positivity)
  have hkprod : (k : ℝ) * L ^ 30 ≤ p ^ 4 * s := (le_div_iff₀ (by positivity)).mp hkfloor
  have hks : (k : ℝ) ≤ s := by
    have hL30 : 1 ≤ L ^ 30 := one_le_pow₀ hL1
    nlinarith [mul_le_mul_of_nonneg_right hp4 hsp.le]
  have hhalf : p ^ 4 * s / (2 * L ^ 30) ≤ (k : ℝ) := by
    have hx := Nat.lt_floor_add_one (p ^ 4 * s / L ^ 30)
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hx2 : p ^ 4 * s / L ^ 30 ≤ 2 * (k : ℝ) := by dsimp [k] at *; linarith
    calc
      _ = (p ^ 4 * s / L ^ 30) / 2 := by ring
      _ ≤ _ := by linarith
  have hpower (m : ℕ) (hm : 1 ≤ m) : L ≤ L ^ m := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 hm
  have h27 : 33554432 ≤ L ^ 27 := by have := hpower 27 (by norm_num); norm_num at hL; linarith
  have h4 : 671088640 ≤ L ^ 4 := by have := hpower 4 (by norm_num); norm_num at hL; linarith
  have h3 : 3072 ≤ L ^ 3 := by have := hpower 3 (by norm_num); norm_num at hL; linarith
  have hsplit27 : L ^ 30 = L ^ 3 * L ^ 27 := by ring
  have hsplit4 : L ^ 30 = L ^ 26 * L ^ 4 := by ring
  refine ⟨by omega, hks, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hkp).mpr
    have hcoef := mul_le_mul_of_nonneg_left h27 (by positivity : 0 ≤ (k : ℝ) * L ^ 3)
    have hpS := mul_le_mul_of_nonneg_right hp4 hsp.le
    rw [hsplit27] at hkprod
    nlinarith
  · apply (le_div_iff₀ (by positivity : 0 < 1048576 * (k : ℝ) * L ^ 2)).mpr
    have hcoef := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ (k : ℝ) * L ^ 26)
    have hc : 671088640 * (k : ℝ) * L ^ 26 ≤ p ^ 4 * s := by
      rw [hsplit4] at hkprod
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ p⁻¹ ^ 4)
    have hcanc : p⁻¹ ^ 4 * (p ^ 4 * s) = s := by field_simp
    rw [hcanc] at hm
    nlinarith [show L ^ 24 * L ^ 2 = L ^ 26 by ring]
  · have hc : 3072 * L ^ 57 ≤ L ^ 60 := by
      have hm := mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ L ^ 57)
      nlinarith [show L ^ 3 * L ^ 57 = L ^ 60 by ring]
    calc
      p ^ 8 * s / L ^ 60 ≤ p ^ 8 * s / (3072 * L ^ 57) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hc
      _ = (p ^ 4 * s / (2 * L ^ 30)) * (p ^ 4 / (1536 * L ^ 27)) := by
        field_simp
        <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hhalf (by positivity)

theorem original_graph_reservoir_failure (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (L s : ℝ) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hL : (10 : ℝ) ^ 30 ≤ L) (hN : 2 ≤ Fintype.card V)
    (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hs : ((p : ℝ)⁻¹) ^ 4 * L ^ 30 ≤ s)
    (hG : RobustExpanderAt G L (1 / 32) s) :
    (sampleMeasure V p).real {omega | ¬ ReservoirReachableAt G
      (sampleVertices omega) ⌊L ^ 4⌋₊ ((p : ℝ) ^ 8 * s / L ^ 60)} ≤
        1 / (Fintype.card V : ℝ) := by
  classical
  let k := ⌊(p : ℝ) ^ 4 * s / L ^ 30⌋₊
  obtain ⟨hk, hks, hpart, hpiece, hbudget⟩ :=
    partition_scalar_budgets (p : ℝ) L s hp hp1.le hL hs
  change 0 < k at hk
  have hk1 : 1 ≤ k := hk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hs1 : 1 ≤ s := hkR.trans hks
  have hL1 : 1 ≤ L := by norm_num at hL; linarith
  obtain ⟨H, hHG, hdisj, _hcover, hH⟩ :=
    EdgePartition.edge_partition_exists_lattice G k hk1 L (1 / 32) s hG hN hlog
      hL1 (by norm_num) (by norm_num) hs1 hpart
  have hdisjF : Pairwise fun i j => Disjoint (H i).edgeFinset (H j).edgeFinset := by
    intro i j hij
    exact SimpleGraph.disjoint_edgeFinset.mpr (hdisj hij)
  have hHH : ∀ i, RobustExpanderAt (H i) L (1 / 128)
      ((1 / 32 : ℝ) * s / (1048576 * (k : ℝ) * L ^ 2)) := by
    intro i
    convert hH i using 1 <;> norm_num
  have hb := boosted_failure_of_partition G H hHG hdisjF hk p L (1 / 128)
    ((1 / 32 : ℝ) * s / (1048576 * (k : ℝ) * L ^ 2))
    hp hp1 hL (by norm_num) (by norm_num) hN hlog hpiece hHH
  have hsub : {omega | ¬ ReservoirReachableAt G (sampleVertices omega) ⌊L ^ 4⌋₊
      ((p : ℝ) ^ 8 * s / L ^ 60)} ⊆
      {omega | ¬ ReservoirReachableAt G (sampleVertices omega) ⌊L ^ 4⌋₊
        ((k : ℝ) * ((p : ℝ) ^ 4 / (1536 * L ^ 27)))} := by
    intro omega ho hbigger
    exact ho (reachable_mono_budget G (sampleVertices omega) ⌊L ^ 4⌋₊ hbudget hbigger)
  apply (measureReal_mono hsub (measure_ne_top _ _)).trans
  apply hb.trans
  have hNs : s < Fintype.card V :=
    EdgePartition.robustness_lt_order G L (1 / 32) s hG hN (by linarith) (by norm_num)
  have hNp : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hkN : (k : ℝ) ≤ Fintype.card V := hks.trans hNs.le
  calc
    (k : ℝ) / (Fintype.card V : ℝ) ^ 2 ≤
        (Fintype.card V : ℝ) / (Fintype.card V : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hkN (by positivity)
    _ = 1 / (Fintype.card V : ℝ) := by field_simp

end Erdos585.Attempt6.ReachabilityBoost
