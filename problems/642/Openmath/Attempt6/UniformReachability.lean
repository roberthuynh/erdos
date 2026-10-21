import Openmath.Attempt6.ReservoirGrowth
import Openmath.Attempt6.WellExpandingSeed

/-
Uniformization of actual sampled reservoir reachability using the checked
fresh-layer growth supplier and finite seed/deletion entropy. CJMM Sections 7.4-7.6,
Advances in Mathematics 469 (2025), 110228. Ambient L remains explicit.
-/

namespace Erdos585.Attempt6.UniformReachability

open Finset SimpleGraph MeasureTheory Real
open RobustCore Reachability SampledReachability ReservoirGrowth
open OAI.ErdosGallai.Sampling

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual polynomial seed/deletion entropy is absorbed by the quadratic-log tail. -/
theorem entropy_tail_sum_le (N : ℕ) (hN : 2 ≤ N) (K D : ℝ)
    (hK : 0 ≤ K) (hKD : K ≤ exp (D / 2)) (hD : 16 * log N ≤ D) :
    (∑ u ∈ Finset.Icc 1 N,
      ((u + 1 : ℕ) : ℝ) * (N : ℝ) ^ (3 * u) * (K * exp (-D * u))) ≤
      1 / (N : ℝ) ^ 2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ log N := log_nonneg (by linarith)
  have hD0 : 0 ≤ D := by linarith
  have hterm : ∀ u ∈ Finset.Icc 1 N,
      ((u + 1 : ℕ) : ℝ) * (N : ℝ) ^ (3 * u) * (K * exp (-D * u)) ≤
        1 / (N : ℝ) ^ 3 := by
    intro u hu
    obtain ⟨hu1, huN⟩ := Finset.mem_Icc.mp hu
    have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu1
    have huNR : (u : ℝ) ≤ N := by exact_mod_cast huN
    have huc : ((u + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by push_cast; nlinarith
    have hpow : (N : ℝ) ^ (3 * u) = exp (((3 * u : ℕ) : ℝ) * log N) := by
      rw [exp_nat_mul, exp_log hNp]
    have hexponent : ((3 * u : ℕ) : ℝ) * log N - D * u + D / 2 ≤ -5 * log N := by
      have hmul := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg u)
      have hmul2 := mul_le_mul_of_nonneg_left huR hD0
      have hlogu := mul_le_mul_of_nonneg_right huR hlog
      push_cast
      nlinarith
    have hexp : (N : ℝ) ^ 2 * exp (-5 * log N) = 1 / (N : ℝ) ^ 3 := by
      rw [show -5 * log (N : ℝ) = -(5 * log (N : ℝ)) by ring, exp_neg]
      rw [show 5 * log (N : ℝ) = ((5 : ℕ) : ℝ) * log (N : ℝ) by norm_num,
        exp_nat_mul, exp_log hNp]
      field_simp
    calc
      _ = ((u + 1 : ℕ) : ℝ) * K *
          exp (((3 * u : ℕ) : ℝ) * log N - D * u) := by
        rw [hpow, sub_eq_add_neg, exp_add]
        simp only [neg_mul]
        ring
      _ ≤ ((u + 1 : ℕ) : ℝ) * exp (D / 2) *
          exp (((3 * u : ℕ) : ℝ) * log N - D * u) := by gcongr
      _ = ((u + 1 : ℕ) : ℝ) *
          exp (((3 * u : ℕ) : ℝ) * log N - D * u + D / 2) := by
        rw [exp_add]
        ring
      _ ≤ (N : ℝ) ^ 2 * exp (-5 * log N) :=
        mul_le_mul huc (exp_le_exp.mpr hexponent) (exp_pos _).le (sq_nonneg _)
      _ = _ := hexp
  calc
    _ ≤ ∑ _u ∈ Finset.Icc 1 N, 1 / (N : ℝ) ^ 3 := Finset.sum_le_sum hterm
    _ = (N : ℝ) * (1 / (N : ℝ) ^ 3) := by simp
    _ = _ := by field_simp

/-- Explicit ambient threshold absorbing the polynomial layer prefactor. -/
theorem large_scale_entropy_parameters (N : ℕ) (L epsilon : ℝ)
    (hL : (10 : ℝ) ^ 30 ≤ L) (heps : (1 / 128 : ℝ) ≤ epsilon)
    (hlog : log N ≤ L) :
    2 * L ^ 4 ≤ exp ((epsilon ^ 2 * L ^ 2 / 65536) / 2) ∧
      16 * log N ≤ epsilon ^ 2 * L ^ 2 / 65536 := by
  let D := epsilon ^ 2 * L ^ 2 / 65536
  have hL1 : 1 ≤ L := by norm_num at hL; linarith
  have hLp : 0 < L := by linarith
  have heps0 : 0 < epsilon := by linarith
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hDlower : L ^ 2 ≤ 1073741824 * D := by
    have heps2 : (1 / 16384 : ℝ) ≤ epsilon ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right heps2 (sq_nonneg L)
    dsimp [D]
    nlinarith
  have hlarge : 16 * (1073741824 : ℝ) ≤ L := by norm_num at hL ⊢; linarith
  have hlogD : 16 * log N ≤ D := by
    have hm := mul_le_mul_of_nonneg_right hlarge hLp.le
    nlinarith
  have hc : 96 * (1073741824 : ℝ) ^ 3 ≤ L ^ 2 := by
    norm_num at hL ⊢
    nlinarith [sq_nonneg (L - 1000000000000000000000000000000)]
  have hm := mul_le_mul_of_nonneg_right hc (pow_nonneg hLp.le 4)
  have hcube := pow_le_pow_left₀ (sq_nonneg L) hDlower 3
  have hpoly : 2 * L ^ 4 ≤ D ^ 3 / 48 := by nlinarith
  have hexp := Real.pow_div_factorial_le_exp (D / 2) (show 0 ≤ D / 2 by positivity) 3
  norm_num at hexp
  constructor
  · change 2 * L ^ 4 ≤ exp (D / 2)
    nlinarith
  · exact hlogD

/-- Actual high-probability CJMM 7.13 uniformization, retaining pure scalar conditions. -/
theorem uniform_well_expanding_failure_probability
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hL : 16 ≤ L)
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hN : 2 ≤ Fintype.card V) (hlarge : 256 ≤ epsilon * L)
    (hlog : log (Fintype.card V) ≤ L)
    (hs : 20 * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ s)
    (hG : RobustExpanderAt G L epsilon s)
    (hKD : 2 * L ^ 4 ≤ exp ((epsilon ^ 2 * L ^ 2 / 65536) / 2))
    (hD : 16 * log (Fintype.card V) ≤ epsilon ^ 2 * L ^ 2 / 65536) :
    (sampleMeasure V p).real
      {omega | ∃ U F, U.Nonempty ∧ WellExpandingAt G p L U ∧
        F ⊆ G.edgeFinset ∧ F.card ≤ U.card ∧
        ((reservoirBall (G.deleteEdges F) U (sampleVertices omega) (growthSteps L + 1)).card : ℝ) ≤
          (sampleVertices omega).card / 2} ≤ 1 / (Fintype.card V : ℝ) ^ 2 := by
  have hlocal : ∀ U F, U.Nonempty → WellExpandingAt G p L U →
      F ⊆ G.edgeFinset → F.card ≤ U.card →
      (sampleMeasure V p).real
        {omega | ((reservoirBall (G.deleteEdges F) U (sampleVertices omega)
          (growthSteps L + 1)).card : ℝ) ≤ (sampleVertices omega).card / 2} ≤
        (2 * L ^ 4) * exp (-(epsilon ^ 2 * L ^ 2 / 65536) * U.card) := by
    intro U F hU hW hFG hF
    have ht := (well_expanding_reservoir_logarithmic_weak_budget G p L epsilon s hp hp1 hL heps
      heps1 hlarge hlog hs hG U hU hW F hFG hF).2
    convert ht using 2 <;> congr 1 <;> ring
  have hprob := all_seed_deletion_union_bound G (by omega : 1 ≤ Fintype.card V)
    (WellExpandingAt G p L)
    (fun U F => {omega | ((reservoirBall (G.deleteEdges F) U (sampleVertices omega)
      (growthSteps L + 1)).card : ℝ) ≤ (sampleVertices omega).card / 2})
    (fun u => (2 * L ^ 4) * exp (-(epsilon ^ 2 * L ^ 2 / 65536) * u))
    (fun _ => by positivity) hlocal
  exact hprob.trans (entropy_tail_sum_le (Fintype.card V) hN (2 * L ^ 4)
    (epsilon ^ 2 * L ^ 2 / 65536) (by positivity) hKD hD)

/-- An ambient binary logarithm also bounds the natural logarithm of the actual order. -/
theorem log_order_le_ambient (N : ℕ) (hN : 2 ≤ N) (L : ℝ)
    (hlog : logTwo (N : ℝ) ≤ L) : log (N : ℝ) ≤ L := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog0 : 0 ≤ log (N : ℝ) := log_nonneg (by linarith)
  have hlog2 : log (2 : ℝ) ≤ 1 := by
    have hh := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlog2p : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hle : log (N : ℝ) ≤ logTwo (N : ℝ) := by
    unfold logTwo
    apply (le_div_iff₀ hlog2p).mpr
    nlinarith
  exact hle.trans hlog

/-- Uniform high probability over all eligible seeds and deletion sets.
The final wrapper has no fixed-pair probability premise. -/
theorem uniform_well_expanding_large_scale
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hL : (10 : ℝ) ^ 30 ≤ L) (heps : (1 / 128 : ℝ) ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hN : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hs : 20 * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ s)
    (hG : RobustExpanderAt G L epsilon s) :
    (sampleMeasure V p).real
      {omega | ∃ U F, U.Nonempty ∧ WellExpandingAt G p L U ∧
        F ⊆ G.edgeFinset ∧ F.card ≤ U.card ∧
        ((reservoirBall (G.deleteEdges F) U (sampleVertices omega) (growthSteps L + 1)).card : ℝ) ≤
          (sampleVertices omega).card / 2} ≤ 1 / (Fintype.card V : ℝ) ^ 2 := by
  have hL16 : 16 ≤ L := by norm_num at hL; linarith
  have heps0 : 0 < epsilon := by linarith
  have hln := log_order_le_ambient (Fintype.card V) hN L hlog
  obtain ⟨hKD, hD⟩ := large_scale_entropy_parameters (Fintype.card V) L epsilon hL heps hln
  have hlarge : 256 ≤ epsilon * L := by
    have hm := mul_le_mul_of_nonneg_right heps (by linarith : 0 ≤ L)
    norm_num at hL
    nlinarith
  exact uniform_well_expanding_failure_probability G p L epsilon s hp hp1 hL16
    heps0 heps1 hN hlarge hln hs hG hKD hD

/-- Literal original-edge reservoir balls are monotone in the starting seed. -/
theorem reservoirBall_mono_seed (J : SimpleGraph V) (U W Q : Finset V) (r : ℕ)
    (hUW : U ⊆ W) : reservoirBall J U Q r ⊆ reservoirBall J W Q r := by
  intro v hv
  obtain ⟨hvQ,u,hu,w,hw,hs⟩ := mem_reservoirBall.mp hv
  exact mem_reservoirBall.mpr ⟨hvQ,u,hUW hu,w,hw,hs⟩

/-- A nonempty set has an actual half-sized subset within the expander range. -/
theorem exists_half_subset (U : Finset V) (hU : U.Nonempty) (hN : 2 ≤ Fintype.card V) :
    ∃ W : Finset V, W ⊆ U ∧ W.Nonempty ∧
      (U.card : ℝ) ≤ 2 * W.card ∧
      (W.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3 := by
  have hu := hU.card_pos
  have hUN := Finset.card_le_univ U
  let m := (U.card + 1) / 2
  have hm : m ≤ U.card := by dsimp [m]; omega
  obtain ⟨W,hWU,hWcard⟩ := Finset.exists_subset_card_eq hm
  have hWpos : 0 < W.card := by dsimp [m] at hWcard; omega
  refine ⟨W,hWU,Finset.card_pos.mp hWpos,?_,?_⟩
  · have hh : U.card ≤ 2 * W.card := by dsimp [m] at hWcard; omega
    exact_mod_cast hh
  · have hh : 3 * W.card ≤ 2 * Fintype.card V := by dsimp [m] at hWcard; omega
    have hhR : (3 : ℝ) * W.card ≤ 2 * Fintype.card V := by exact_mod_cast hh
    linarith

/-- The deletion budget for an arbitrary seed is affordable for its extracted half-seed. -/
theorem deletion_budget_le_seed_lower (p : unitInterval) (L epsilon : ℝ)
    (hp : 0 < (p : ℝ)) (hL : 1 ≤ L) (heps : (1 / 128 : ℝ) ≤ epsilon)
    (U W : Finset V) (hhalf : (U.card : ℝ) ≤ 2 * W.card) :
    (p : ℝ) ^ 4 * U.card / (1536 * L ^ 27) ≤
      epsilon * W.card / (3 * ((p : ℝ)⁻¹) ^ 4 * L ^ 26) := by
  have hLp : 0 < L := by linarith
  have heps0 : 0 ≤ epsilon := by linarith
  have hEW : 2 * (W.card : ℝ) ≤ 512 * epsilon * W.card := by
    have hm := mul_le_mul_of_nonneg_right heps (Nat.cast_nonneg W.card)
    nlinarith
  have hnum : (p : ℝ) ^ 4 * U.card ≤ 512 * epsilon * (p : ℝ) ^ 4 * W.card := by
    have hm := mul_le_mul_of_nonneg_left (hhalf.trans hEW) (pow_nonneg hp.le 4)
    nlinarith
  have hden : 1536 * L ^ 26 ≤ 1536 * L ^ 27 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by norm_num : 26 ≤ 27)) (by norm_num)
  have hh := div_le_div₀ (by positivity : 0 ≤ 512 * epsilon * (p : ℝ) ^ 4 * W.card)
    hnum (by positivity : 0 < 1536 * L ^ 26) hden
  have heq : 512 * epsilon * (p : ℝ) ^ 4 * W.card / (1536 * L ^ 26) =
      epsilon * W.card / (3 * ((p : ℝ)⁻¹) ^ 4 * L ^ 26) := by field_simp; ring
  simpa only [heq] using hh

/-- An actual well-expanding seed transports the failure of any nonempty starting set. -/
theorem arbitrary_failure_subset_well_expanding_failure
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hL : 1 ≤ L) (heps : (1 / 128 : ℝ) ≤ epsilon)
    (heps1 : epsilon ≤ 1) (hN : 2 ≤ Fintype.card V)
    (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hs : 20 * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ s)
    (hG : RobustExpanderAt G L epsilon s) (r : ℕ) :
    {omega : V → Bool | ∃ (U : Finset V) (F : Finset (Sym2 V)), U.Nonempty ∧
      F ⊆ G.edgeFinset ∧
      (F.card : ℝ) ≤ (p : ℝ) ^ 4 * U.card / (1536 * L ^ 27) ∧
      ((reservoirBall (G.deleteEdges F) U (sampleVertices omega) r).card : ℝ) ≤
        (sampleVertices omega).card / 2} ⊆
    {omega : V → Bool | ∃ (S : Finset V) (F : Finset (Sym2 V)), S.Nonempty ∧
      WellExpandingAt G p L S ∧ F ⊆ G.edgeFinset ∧ F.card ≤ S.card ∧
      ((reservoirBall (G.deleteEdges F) S (sampleVertices omega) r).card : ℝ) ≤
        (sampleVertices omega).card / 2} := by
  classical
  have heps0 : 0 < epsilon := by linarith
  have hLp : 0 < L := by linarith
  have hs24 : ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ s := by
    have hscale : 0 ≤ ((p : ℝ)⁻¹) ^ 4 * L ^ 24 := by positivity
    nlinarith [hs]
  rintro omega ⟨U,F,hU,hFG,hF,hbad⟩
  obtain ⟨W,hWU,hW,hhalf,hWsmall⟩ := exists_half_subset U hU hN
  obtain ⟨S,hSW,hSgood,hSsize⟩ := WellExpandingSeed.exists_sampled_well_expanding_seed
    G p L epsilon s hG hN hlog hp heps0 heps1 hs24 W hWsmall
  have hWpos : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
  have hSposR : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hSsize
  have hSpos : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hSposR)
  have hFSR : (F.card : ℝ) ≤ S.card := hF.trans
    ((deletion_budget_le_seed_lower p L epsilon hp hL heps U W hhalf).trans hSsize)
  have hFS : F.card ≤ S.card := by exact_mod_cast hFSR
  have hball : ((reservoirBall (G.deleteEdges F) S (sampleVertices omega) r).card : ℝ) ≤
      (reservoirBall (G.deleteEdges F) U (sampleVertices omega) r).card := by
    exact_mod_cast Finset.card_le_card
      (reservoirBall_mono_seed (G.deleteEdges F) S U (sampleVertices omega) r (hSW.trans hWU))
  exact ⟨S,F,hSpos,hSgood,hFG,hFS,hball.trans hbad⟩

/-- High probability for every actual nonempty starting set and affordable deletion set.
This conclusion is simultaneous and has no fixed-pair probability hypothesis. -/
theorem uniform_arbitrary_reservoir_large_scale
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hL : (10 : ℝ) ^ 30 ≤ L) (heps : (1 / 128 : ℝ) ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hN : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hs : 20 * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ s)
    (hG : RobustExpanderAt G L epsilon s) :
    (sampleMeasure V p).real
      {omega | ∃ (U : Finset V) (F : Finset (Sym2 V)), U.Nonempty ∧
        F ⊆ G.edgeFinset ∧
        (F.card : ℝ) ≤ (p : ℝ) ^ 4 * U.card / (1536 * L ^ 27) ∧
        ((reservoirBall (G.deleteEdges F) U (sampleVertices omega) (growthSteps L + 1)).card : ℝ) ≤
          (sampleVertices omega).card / 2} ≤ 1 / (Fintype.card V : ℝ) ^ 2 := by
  have hL1 : 1 ≤ L := by norm_num at hL; linarith
  apply (measureReal_mono
    (arbitrary_failure_subset_well_expanding_failure G p L epsilon s hp hL1 heps
      heps1 hN hlog hs hG (growthSteps L + 1)) (measure_ne_top _ _)).trans
  exact uniform_well_expanding_large_scale G p L epsilon s hp hp1 hL heps heps1 hN hlog hs hG

/-- The simultaneous reachability event itself has probability at least one minus n inverse squared. -/
theorem uniform_arbitrary_good_probability
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hL : (10 : ℝ) ^ 30 ≤ L) (heps : (1 / 128 : ℝ) ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hN : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hs : 20 * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ s)
    (hG : RobustExpanderAt G L epsilon s) :
    1 - 1 / (Fintype.card V : ℝ) ^ 2 ≤
      (sampleMeasure V p).real {omega | ∀ U : Finset V, U.Nonempty →
        ∀ F : Finset (Sym2 V), F ⊆ G.edgeFinset →
          (F.card : ℝ) ≤ (p : ℝ) ^ 4 * U.card / (1536 * L ^ 27) →
          (sampleVertices omega).card / (2 : ℝ) <
            ((reservoirBall (G.deleteEdges F) U (sampleVertices omega) (growthSteps L + 1)).card : ℝ)} := by
  classical
  let B : Set (V → Bool) := {omega | ∃ (U : Finset V) (F : Finset (Sym2 V)), U.Nonempty ∧
      F ⊆ G.edgeFinset ∧
      (F.card : ℝ) ≤ (p : ℝ) ^ 4 * U.card / (1536 * L ^ 27) ∧
      ((reservoirBall (G.deleteEdges F) U (sampleVertices omega) (growthSteps L + 1)).card : ℝ) ≤
        (sampleVertices omega).card / 2}
  have hb : (sampleMeasure V p).real B ≤ 1 / (Fintype.card V : ℝ) ^ 2 :=
    uniform_arbitrary_reservoir_large_scale G p L epsilon s hp hp1 hL heps heps1 hN hlog hs hG
  have heq : {omega | ∀ U : Finset V, U.Nonempty →
        ∀ F : Finset (Sym2 V), F ⊆ G.edgeFinset →
          (F.card : ℝ) ≤ (p : ℝ) ^ 4 * U.card / (1536 * L ^ 27) →
          (sampleVertices omega).card / (2 : ℝ) <
            ((reservoirBall (G.deleteEdges F) U (sampleVertices omega) (growthSteps L + 1)).card : ℝ)} = Bᶜ := by
    ext omega
    constructor
    · intro hgood hbad
      obtain ⟨U,F,hU,hFG,hF,hfail⟩ := hbad
      exact not_le_of_gt (hgood U hU F hFG hF) hfail
    · intro hgood U hU F hFG hF
      apply lt_of_not_ge
      exact fun hbad => hgood ⟨U,F,hU,hFG,hF,hbad⟩
  rw [heq, measureReal_compl (MeasurableSet.of_discrete), probReal_univ]
  linarith

/-- The actual integer radius stays within the fourth power of the ambient logarithm. -/
theorem growth_radius_le_floor (L : ℝ) (hL : 16 ≤ L) :
    growthSteps L + 1 ≤ ⌊L ^ 4⌋₊ := by
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hL4 : 2 ≤ L ^ 4 := by
    have hh := pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 4)
    nlinarith
  have hk : (growthSteps L : ℝ) ≤ L ^ 4 / 2 := Nat.floor_le (by positivity)
  apply (Nat.le_floor_iff (by positivity : 0 ≤ L ^ 4)).mpr
  push_cast
  linarith

/-- Source radius version of the simultaneous high-probability event. -/
theorem uniform_arbitrary_good_probability_floor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (L epsilon s : ℝ)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hL : (10 : ℝ) ^ 30 ≤ L) (heps : (1 / 128 : ℝ) ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hN : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hs : 20 * ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ s)
    (hG : RobustExpanderAt G L epsilon s) :
    1 - 1 / (Fintype.card V : ℝ) ^ 2 ≤
      (sampleMeasure V p).real {omega | ∀ U : Finset V, U.Nonempty →
        ∀ F : Finset (Sym2 V), F ⊆ G.edgeFinset →
          (F.card : ℝ) ≤ (p : ℝ) ^ 4 * U.card / (1536 * L ^ 27) →
          (sampleVertices omega).card / (2 : ℝ) <
            ((reservoirBall (G.deleteEdges F) U (sampleVertices omega) ⌊L ^ 4⌋₊).card : ℝ)} := by
  have hL16 : 16 ≤ L := by norm_num at hL; linarith
  apply (uniform_arbitrary_good_probability G p L epsilon s hp hp1 hL heps heps1
    hN hlog hs hG).trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro omega hgood U hU F hFG hF
  apply (hgood U hU F hFG hF).trans_le
  exact_mod_cast Finset.card_le_card
    (reservoirBall_mono_radius (G.deleteEdges F) U (sampleVertices omega)
      (growth_radius_le_floor L hL16))

end Erdos585.Attempt6.UniformReachability
