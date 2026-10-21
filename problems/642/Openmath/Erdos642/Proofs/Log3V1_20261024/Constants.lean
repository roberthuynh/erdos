import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

   
                                                                     

                                                                                             
                             

                                                                              
                                                                          
                                                                                      
                                
                                                                                        
                                                                       
                               
                                                                

                                                                                                   
                                                                                              
                                                                            
                                                                                                 
  

namespace Erdos642.Log3V1_20261024.Constants

/-! ### Definitions -/

/-- The fixed residual degree ratio `D0 = 534`. -/
noncomputable def D0 : ℝ := 534

/-- The toughness constant `η = 1/(64·D0)` of `ToughLayersV2.LayerGood`. -/
noncomputable def η : ℝ := 1 / (64 * D0)

/-- The merger's linking constant `γ = η/4` (`ToughPaths.linked_of_ordinaryTough`). -/
noncomputable def γ : ℝ := η / 4

/-- `q0 = -log(1 - γ)`. -/
noncomputable def q0 : ℝ := -Real.log (1 - γ)

/-- `Cη = 3 + 1/q0`. -/
noncomputable def Cη : ℝ := 3 + 1 / q0

/-- The cut constant `a = log 2 / 6` (equal by `rfl` to `Extract.cutConstant`). -/
noncomputable def a : ℝ := Real.log 2 / 6

/-- The expansion constant handed to the layer sampler: `a_s = 3a/(1600·Cη)`. -/
noncomputable def a_s : ℝ := 3 * a / (1600 * Cη)

/-- The mask constant `C0 = max(4, 800/a, 2048·Cη)`. -/
noncomputable def C0 : ℝ := max (max 4 (800 / a)) (2048 * Cη)

/-- The host constant `K = max(16·C0², 64·C0, 128·Cη, 4·Cη·Ks/3)`. -/
noncomputable def K (Ks : ℝ) : ℝ :=
  max (max (max (16 * C0 ^ 2) (64 * C0)) (128 * Cη)) (4 * Cη * Ks / 3)

/-- The absolute constant of the theorem, `C = max(200·K, 10^6)`. -/
noncomputable def C (Ks : ℝ) : ℝ := max (200 * K Ks) 1000000

/-- The number of layers, `b = ⌈log t / q0⌉₊ + 2`. -/
noncomputable def phaseCount (t : ℕ) : ℕ := ⌈Real.log (t : ℝ) / q0⌉₊ + 2

/-! ### 1. Signs and basic bounds -/

theorem D0_eq : D0 = 534 := rfl

theorem one_le_D0 : 1 ≤ D0 := by norm_num [D0]

theorem D0_pos : 0 < D0 := by norm_num [D0]

theorem η_eq : η = 1 / (64 * D0) := rfl

theorem η_pos : 0 < η := by unfold η; have := D0_pos; positivity

theorem η_le_one : η ≤ 1 := by
  unfold η D0
  norm_num

theorem γ_eq : γ = η / 4 := rfl

theorem γ_pos : 0 < γ := by unfold γ; have := η_pos; positivity

theorem γ_lt_one : γ < 1 := by
  unfold γ
  have := η_le_one
  linarith

theorem γ_le_one : γ ≤ 1 := γ_lt_one.le

theorem q0_pos : 0 < q0 := by
  unfold q0
  have h := Real.log_neg (by linarith [γ_lt_one] : (0 : ℝ) < 1 - γ)
    (by linarith [γ_pos] : 1 - γ < 1)
  linarith

theorem log_one_sub_γ : Real.log (1 - γ) = -q0 := by
  unfold q0
  ring

theorem three_le_Cη : 3 ≤ Cη := by
  unfold Cη
  have := q0_pos
  have : 0 < 1 / q0 := by positivity
  linarith

theorem one_le_Cη : 1 ≤ Cη := by linarith [three_le_Cη]

theorem Cη_pos : 0 < Cη := by linarith [three_le_Cη]

theorem a_pos : 0 < a := by
  unfold a
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

theorem a_s_eq : a_s = 3 * a / (1600 * Cη) := rfl

theorem a_s_pos : 0 < a_s := by
  unfold a_s
  have := a_pos
  have := Cη_pos
  positivity

theorem four_le_C0 : 4 ≤ C0 := (le_max_left _ _).trans (le_max_left _ _)

theorem C0_pos : 0 < C0 := by linarith [four_le_C0]

theorem C0_ge_a : 800 / a ≤ C0 := (le_max_right _ _).trans (le_max_left _ _)

theorem C0_ge_Cη : 2048 * Cη ≤ C0 := le_max_right _ _

theorem K_ge_C0_sq (Ks : ℝ) : 16 * C0 ^ 2 ≤ K Ks :=
  ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)

theorem K_ge_C0 (Ks : ℝ) : 64 * C0 ≤ K Ks :=
  ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)

theorem K_ge_Cη (Ks : ℝ) : 128 * Cη ≤ K Ks :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem K_ge_Ks (Ks : ℝ) : 4 * Cη * Ks / 3 ≤ K Ks := le_max_right _ _

theorem K_pos (Ks : ℝ) : 0 < K Ks := by
  have := K_ge_C0_sq Ks
  have := C0_pos
  have : 0 < 16 * C0 ^ 2 := by positivity
  linarith

theorem K_nonneg (Ks : ℝ) : 0 ≤ K Ks := (K_pos Ks).le

theorem C_ge_K (Ks : ℝ) : 200 * K Ks ≤ C Ks := le_max_left _ _

theorem C_ge_million (Ks : ℝ) : 1000000 ≤ C Ks := le_max_right _ _

theorem C_pos (Ks : ℝ) : 0 < C Ks := by linarith [C_ge_million Ks]

/-! ### 2. The merger's phase hypothesis -/

/-- `(1 - γ)^(b - 1)·t < 2` for `b = phaseCount t` and every natural `t ≥ 1`
(`hphase` of `Merger.cycle_through_tokens`). -/
theorem phase_bound (t : ℕ) (ht : 1 ≤ t) :
    (1 - γ) ^ (phaseCount t - 1) * (t : ℝ) < 2 := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈Real.log (t : ℝ) / q0⌉₊ := ⟨_, rfl⟩
  have hpc : phaseCount t - 1 = m + 1 := by
    unfold phaseCount
    rw [← hm]
    omega
  have hγ0 : 0 < 1 - γ := by linarith [γ_lt_one]
  have hγ1 : 1 - γ ≤ 1 := by linarith [γ_pos]
  have hmq : Real.log (t : ℝ) ≤ (m : ℝ) * q0 := by
    have h := Nat.le_ceil (Real.log (t : ℝ) / q0)
    rw [← hm, div_le_iff₀ q0_pos] at h
    exact h
  have h2 : (1 - γ) ^ m * (t : ℝ) = Real.exp ((m : ℝ) * Real.log (1 - γ) + Real.log t) := by
    rw [Real.exp_add, Real.exp_log ht0, ← Real.log_pow, Real.exp_log (pow_pos hγ0 m)]
  have h3 : (m : ℝ) * Real.log (1 - γ) + Real.log t ≤ 0 := by
    rw [log_one_sub_γ]
    linarith
  have hpow : (1 - γ) ^ m * (t : ℝ) ≤ 1 := by
    rw [h2]
    calc _ ≤ Real.exp 0 := Real.exp_le_exp.mpr h3
      _ = 1 := Real.exp_zero
  have hnn : 0 ≤ (1 - γ) ^ m * (t : ℝ) := by positivity
  rw [hpc]
  calc (1 - γ) ^ (m + 1) * (t : ℝ) = ((1 - γ) ^ m * t) * (1 - γ) := by ring
    _ ≤ ((1 - γ) ^ m * t) * 1 := mul_le_mul_of_nonneg_left hγ1 hnn
    _ ≤ 1 := by linarith
    _ < 2 := by norm_num

/-! ### 3. The number of layers -/

theorem one_le_phaseCount (t : ℕ) : 1 ≤ phaseCount t := by
  unfold phaseCount
  omega

/-- `b = phaseCount t ≤ Cη·L` whenever `t ≥ 1`, `log t ≤ L` and `L ≥ 1`. -/
theorem phaseCount_le (t : ℕ) (ht : 1 ≤ t) (L : ℝ) (htL : Real.log (t : ℝ) ≤ L)
    (hL : 1 ≤ L) : (phaseCount t : ℝ) ≤ Cη * L := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hlog0 : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg htR
  have hx0 : 0 ≤ Real.log (t : ℝ) / q0 := div_nonneg hlog0 q0_pos.le
  have hceil : (⌈Real.log (t : ℝ) / q0⌉₊ : ℝ) < Real.log (t : ℝ) / q0 + 1 :=
    Nat.ceil_lt_add_one hx0
  have hdiv : Real.log (t : ℝ) / q0 ≤ L / q0 := div_le_div_of_nonneg_right htL q0_pos.le
  have hpc : (phaseCount t : ℝ) = (⌈Real.log (t : ℝ) / q0⌉₊ : ℝ) + 2 := by
    unfold phaseCount
    push_cast
    ring
  have hCL : Cη * L = 3 * L + L / q0 := by
    unfold Cη
    ring
  rw [hpc, hCL]
  linarith

/-- `log t ≤ L` from `1 ≤ t ≤ N` and `log (2N) ≤ L` (for `t = |Q| ≤ |W|`). -/
theorem log_le_of_le (t N : ℕ) (ht : 1 ≤ t) (htN : t ≤ N) (L : ℝ)
    (hL : Real.log (2 * (N : ℝ)) ≤ L) : Real.log (t : ℝ) ≤ L := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htN' : (t : ℝ) ≤ N := by exact_mod_cast htN
  refine le_trans (Real.log_le_log (by linarith) ?_) hL
  linarith

/-- `log (2m) ≤ log (2N)` for `1 ≤ m ≤ N` (for `log (2|R|) ≤ log (2|W|)`). -/
theorem log_two_mul_le (m N : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) :
    Real.log (2 * (m : ℝ)) ≤ Real.log (2 * (N : ℝ)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
  exact Real.log_le_log (by linarith) (by linarith)

/-- `1 ≤ log (2n)` for `n ≥ 2` (so `L = log (2n) ≥ 1` once `n ≥ 3`). -/
theorem one_le_log_two_mul (n : ℕ) (hn : 2 ≤ n) : 1 ≤ Real.log (2 * (n : ℝ)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-! ### 4. The layer sampler's scale and expansion hypotheses -/

/-- `Ks·L ≤ rate·d0` with `rate = 1/b`, `d0 = 3d/4` (`K*L ≤ rate*d` of `exists_tough_layers`). -/
theorem layer_scale (Ks L d : ℝ) (b : ℕ) (hb : 1 ≤ b) (hKs : 0 ≤ Ks) (hL : 1 ≤ L)
    (hd : K Ks * L ^ 2 ≤ d) (hbL : (b : ℝ) ≤ Cη * L) :
    Ks * L ≤ (1 / (b : ℝ)) * (3 * d / 4) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hL0 : 0 < L := by linarith
  rw [show (1 / (b : ℝ)) * (3 * d / 4) = (3 * d / 4) / b by ring, le_div_iff₀ hb0]
  have h1 : Ks * L * b ≤ Ks * L * (Cη * L) :=
    mul_le_mul_of_nonneg_left hbL (mul_nonneg hKs hL0.le)
  have h2 : (4 * Cη * Ks / 3) * L ^ 2 ≤ K Ks * L ^ 2 :=
    mul_le_mul_of_nonneg_right (K_ge_Ks Ks) (by positivity)
  nlinarith

/-- `0 < d0 = 3d/4` from `K·L² ≤ d` and `L ≥ 1`. -/
theorem d0_pos (Ks L d : ℝ) (hL : 1 ≤ L) (hd : K Ks * L ^ 2 ≤ d) : 0 < 3 * d / 4 := by
  have hK := K_pos Ks
  have hL2 : 0 < L ^ 2 := by positivity
  have : 0 < K Ks * L ^ 2 := mul_pos hK hL2
  linarith

/-- `a_s/L² ≤ rate·lam` with `lam = 3φ/1600` and `φ ≥ a/L` (`a/L^2 ≤ rate*lam`). -/
theorem layer_expansion (L φ : ℝ) (b : ℕ) (hb : 1 ≤ b) (hL : 1 ≤ L) (hφ : a / L ≤ φ)
    (hbL : (b : ℝ) ≤ Cη * L) :
    a_s / L ^ 2 ≤ (1 / (b : ℝ)) * (3 * φ / 1600) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hL0 : 0 < L := by linarith
  have ha := a_pos
  have hC := Cη_pos
  have haL : a ≤ φ * L := (div_le_iff₀ hL0).mp hφ
  have hφ0 : 0 ≤ φ := le_trans (div_pos ha hL0).le hφ
  have e1 : a_s / L ^ 2 = (3 * a) / (1600 * Cη * L ^ 2) := by
    unfold a_s
    field_simp
  have e2 : (1 / (b : ℝ)) * (3 * φ / 1600) = (3 * φ) / (1600 * b) := by
    field_simp
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : a * b ≤ φ * L * b := mul_le_mul_of_nonneg_right haL hb0.le
  have h2 : φ * L * b ≤ φ * L * (Cη * L) := mul_le_mul_of_nonneg_left hbL (mul_nonneg hφ0 hL0.le)
  nlinarith

/-- `0 < lam = 3φ/1600` when `φ ≥ a/L`, `L > 0`. -/
theorem lam_pos (L φ : ℝ) (hL : 0 < L) (hφ : a / L ≤ φ) : 0 < 3 * φ / 1600 := by
  have := div_pos a_pos hL
  linarith

/-- `lam = 3φ/1600 ≤ 1` when `φ ≤ 1`. -/
theorem lam_le_one (φ : ℝ) (hφ : φ ≤ 1) : 3 * φ / 1600 ≤ 1 := by linarith

/-! ### 5. The Hall load -/

theorem p_pos (L p : ℝ) (hL : 0 < L) (hp : p = 1 / (C0 * L)) : 0 < p := by
  rw [hp]
  have := C0_pos
  positivity

/-- `800·p·d ≤ rho` with `p = 1/(C0·L)` and `rho = rate·d0 = (1/b)·(3d/4)`: the hypothesis `hpd`
of `LayerHall.layers_package` (that is `load(v) ≤ 2·(2p·100d) ≤ rho/2`, written (3)). -/
theorem hall_load (L d p : ℝ) (b : ℕ) (hb : 1 ≤ b) (hL : 1 ≤ L) (hd : 0 ≤ d)
    (hp : p = 1 / (C0 * L)) (hbL : (b : ℝ) ≤ Cη * L) :
    800 * p * d ≤ (1 / (b : ℝ)) * (3 * d / 4) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hL0 : 0 < L := by linarith
  have hC0 := C0_pos
  have e1 : 800 * p * d = (800 * d) / (C0 * L) := by
    rw [hp]
    field_simp
  have e2 : (1 / (b : ℝ)) * (3 * d / 4) = (3 * d) / (4 * b) := by
    field_simp
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : d * b ≤ d * (Cη * L) := mul_le_mul_of_nonneg_left hbL hd
  have h2 : (d * L) * (2048 * Cη) ≤ (d * L) * C0 :=
    mul_le_mul_of_nonneg_left C0_ge_Cη (mul_nonneg hd hL0.le)
  have h3 : 0 ≤ d * L * C0 := mul_nonneg (mul_nonneg hd hL0.le) hC0.le
  nlinarith

/-- The same bound in the written form `2·(2·p·(100·d)) ≤ rate·d0/2`. -/
theorem hall_load' (L d p : ℝ) (b : ℕ) (hb : 1 ≤ b) (hL : 1 ≤ L) (hd : 0 ≤ d)
    (hp : p = 1 / (C0 * L)) (hbL : (b : ℝ) ≤ Cη * L) :
    2 * (2 * p * (100 * d)) ≤ (1 / (b : ℝ)) * (3 * d / 4) / 2 := by
  have := hall_load L d p b hb hL hd hp hbL
  linarith

/-- The per-center load: `|N(v) ∩ Q| ≤ 2p·deg v` and `deg v ≤ 100d` give
`2·|N(v) ∩ Q| ≤ 2·(2p·100d) ≤ rate·d0/2`. -/
theorem hall_load_center (L d p x deg : ℝ) (b : ℕ) (hb : 1 ≤ b) (hL : 1 ≤ L) (hd : 0 ≤ d)
    (hp : p = 1 / (C0 * L)) (hbL : (b : ℝ) ≤ Cη * L) (hx : x ≤ 2 * p * deg)
    (hdeg : deg ≤ 100 * d) :
    2 * x ≤ (1 / (b : ℝ)) * (3 * d / 4) / 2 := by
  have hp0 := p_pos L p (by linarith) hp
  have h1 : 2 * p * deg ≤ 2 * p * (100 * d) := mul_le_mul_of_nonneg_left hdeg (by linarith)
  have := hall_load' L d p b hb hL hd hp hbL
  linarith

/-! ### 6. MaskCore's constant side conditions -/

/-- `0 < a`, `800/a ≤ C0`, `16·C0² ≤ K`, `64·C0 ≤ K` (`ha`, `hC0`, `hK1`, `hK2` of
`MaskCore.exists_dense_mask` with MaskCore's `a := a`). -/
theorem maskCore_constants (Ks : ℝ) :
    0 < a ∧ 800 / a ≤ C0 ∧ 16 * C0 ^ 2 ≤ K Ks ∧ 64 * C0 ≤ K Ks :=
  ⟨a_pos, C0_ge_a, K_ge_C0_sq Ks, K_ge_C0 Ks⟩

/-! ### 7. The number of layers is at most the residual order -/

/-- `b ≤ |R|`: from `|W| ≥ d + 1`, `d ≥ K·L²`, `L ≥ 1`, `b ≤ Cη·L` and `|W| ≤ 2|R|`. -/
theorem le_card_R (Ks L d : ℝ) (b nW nR : ℕ) (hL : 1 ≤ L) (hd : K Ks * L ^ 2 ≤ d)
    (hW : d + 1 ≤ (nW : ℝ)) (hWR : nW ≤ 2 * nR) (hbL : (b : ℝ) ≤ Cη * L) : b ≤ nR := by
  have hWR' : (nW : ℝ) ≤ 2 * (nR : ℝ) := by exact_mod_cast hWR
  have hC := Cη_pos
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have h1 : Cη * L ≤ Cη * L ^ 2 := mul_le_mul_of_nonneg_left hL2 hC.le
  have h2 : 128 * Cη * L ^ 2 ≤ K Ks * L ^ 2 :=
    mul_le_mul_of_nonneg_right (K_ge_Cη Ks) (by positivity)
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have : (b : ℝ) ≤ nR := by nlinarith
  exact_mod_cast this

/-- `2 ≤ |R|` under the same hypotheses (`2 ≤ Fintype.card V` of `exists_tough_layers`). -/
theorem two_le_card_R (Ks L d : ℝ) (nW nR : ℕ) (hL : 1 ≤ L) (hd : K Ks * L ^ 2 ≤ d)
    (hW : d + 1 ≤ (nW : ℝ)) (hWR : nW ≤ 2 * nR) : 2 ≤ nR := by
  have hWR' : (nW : ℝ) ≤ 2 * (nR : ℝ) := by exact_mod_cast hWR
  have hC := three_le_Cη
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have h2 : 128 * Cη * L ^ 2 ≤ K Ks * L ^ 2 :=
    mul_le_mul_of_nonneg_right (K_ge_Cη Ks) (by positivity)
  have h3 : 128 * Cη * 1 ≤ 128 * Cη * L ^ 2 := mul_le_mul_of_nonneg_left hL2 (by linarith)
  have : (2 : ℝ) ≤ nR := by linarith
  exact_mod_cast this

/-! ### 8. The degree ratio -/

/-- `100·d ≤ D0·(3d/4)` for `d ≥ 0` (upper degree hypothesis of `exists_tough_layers`). -/
theorem degree_ratio (d : ℝ) (hd : 0 ≤ d) : 100 * d ≤ D0 * (3 * d / 4) := by
  unfold D0
  linarith

/-! ### 9. Small orders and the host trigger -/

/-- For `n ≤ 2`, `C·n·log(2n)³` is at least the maximum edge count `n.choose 2`. -/
theorem small_n (Ks : ℝ) (n : ℕ) (hn : n ≤ 2) :
    ((n.choose 2 : ℕ) : ℝ) ≤ C Ks * n * Real.log (2 * (n : ℝ)) ^ 3 := by
  have hC := C_ge_million Ks
  rcases n with _ | _ | _ | n
  · simp
  · have h := Real.log_pos (by norm_num : (1 : ℝ) < 2 * ((1 : ℕ) : ℝ))
    have : 0 ≤ C Ks * ((1 : ℕ) : ℝ) * Real.log (2 * ((1 : ℕ) : ℝ)) ^ 3 := by
      have : 0 ≤ C Ks := by linarith
      positivity
    simpa using this
  swap
  · omega
  · have h1 := one_le_log_two_mul 2 le_rfl
    have h3 : 1 ≤ Real.log (2 * ((2 : ℕ) : ℝ)) ^ 3 := one_le_pow₀ h1
    have : (1 : ℝ) ≤ C Ks * ((2 : ℕ) : ℝ) * Real.log (2 * ((2 : ℕ) : ℝ)) ^ 3 := by
      push_cast at h3 ⊢
      nlinarith
    simpa using this

/-- The strict edge antecedent `C·n·log(2n)³ < e` with `e ≤ n.choose 2` forces `n ≥ 3`. -/
theorem three_le_of_edges (Ks : ℝ) (n e : ℕ) (hen : e ≤ n.choose 2)
    (he : C Ks * n * Real.log (2 * (n : ℝ)) ^ 3 < (e : ℝ)) : 3 ≤ n := by
  by_contra h
  have h2 := small_n Ks n (by omega)
  have hen' : (e : ℝ) ≤ ((n.choose 2 : ℕ) : ℝ) := by exact_mod_cast hen
  linarith

/-- The original antecedent pays the host trigger of `Extract.exists_mask_host`
(`hostConstant K = 200·K`): `C·n·L³ < e` implies `200·K·n·L³ < e` for `L ≥ 0`. -/
theorem host_trigger (Ks : ℝ) (n : ℕ) (L e : ℝ) (hL : 0 ≤ L)
    (he : C Ks * n * L ^ 3 < e) : 200 * K Ks * n * L ^ 3 < e := by
  have hnL : 0 ≤ (n : ℝ) * L ^ 3 := by positivity
  have h := mul_le_mul_of_nonneg_right (C_ge_K Ks) hnL
  nlinarith

end Erdos642.Log3V1_20261024.Constants
