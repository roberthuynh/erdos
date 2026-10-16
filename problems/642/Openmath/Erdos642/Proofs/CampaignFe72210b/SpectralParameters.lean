import Mathlib

namespace Erdos642.CampaignFe72210b.SpectralParameters

noncomputable def beta : ℝ := 1/(10:ℝ)^24
def A : ℝ := (10:ℝ)^100
noncomputable def a : ℝ := beta^2/84000
noncomputable def q (N k : ℕ) : ℕ := ⌊a*(N:ℝ)/(k:ℝ)^2⌋₊

theorem beta_pos : 0 < beta := by norm_num [beta]
theorem A_pos : 0 < A := by norm_num [A]
theorem a_pos : 0 < a := by norm_num [a, beta]
theorem constant_bounds : 421/A ≤ beta ∧ 2 ≤ a*A ∧ 42000*a ≤ beta^2 := by
  norm_num [A, a, beta]

theorem ratio_ge_two (N k : ℕ) (hk : 2 ≤ k) (hN : A*(k:ℝ)^2 ≤ N) :
    2 ≤ a*(N:ℝ)/(k:ℝ)^2 := by
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hmul := mul_le_mul_of_nonneg_left hN a_pos.le
  have hratio : a*A ≤ a*(N:ℝ)/(k:ℝ)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hk')).mpr
    nlinarith
  exact constant_bounds.2.1.trans hratio

theorem q_bounds (N k : ℕ) (hk : 2 ≤ k) (hN : A*(k:ℝ)^2 ≤ N) :
    1 ≤ q N k ∧ a*(N:ℝ)/(2*(k:ℝ)^2) ≤ (q N k:ℝ) ∧
      (q N k:ℝ) ≤ a*(N:ℝ)/(k:ℝ)^2 := by
  have hr := ratio_ge_two N k hk hN
  have hl := Nat.lt_floor_add_one (a*(N:ℝ)/(k:ℝ)^2)
  have hu := Nat.floor_le (by linarith : (0:ℝ)≤a*(N:ℝ)/(k:ℝ)^2)
  refine ⟨(Nat.one_le_floor_iff _).mpr (by linarith), ?_, hu⟩
  change a*(N:ℝ)/(2*(k:ℝ)^2) ≤ (⌊a*(N:ℝ)/(k:ℝ)^2⌋₊:ℝ)
  have he : a*(N:ℝ)/(2*(k:ℝ)^2) = (a*(N:ℝ)/(k:ℝ)^2)/2 := by ring
  rw [he]
  linarith

theorem degree_pos (d k : ℕ) (γ : ℝ) (hk : 2 ≤ k) (hγ : 0<γ)
    (hd : A*(k:ℝ)/γ ≤ d) : 1 ≤ d := by
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hA := A_pos
  have hd' : (0:ℝ)<d := lt_of_lt_of_le (by positivity : (0:ℝ)<A*(k:ℝ)/γ) hd
  have hn : 0<d := by exact_mod_cast hd'
  omega

theorem local_failure_le_beta (N d k : ℕ) (γ : ℝ) (hk : 2 ≤ k)
    (hγ : 0<γ) (hγupper : γ≤1) (hN : A*(k:ℝ)^2 ≤ N)
    (hd : A*(k:ℝ)/γ ≤ d) :
    (k:ℝ)/(d:ℝ)+400*(k:ℝ)^2/(N:ℝ)+20*(k:ℝ)/((d:ℝ)*γ) ≤ beta := by
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hd' : (0:ℝ)<d := by
    have hn := degree_pos d k γ hk hγ hd
    exact_mod_cast (show 0<d by omega)
  have hN' : (0:ℝ)<N := lt_of_lt_of_le (mul_pos A_pos (sq_pos_of_pos hk')) hN
  have hdg : A*(k:ℝ) ≤ (d:ℝ)*γ := (div_le_iff₀ hγ).mp hd
  have h1 : (k:ℝ)/(d:ℝ) ≤ 1/A := by
    apply (div_le_div_iff₀ hd' A_pos).mpr
    have hh := mul_le_mul_of_nonneg_left hγupper hd'.le
    nlinarith
  have h2 : 400*(k:ℝ)^2/(N:ℝ) ≤ 400/A := by
    apply (div_le_div_iff₀ hN' A_pos).mpr
    nlinarith
  have h3 : 20*(k:ℝ)/((d:ℝ)*γ) ≤ 20/A := by
    apply (div_le_div_iff₀ (mul_pos hd' hγ) A_pos).mpr
    nlinarith
  calc
    _ ≤ 1/A+400/A+20/A := add_le_add (add_le_add h1 h2) h3
    _ = 421/A := by ring
    _ ≤ beta := constant_bounds.1

theorem block_order_bound (N k : ℕ) (hk : 2 ≤ k) (hN : A*(k:ℝ)^2 ≤ N) :
    21000*(k:ℝ)*((q N k*k+1:ℕ):ℝ) ≤ beta^2*(N:ℝ) := by
  have hq := q_bounds N k hk hN
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hqscaled : (q N k:ℝ)*(k:ℝ)^2 ≤ a*(N:ℝ) :=
    (le_div_iff₀ (sq_pos_of_pos hk')).mp hq.2.2
  have ht : (1:ℝ) ≤ (q N k:ℝ)*(k:ℝ) := by
    have hnat : 1 ≤ q N k*k := by
      simpa using Nat.mul_le_mul hq.1 (show 1≤k by omega)
    exact_mod_cast hnat
  have hdouble : (q N k:ℝ)*(k:ℝ)+1 ≤ 2*(q N k:ℝ)*(k:ℝ) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hdouble
    (show (0:ℝ)≤21000*(k:ℝ) by positivity)
  have hc := mul_le_mul_of_nonneg_right constant_bounds.2.2 (Nat.cast_nonneg N : (0:ℝ)≤N)
  push_cast
  nlinarith
end Erdos642.CampaignFe72210b.SpectralParameters
