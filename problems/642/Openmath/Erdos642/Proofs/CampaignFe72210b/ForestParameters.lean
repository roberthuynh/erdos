import Mathlib

namespace Erdos642.CampaignFe72210b.ForestParameters

def q (d : ℕ) : ℕ := d/100000
def b (d : ℕ) : ℕ := d/10000000
noncomputable def m (N d : ℕ) : ℕ := ⌈(N:ℝ)/(100000*(d:ℝ))⌉₊

/-- Natural quotient bounds with no divisibility assumption. -/
theorem div_real_bounds (n c : ℕ) (hc : 0 < c) (hn : 2*c ≤ n) :
    (n:ℝ)/(2*(c:ℝ)) ≤ (n/c:ℕ) ∧ (n/c:ℕ) ≤ (n:ℝ)/(c:ℝ) := by
  have hc' : (0:ℝ) < c := by exact_mod_cast hc
  have hn' : (2:ℝ)*c ≤ n := by exact_mod_cast hn
  have hr : ((n%c:ℕ):ℝ) < c := by exact_mod_cast Nat.mod_lt n hc
  have he : ((n%c:ℕ):ℝ)+(c:ℝ)*(n/c:ℕ) = n := by exact_mod_cast Nat.mod_add_div n c
  constructor
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(c:ℝ))).mpr
    nlinarith
  · apply (le_div_iff₀ hc').mpr
    have h := Nat.div_mul_le_self n c
    exact_mod_cast h

theorem q_pos (d : ℕ) (hd : 100000000 ≤ d) : 0 < q d := by
  unfold q
  omega

theorem ten_le_b (d : ℕ) (hd : 100000000 ≤ d) : 10 ≤ b d := by
  unfold b
  omega

theorem q_bounds (d : ℕ) (hd : 100000000 ≤ d) :
    (d:ℝ)/200000 ≤ (q d:ℝ) ∧ (q d:ℝ) ≤ (d:ℝ)/100000 := by
  have h := div_real_bounds d 100000 (by norm_num) (by omega)
  norm_num [q] at h ⊢
  exact h

theorem b_bounds (d : ℕ) (hd : 100000000 ≤ d) :
    (d:ℝ)/20000000 ≤ (b d:ℝ) ∧ (b d:ℝ) ≤ (d:ℝ)/10000000 := by
  have h := div_real_bounds d 10000000 (by norm_num) (by omega)
  norm_num [b] at h ⊢
  exact h

theorem m_bounds (N d : ℕ) (hd : 100000000 ≤ d) (hN : 2*d ≤ N) :
    1 ≤ m N d ∧ (N:ℝ)/(100000*(d:ℝ)) ≤ (m N d:ℝ) ∧
      (m N d:ℝ) ≤ (N:ℝ)/(100000*(d:ℝ))+1 := by
  have hd' : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hN' : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hr : (0:ℝ)<(N:ℝ)/(100000*(d:ℝ)) := by positivity
  exact ⟨Nat.one_le_ceil_iff.mpr hr, Nat.le_ceil _, (Nat.ceil_lt_add_one hr.le).le⟩

theorem lt_ratio_of_lt_m (N d f : ℕ) (hf : f < m N d) :
    (f:ℝ) < (N:ℝ)/(100000*(d:ℝ)) := by
  exact Nat.lt_ceil.mp hf

theorem product_bounds (N d : ℕ) (hd : 100000000 ≤ d) (hN : 2*d ≤ N) :
    (N:ℝ)/20000000000 ≤ (q d:ℝ)*(m N d:ℝ) ∧
      (N:ℝ)/2000000000000 ≤ (m N d:ℝ)*(b d:ℝ) := by
  have hd' : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hm := (m_bounds N d hd hN).2.1
  have hml : (N:ℝ) ≤ (m N d:ℝ)*(100000*(d:ℝ)) :=
    (div_le_iff₀ (by positivity : (0:ℝ)<100000*(d:ℝ))).mp hm
  have hq := (q_bounds d hd).1
  have hb := (b_bounds d hd).1
  have hqs : (d:ℝ) ≤ 200000*(q d:ℝ) := by linarith
  have hbs : (d:ℝ) ≤ 20000000*(b d:ℝ) := by linarith
  have hmq := mul_le_mul_of_nonneg_left hqs (Nat.cast_nonneg (m N d) : (0:ℝ) ≤ (m N d:ℝ))
  have hmb := mul_le_mul_of_nonneg_left hbs (Nat.cast_nonneg (m N d) : (0:ℝ) ≤ (m N d:ℝ))
  constructor <;> nlinarith

theorem m_le_order_div_degree (N d : ℕ) (hd : 100000000 ≤ d) (hN : 2*d ≤ N) :
    (m N d:ℝ) ≤ (N:ℝ)/(d:ℝ) := by
  have hd' : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hN' : (2:ℝ)*d ≤ N := by exact_mod_cast hN
  have hm := (m_bounds N d hd hN).2.2
  have hmul := mul_le_mul_of_nonneg_right hm hd'.le
  have hcancel : ((N:ℝ)/(100000*(d:ℝ)))*(d:ℝ) = (N:ℝ)/100000 := by
    field_simp
  apply (le_div_iff₀ hd').mpr
  nlinarith
end Erdos642.CampaignFe72210b.ForestParameters
