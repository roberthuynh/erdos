import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestParameters

namespace Erdos642.CampaignFe72210b.ForestOccupationParameters
open ForestParameters

noncomputable def h (N d : ℕ) : ℕ := (m N d+1)/2
noncomputable def u (N d : ℕ) : ℕ := q d*h N d

theorem half_le_h (N d : ℕ) : (m N d:ℝ)/2 ≤ (h N d:ℝ) := by
  have hn : m N d ≤ 2*h N d := by unfold h; omega
  have hr : (m N d:ℝ) ≤ 2*(h N d:ℝ) := by exact_mod_cast hn
  linarith

theorem support_bounds (N d : ℕ) (hd : 100000000≤d) (hN : 2*d≤N) :
    (N:ℝ)/40000000000 ≤ (u N d:ℝ) ∧
      (N:ℝ)/4000000000000 ≤ (h N d:ℝ)*(b d:ℝ) := by
  have hf := product_bounds N d hd hN
  have hh := half_le_h N d
  have hq := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (q d) : (0:ℝ)≤q d)
  have hb := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (b d) : (0:ℝ)≤b d)
  constructor
  · simp only [u, Nat.cast_mul]
    nlinarith [hf.1]
  · nlinarith [hf.2]

theorem threshold_product (N d t : ℕ) (hd : 100000000≤d) (hN : 2*d≤N) :
    (d:ℝ)*(t:ℝ)^2/(1000000000000000000000000*(N:ℝ)) ≤
      ((t:ℝ)*(b d:ℝ)/(600*(N:ℝ)))*
        ((t:ℝ)*(u N d:ℝ)/(300*(N:ℝ))) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hb := (b_bounds d hd).1
  have hu := (support_bounds N d hd hN).1
  have hbs : (d:ℝ)≤20000000*(b d:ℝ) := by linarith
  have hus : (N:ℝ)≤40000000000*(u N d:ℝ) := by linarith
  have hp := mul_le_mul hbs hus (Nat.cast_nonneg N : (0:ℝ)≤N)
    (show (0:ℝ)≤20000000*(b d:ℝ) by positivity)
  have hbase : (d:ℝ)*(N:ℝ) ≤
      (1000000000000000000000000/180000:ℝ)*(b d:ℝ)*(u N d:ℝ) := by
    have hbu : (0:ℝ)≤(b d:ℝ)*(u N d:ℝ) := by positivity
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hbase
    (show (0:ℝ)≤(t:ℝ)^2/(1000000000000000000000000*(N:ℝ)^2) by positivity)
  convert hm using 1
  all_goals try field_simp [ne_of_gt hNp]
  all_goals try ring
  all_goals rfl

theorem two_pow_le_exp (n : ℕ) : (2:ℝ)^n ≤ Real.exp (n:ℝ) := by
  have hh : (2:ℝ)≤Real.exp 1 := by have he := Real.add_one_le_exp 1; linarith
  calc
    (2:ℝ)^n ≤ (Real.exp 1)^n := pow_le_pow_left₀ (by norm_num) hh n
    _ = Real.exp (n:ℝ) := by rw [← Real.exp_nat_mul]; simp

theorem m_le_scaled_time (N d t : ℕ) (γ : ℝ)
    (hd : 100000000≤d) (hN : 2*d≤N)
    (hlarge : 1000000000000000000 ≤ (d:ℝ)*γ*(t:ℝ)/(N:ℝ)) :
    (m N d:ℝ) ≤ γ*(t:ℝ)/1000000000000000000 := by
  have hdp : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hl := (le_div_iff₀ hNp).mp hlarge
  apply (m_le_order_div_degree N d hd hN).trans
  apply (div_le_div_iff₀ hdp (by norm_num : (0:ℝ)<1000000000000000000)).mpr
  nlinarith

theorem q_le_order (N d : ℕ) (hd : 100000000≤d) (hN : 2*d≤N) :
    (q d:ℝ) ≤ (N:ℝ) := by
  have hq := (q_bounds d hd).2
  have hn : (2:ℝ)*d≤N := by exact_mod_cast hN
  have hdp : (0:ℝ)≤d := Nat.cast_nonneg d
  nlinarith

theorem raw_failure_bound (N d t : ℕ) (γ : ℝ)
    (hd : 100000000≤d) (hN : 2*d≤N) (hγ : 0<γ) (ht : 2≤t)
    (hlarge : 1000000000000000000 ≤ (d:ℝ)*γ*(t:ℝ)/(N:ℝ)) :
    (q d:ℝ)*(2:ℝ)^(m N d)*200*(N:ℝ)*
      Real.exp (-γ*(t:ℝ)*(h N d:ℝ)*(b d:ℝ)/(10000*(N:ℝ))) +
      200*(N:ℝ)*Real.exp (-γ*(t:ℝ)*(u N d:ℝ)/(10000*(N:ℝ))) ≤
      400*(N:ℝ)^2*Real.exp (-γ*(t:ℝ)/100000000000000000) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have htp : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have hgt : 0<γ*(t:ℝ) := mul_pos hγ htp
  have hs := support_bounds N d hd hN
  have hhb : (N:ℝ)≤4000000000000*((h N d:ℝ)*(b d:ℝ)) := by linarith [hs.2]
  have hu : (N:ℝ)≤40000000000*(u N d:ℝ) := by linarith [hs.1]
  have hrate1 : γ*(t:ℝ)/40000000000000000 ≤
      γ*(t:ℝ)*(h N d:ℝ)*(b d:ℝ)/(10000*(N:ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<40000000000000000)
      (by positivity : (0:ℝ)<10000*(N:ℝ))).mpr
    have hm := mul_le_mul_of_nonneg_left hhb hgt.le
    nlinarith
  have hrate2 : γ*(t:ℝ)/400000000000000 ≤
      γ*(t:ℝ)*(u N d:ℝ)/(10000*(N:ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<400000000000000)
      (by positivity : (0:ℝ)<10000*(N:ℝ))).mpr
    have hm := mul_le_mul_of_nonneg_left hu hgt.le
    nlinarith
  have hm := m_le_scaled_time N d t γ hd hN hlarge
  have hexp1 : (m N d:ℝ)-γ*(t:ℝ)*(h N d:ℝ)*(b d:ℝ)/(10000*(N:ℝ)) ≤
      -γ*(t:ℝ)/100000000000000000 := by linarith
  have hexp2 : -γ*(t:ℝ)*(u N d:ℝ)/(10000*(N:ℝ)) ≤
      -γ*(t:ℝ)/100000000000000000 := by
    calc
      _ = -(γ*(t:ℝ)*(u N d:ℝ)/(10000*(N:ℝ))) := by ring
      _ ≤ -(γ*(t:ℝ)/400000000000000) := neg_le_neg hrate2
      _ ≤ _ := by nlinarith
  have hqN := q_le_order N d hd hN
  have hfirst : (q d:ℝ)*(2:ℝ)^(m N d)*200*(N:ℝ)*
      Real.exp (-γ*(t:ℝ)*(h N d:ℝ)*(b d:ℝ)/(10000*(N:ℝ))) ≤
      200*(N:ℝ)^2*Real.exp (-γ*(t:ℝ)/100000000000000000) := by
    calc
      _ ≤ (q d:ℝ)*Real.exp (m N d:ℝ)*200*(N:ℝ)*
          Real.exp (-γ*(t:ℝ)*(h N d:ℝ)*(b d:ℝ)/(10000*(N:ℝ))) := by
        gcongr
        exact two_pow_le_exp _
      _ = (q d:ℝ)*200*(N:ℝ)*Real.exp
          ((m N d:ℝ)-γ*(t:ℝ)*(h N d:ℝ)*(b d:ℝ)/(10000*(N:ℝ))) := by
        rw [show -γ*(t:ℝ)*(h N d:ℝ)*(b d:ℝ)/(10000*(N:ℝ)) =
          -(γ*(t:ℝ)*(h N d:ℝ)*(b d:ℝ)/(10000*(N:ℝ))) by ring]
        rw [Real.exp_sub, Real.exp_neg]
        ring
      _ ≤ (N:ℝ)*200*(N:ℝ)*Real.exp (-γ*(t:ℝ)/100000000000000000) := by
        gcongr
      _ = _ := by ring
  have hsecond : 200*(N:ℝ)*Real.exp (-γ*(t:ℝ)*(u N d:ℝ)/(10000*(N:ℝ))) ≤
      200*(N:ℝ)^2*Real.exp (-γ*(t:ℝ)/100000000000000000) := by
    calc
      _ ≤ 200*(N:ℝ)*Real.exp (-γ*(t:ℝ)/100000000000000000) := by gcongr
      _ ≤ 200*(N:ℝ)^2*Real.exp (-γ*(t:ℝ)/100000000000000000) := by
        gcongr
        nlinarith
  linarith
end Erdos642.CampaignFe72210b.ForestOccupationParameters
