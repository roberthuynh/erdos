import Openmath.Erdos643R3.WBox

set_option autoImplicit false

namespace Erdos643R3.WBox

theorem betaW_lower (N m2 : ℕ) : (1 : ℚ) / 6 ≤ betaW N m2 := by
  have h1 : (0 : ℚ) ≤ 1 / (2 + (N : ℚ)) := by positivity
  have h2 : (0 : ℚ) ≤ 1 / (2 * (2 + (m2 : ℚ))) := by positivity
  unfold betaW
  split_ifs <;> linarith

theorem tauW_lt (m m2 : ℕ) : tauW m m2 false < (5 : ℚ) / 12 := by
  have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hr : (m : ℚ) / (3 * ((m : ℚ) + 3)) < 1 / 3 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℚ) < 3 * ((m : ℚ) + 3))).2
    linarith
  unfold tauW
  simp only [Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> linarith

theorem tauW_le_mass (m m2 : ℕ) : tauW m m2 false ≤ ((m : ℚ) + m2) / 6 := by
  have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℚ) ≤ m2 := Nat.cast_nonneg m2
  unfold tauW
  simp only [Bool.false_eq_true, ↓reduceIte]
  split_ifs with h0 h1 h2 h3 h4
  · subst m; subst m2; norm_num
  · subst m; positivity
  · subst m; subst m2; norm_num
  · subst m; linarith
  · have hm2 : (2 : ℚ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
    have hfrac : (m : ℚ) / (3 * ((m : ℚ) + 3)) ≤ (m : ℚ) / 6 := by
      apply div_le_div_of_nonneg_left hm (by norm_num)
      linarith
    subst m2
    norm_num at *
    linarith
  · have hfrac : (m : ℚ) / (3 * ((m : ℚ) + 3)) ≤ (m : ℚ) / 6 := by
      apply div_le_div_of_nonneg_left hm (by norm_num)
      linarith
    linarith

/-- A single side of the relation-cost estimate, including its distinguished slot. -/
def sideW (n p m : ℕ) : ℚ :=
  if 1 ≤ m then 1 / (2 * (1 + (p : ℚ) + m)) + ((n : ℚ) - 1) / (2 * (1 + (p : ℚ)))
  else (n : ℚ) / (2 * (1 + (p : ℚ)))

theorem XW_sides (nB nC m m2 : ℕ) :
    XW nB nC m m2 false = sideW nB nC m + sideW nC nB m2 := rfl

theorem sideW_nonneg (n p m : ℕ) (h : 1 ≤ m → 1 ≤ n) : 0 ≤ sideW n p m := by
  unfold sideW
  split_ifs with hm
  · have hn : (1 : ℚ) ≤ n := by exact_mod_cast h hm
    positivity
  · positivity

theorem sideW_strip (n p m : ℕ) (hn : 1 ≤ n) :
    ((n : ℚ) - 1) / (2 * (1 + (p : ℚ))) ≤ sideW n p m := by
  have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
  unfold sideW
  split_ifs
  · have hh : (0 : ℚ) ≤ 1 / (2 * (1 + (p : ℚ) + m)) := by positivity
    linarith
  · apply div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem stripped_large (n p : ℕ) (hn : 7 ≤ n) (hp : 7 ≤ p) :
    (3 : ℚ) / 4 ≤ ((n : ℚ) - 1) / (2 * (1 + (p : ℚ))) +
      ((p : ℚ) - 1) / (2 * (1 + (n : ℚ))) := by
  have hn' : (7 : ℚ) ≤ n := by exact_mod_cast hn
  have hp' : (7 : ℚ) ≤ p := by exact_mod_cast hp
  have hn0 : (0 : ℚ) < 1 + n := by positivity
  have hp0 : (0 : ℚ) < 1 + p := by positivity
  have hprod : (0 : ℚ) ≤ ((n : ℚ) - 7) * ((p : ℚ) - 7) := mul_nonneg (by linarith) (by linarith)
  have hsq := sq_nonneg ((n : ℚ) - p)
  field_simp
  nlinarith

theorem stripped_imbalanced (n p : ℕ) (hn : 12 ≤ n) (hp : p ≤ 6) :
    (3 : ℚ) / 4 ≤ ((n : ℚ) - 1) / (2 * (1 + (p : ℚ))) := by
  have hn' : (12 : ℚ) ≤ n := by exact_mod_cast hn
  have hp' : (p : ℚ) ≤ 6 := by exact_mod_cast hp
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2 * (1 + (p : ℚ)))).2
  linarith

theorem sideW_pair_large (n p m m2 : ℕ) (hn : 1 ≤ n) (hp : 1 ≤ p)
    (hlarge : 12 ≤ n ∨ 12 ≤ p) : (3 : ℚ) / 4 ≤ sideW n p m + sideW p n m2 := by
  have hsn := sideW_strip n p m hn
  have hsp := sideW_strip p n m2 hp
  have hnn := sideW_nonneg n p m (fun _ => hn)
  have hpn := sideW_nonneg p n m2 (fun _ => hp)
  rcases hlarge with hlarge | hlarge
  · by_cases hp7 : 7 ≤ p
    · have hh := stripped_large n p (by omega) hp7
      linarith
    · have hh := stripped_imbalanced n p hlarge (by omega)
      linarith
  · by_cases hn7 : 7 ≤ n
    · have hh := stripped_large n p hn7 (by omega)
      linarith
    · have hh := stripped_imbalanced p n hlarge (by omega)
      linarith

/-- Lemma W Step 3, together with the existing kernel finite certificate.
This is a numerical theorem. It does not assert that a host has these parameters. -/
theorem w_unbounded (nB nC m m2 : ℕ) (hmass : 1 ≤ m + m2)
    (hadm : admW nB nC m m2 false = true) :
    tauW m m2 false ≤ thetaW nB nC m m2 false := by
  have hadm' := hadm
  simp only [admW, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not] at hadm'
  have hnB : 1 ≤ m → 1 ≤ nB := by omega
  have hnC : 1 ≤ m2 → 1 ≤ nC := by omega
  have hzB : nC = 0 → nB ≤ 1 := by
    intro hz
    by_cases hm : 1 ≤ m <;> simp only [hm, ↓reduceIte] at hadm' <;> omega
  have hzC : nB = 0 → nC ≤ 1 := by
    intro hz
    by_cases hm : 1 ≤ m2 <;> simp only [hm, ↓reduceIte] at hadm' <;> omega
  have hX : 0 ≤ XW nB nC m m2 false := by
    rw [XW_sides]
    exact add_nonneg (sideW_nonneg nB nC m hnB) (sideW_nonneg nC nB m2 hnC)
  have hb := betaW_lower (nB + m2) m2
  by_cases hm7 : 7 ≤ m + m2
  · have hm7' : (7 : ℚ) ≤ (m : ℚ) + m2 := by exact_mod_cast hm7
    have ht := tauW_lt m m2
    unfold thetaW
    linarith
  · by_cases hbig : 12 ≤ nB ∨ 12 ≤ nC
    · have hB : 1 ≤ nB := by omega
      have hC : 1 ≤ nC := by omega
      have hxx : (3 : ℚ) / 4 ≤ XW nB nC m m2 false := by
        rw [XW_sides]
        exact sideW_pair_large nB nC m m2 hB hC hbig
      have ht := tauW_le_mass m m2
      unfold thetaW
      linarith
    · apply wbox nB nC m m2 false _ hadm
      have hB : nB ≤ 11 := by omega
      have hC : nC ≤ 11 := by omega
      have hsum : m + m2 ≤ 6 := by omega
      simp [inBox, hB, hC, hmass, hsum]

end Erdos643R3.WBox
