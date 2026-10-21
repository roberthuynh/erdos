import Mathlib

/-!
# Arithmetic lemmas of g3hp: Lemma 5 (`Ψ > 2`) and Lemma 6 (`f(a,c) ≥ 11/12`)

the G3h-prime argument §3 Lemma 5 and §4 Lemma 6, for natural-number parameters. The written proofs use
derivatives in a real variable and a square root; here every such step is replaced by an exact difference over the
integers (the variables are integers in the text):
* Lemma 6: `(A+1)/(2C) + C/(2A) ≥ 1 + 1/(2A)` for integers `A, C ≥ 1` (it is `(C − A)(C − A − 1) ≥ 0`), which
  gives `f(a,c) ≥ 1 − 1/(2(1+a)(2+a))` for `a ≥ 1`; `a = 0` is direct. `lemma6`, `lemma6_eq` (equality only at
  `(a,c) = (1,2)`).
* Lemma 5: case `r ≥ j` by the AM-GM pairing of the text; case `j ≥ r + 1` by `e_part` (the `e`-terms are at least
  their value at `e = 0`), `psi_mono` (the `d`-terms likewise), and `chi_mono` (`χ(k+1) ≥ χ(k)` for `k ≥ r + 2`).
* Lemma 9, arithmetic part (`lemma9_arith`): from the Lemma 3 bound `S1 ≥ L9 j d r` (with `d_A ≤ 1 + r` on `J_1`),
  `S1 < 13/12` and `r ≥ 1` give `j ≥ 2`, and `j ≥ 5`, `S1 − 1 ≥ 1/(2(2+j))` when `r ≥ j`. Lemma 3 itself (the
  slot analysis of `T1`) is not formalized here.
-/

set_option autoImplicit false

namespace Erdos643R3
namespace G3hpArith

/-! ## Lemma 6 -/

/-- `f(a,c) = 1/(1+c) + 1/(2(2+a)) + (c−1)/(2(1+a)) + a/(2(1+c))` (here `c ≥ 2`, so `c − 1` is exact). -/
def f6 (a c : ℕ) : ℚ :=
  1 / (1 + (c : ℚ)) + 1 / (2 * (2 + (a : ℚ))) + ((c : ℚ) - 1) / (2 * (1 + (a : ℚ))) + (a : ℚ) / (2 * (1 + (c : ℚ)))

/-- Integer AM-GM: `(A+1)/(2C) + C/(2A) ≥ 1 + 1/(2A)` for naturals `A, C ≥ 1`. -/
theorem int_amgm {A C : ℕ} (hA : 1 ≤ A) (hC : 1 ≤ C) :
    1 + 1 / (2 * (A : ℚ)) ≤ ((A : ℚ) + 1) / (2 * C) + (C : ℚ) / (2 * A) := by
  have hA' : (1 : ℚ) ≤ A := by exact_mod_cast hA
  have hC' : (1 : ℚ) ≤ C := by exact_mod_cast hC
  have key : (0 : ℚ) ≤ ((C : ℚ) - A) * ((C : ℚ) - A - 1) := by
    rcases le_or_gt C A with h | h
    · have : (C : ℚ) ≤ A := by exact_mod_cast h
      nlinarith
    · have : (A : ℚ) + 1 ≤ C := by exact_mod_cast h
      nlinarith
  rw [show (1 : ℚ) + 1 / (2 * A) = (2 * A + 1) / (2 * A) by field_simp,
    show ((A : ℚ) + 1) / (2 * C) + (C : ℚ) / (2 * A) = (A * (A + 1) + C * C) / (2 * A * C) by
      field_simp,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `f(a,c) ≥ 1 − 1/(2(1+a)(2+a))` for `a ≥ 1`, `c ≥ 2`. -/
theorem f6_ge {a c : ℕ} (ha : 1 ≤ a) (hc : 2 ≤ c) :
    1 - 1 / (2 * (1 + (a : ℚ)) * (2 + (a : ℚ))) ≤ f6 a c := by
  have h := int_amgm (A := 1 + a) (C := 1 + c) (by omega) (by omega)
  push_cast at h
  unfold f6
  have hc' : (2 : ℚ) ≤ c := by exact_mod_cast hc
  have ha' : (1 : ℚ) ≤ a := by exact_mod_cast ha
  have e : (1 : ℚ) / (1 + c) + 1 / (2 * (2 + a)) + ((c : ℚ) - 1) / (2 * (1 + a)) + a / (2 * (1 + c)) =
      ((1 + (a : ℚ)) + 1) / (2 * (1 + c)) + (1 + (c : ℚ)) / (2 * (1 + a)) - 1 / (1 + a) +
        1 / (2 * (2 + a)) := by
    field_simp; ring
  rw [e]
  have e2 : (1 : ℚ) - 1 / (2 * (1 + a) * (2 + a)) = 1 + 1 / (2 * (1 + a)) - 1 / (1 + a) + 1 / (2 * (2 + a)) := by
    field_simp; ring
  rw [e2]
  linarith

/-- `1/(1+c) + (c−1)/2 ≥ 5/6` for `c ≥ 2` (the case `a = 0`). -/
theorem c_part {c : ℕ} (hc : 2 ≤ c) : 5 / 6 ≤ 1 / (1 + (c : ℚ)) + ((c : ℚ) - 1) / 2 := by
  have hc' : (2 : ℚ) ≤ c := by exact_mod_cast hc
  have e : 1 / (1 + (c : ℚ)) + ((c : ℚ) - 1) / 2 - 5 / 6 = (3 * c + 1) * (c - 2) / (6 * (1 + c)) := by
    field_simp; ring
  have : 0 ≤ (3 * (c : ℚ) + 1) * (c - 2) / (6 * (1 + c)) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  linarith

/-- **Lemma 6** (g3hp §4). `f(a,c) ≥ 11/12` for integers `a ≥ 0`, `c ≥ 2`. -/
theorem lemma6 {a c : ℕ} (hc : 2 ≤ c) : 11 / 12 ≤ f6 a c := by
  rcases Nat.eq_zero_or_pos a with h0 | ha
  · subst h0
    unfold f6
    have hc' : (2 : ℚ) ≤ c := by exact_mod_cast hc
    rw [show (1 : ℚ) / (1 + c) + 1 / (2 * (2 + ((0 : ℕ) : ℚ))) + ((c : ℚ) - 1) / (2 * (1 + ((0 : ℕ) : ℚ))) +
        ((0 : ℕ) : ℚ) / (2 * (1 + c)) = 1 / (1 + c) + 1 / 4 + ((c : ℚ) - 1) / 2 by push_cast; ring]
    have := c_part hc
    linarith
  · have h := f6_ge ha hc
    have ha' : (1 : ℚ) ≤ a := by exact_mod_cast ha
    have : 1 / (2 * (1 + (a : ℚ)) * (2 + (a : ℚ))) ≤ 1 / 12 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith

/-- Lemma 6, equality case: `f(a,c) = 11/12` (with `c ≥ 2`) only at `(a,c) = (1,2)`. -/
theorem lemma6_eq {a c : ℕ} (hc : 2 ≤ c) (h : f6 a c = 11 / 12) : a = 1 ∧ c = 2 := by
  have hc' : (2 : ℚ) ≤ c := by exact_mod_cast hc
  rcases Nat.lt_or_ge a 1 with h0 | ha
  · have : a = 0 := by omega
    subst this
    unfold f6 at h
    rw [show (1 : ℚ) / (1 + c) + 1 / (2 * (2 + ((0 : ℕ) : ℚ))) + ((c : ℚ) - 1) / (2 * (1 + ((0 : ℕ) : ℚ))) +
        ((0 : ℕ) : ℚ) / (2 * (1 + c)) = 1 / (1 + c) + 1 / 4 + ((c : ℚ) - 1) / 2 by push_cast; ring] at h
    have := c_part hc
    linarith
  rcases Nat.lt_or_ge a 2 with h1 | ha2
  · have ha1 : a = 1 := by omega
    subst ha1
    refine ⟨rfl, ?_⟩
    unfold f6 at h
    push_cast at h
    have e : (1 : ℚ) / (1 + c) + 1 / (2 * (2 + 1)) + ((c : ℚ) - 1) / (2 * (1 + 1)) + 1 / (2 * (1 + c)) - 11 / 12 =
        ((c : ℚ) - 1) * (c - 2) / (4 * (1 + c)) := by field_simp; ring
    have h0 : ((c : ℚ) - 1) * (c - 2) / (4 * (1 + c)) = 0 := by rw [← e, h]; ring
    rcases div_eq_zero_iff.mp h0 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · linarith
      · have : (c : ℚ) = 2 := by linarith
        exact_mod_cast this
    · have : (0 : ℚ) < 4 * (1 + c) := by positivity
      linarith
  · exfalso
    have hge := f6_ge (by omega : 1 ≤ a) hc
    have ha' : (2 : ℚ) ≤ a := by exact_mod_cast ha2
    have : 1 / (2 * (1 + (a : ℚ)) * (2 + (a : ℚ))) ≤ 1 / 24 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith

/-! ## Lemma 5 -/

/-- `Ψ(j,d,e,r)` of g3hp Lemma 5. -/
def Psi (j d e r : ℕ) : ℚ :=
  2 / ((r : ℚ) + 2) + 1 / ((j : ℚ) + d + 2) + 1 / (2 + (j : ℚ)) + (j : ℚ) / ((r : ℚ) + 2) +
    (d : ℚ) / (2 * (1 + (r : ℚ))) + (e : ℚ) / (2 * (1 + (r : ℚ))) + (r : ℚ) / (2 * (1 + (j : ℚ) + d)) +
    (r : ℚ) / (2 * (1 + (j : ℚ) + e))

/-- AM-GM pairing: `x/(2y) + y/(2x) ≥ 1` for `x, y > 0`. -/
theorem amgm_pair {x y : ℚ} (hx : 0 < x) (hy : 0 < y) : 1 ≤ x / (2 * y) + y / (2 * x) := by
  rw [div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (x - y)]

/-- Lemma 5, case `r ≥ j`. -/
theorem lemma5_ge {j d e r : ℕ} (hr : 1 ≤ r) (hrj : j ≤ r) : 2 < Psi j d e r := by
  unfold Psi
  have hr' : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
  have hd : (0 : ℚ) ≤ d := Nat.cast_nonneg d
  have he : (0 : ℚ) ≤ e := Nat.cast_nonneg e
  have hrj' : (j : ℚ) ≤ r := by exact_mod_cast hrj
  set Pd : ℚ := 1 + j + d with hPd
  set Pe : ℚ := 1 + j + e with hPe
  have hPd1 : 1 + (j : ℚ) ≤ Pd := by rw [hPd]; linarith
  have hPe1 : 1 + (j : ℚ) ≤ Pe := by rw [hPe]; linarith
  have hPd0 : Pd ≠ 0 := ne_of_gt (by linarith)
  have hPd2 : Pd + 1 ≠ 0 := ne_of_gt (by linarith)
  have hPe0 : Pe ≠ 0 := ne_of_gt (by linarith)
  -- pairings
  have pd := amgm_pair (x := Pd) (y := (r : ℚ) + 1) (by linarith) (by linarith)
  have pe := amgm_pair (x := Pe) (y := (r : ℚ) + 1) (by linarith) (by linarith)
  have ed : (d : ℚ) / (2 * (1 + r)) + r / (2 * Pd) =
      (Pd / (2 * ((r : ℚ) + 1)) + ((r : ℚ) + 1) / (2 * Pd)) - (1 + j) / (2 * (1 + r)) - 1 / (2 * Pd) := by
    rw [hPd]; field_simp; ring
  have ee : (e : ℚ) / (2 * (1 + r)) + r / (2 * Pe) =
      (Pe / (2 * ((r : ℚ) + 1)) + ((r : ℚ) + 1) / (2 * Pe)) - (1 + j) / (2 * (1 + r)) - 1 / (2 * Pe) := by
    rw [hPe]; field_simp; ring
  have e1 : 1 / ((j : ℚ) + d + 2) = 1 / (Pd + 1) := by rw [hPd]; ring_nf
  -- the remaining terms
  have k1 : (2 + (j : ℚ)) / (r + 2) - (1 + j) / (1 + r) = (r - j) / ((r + 1) * (r + 2)) := by
    field_simp; ring
  have k2 : 0 ≤ ((r : ℚ) - j) / ((r + 1) * (r + 2)) := div_nonneg (by linarith) (by positivity)
  have k3 : 1 / (Pd + 1) - 1 / (2 * Pd) = (Pd - 1) / (2 * Pd * (Pd + 1)) := by
    field_simp; ring
  have k4 : 0 ≤ (Pd - 1) / (2 * Pd * (Pd + 1)) := div_nonneg (by linarith) (by positivity)
  have k5 : 1 / (2 * Pe) ≤ 1 / (2 * (1 + (j : ℚ))) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have k6 : 1 / (2 + (j : ℚ)) - 1 / (2 * (1 + j)) = j / (2 * (1 + j) * (2 + j)) := by
    field_simp; ring
  have k7 : 0 ≤ (j : ℚ) / (2 * (1 + j) * (2 + j)) := by positivity
  -- strictness: r > j, or r = j ≥ 1
  have strict : 0 < ((r : ℚ) - j) / ((r + 1) * (r + 2)) + (j : ℚ) / (2 * (1 + j) * (2 + j)) := by
    rcases lt_or_eq_of_le hrj' with h | h
    · have : 0 < ((r : ℚ) - j) / ((r + 1) * (r + 2)) := div_pos (by linarith) (by positivity)
      linarith
    · have : 0 < (j : ℚ) / (2 * (1 + j) * (2 + j)) := div_pos (by rw [h]; linarith) (by positivity)
      linarith
  have split : 2 / ((r : ℚ) + 2) + (j : ℚ) / ((r : ℚ) + 2) = (2 + (j : ℚ)) / (r + 2) := by ring
  have k8 : (1 + (j : ℚ)) / (1 + r) = 2 * ((1 + j) / (2 * (1 + r))) := by field_simp
  rw [e1]
  linarith

/-- The `e`-terms are at least their value at `e = 0` when `j ≥ r + 1`. -/
theorem e_part {j e r : ℕ} (hjr : r + 1 ≤ j) :
    (r : ℚ) / (2 * (1 + (j : ℚ))) ≤ (e : ℚ) / (2 * (1 + (r : ℚ))) + (r : ℚ) / (2 * (1 + (j : ℚ) + e)) := by
  have hjr' : (r : ℚ) + 1 ≤ j := by exact_mod_cast hjr
  have he : (0 : ℚ) ≤ e := Nat.cast_nonneg e
  have hr : (0 : ℚ) ≤ r := Nat.cast_nonneg r
  have key : (r : ℚ) / (2 * (1 + j)) - r / (2 * (1 + j + e)) = r * e / (2 * (1 + j) * (1 + j + e)) := by
    field_simp; ring
  have : (r : ℚ) * e / (2 * (1 + j) * (1 + j + e)) ≤ e / (2 * (1 + r)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (r : ℚ) * (1 + r) ≤ (1 + j) * (1 + j + e) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 he]
  linarith

/-- `ψ(d) ≥ ψ(0)` when `j ≥ r + 1`, `ψ(d) = 1/(2+j+d) + d/(2(1+r)) + r/(2(1+j+d))`. -/
theorem psi_mono {j d r : ℕ} (hjr : r + 1 ≤ j) :
    1 / (2 + (j : ℚ)) + (r : ℚ) / (2 * (1 + (j : ℚ))) ≤
      1 / (2 + (j : ℚ) + d) + (d : ℚ) / (2 * (1 + (r : ℚ))) + (r : ℚ) / (2 * (1 + (j : ℚ) + d)) := by
  have hjr' : (r : ℚ) + 1 ≤ j := by exact_mod_cast hjr
  have hd : (0 : ℚ) ≤ d := Nat.cast_nonneg d
  have hr : (0 : ℚ) ≤ r := Nat.cast_nonneg r
  have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
  -- difference = d · [1/(2(1+r)) − 1/((2+j)(2+j+d)) − r/(2(1+j)(1+j+d))]
  have key : 1 / (2 + (j : ℚ) + d) + (d : ℚ) / (2 * (1 + r)) + r / (2 * (1 + j + d)) -
      (1 / (2 + (j : ℚ)) + r / (2 * (1 + j))) =
      d * (1 / (2 * (1 + (r : ℚ))) - 1 / ((2 + j) * (2 + j + d)) - r / (2 * (1 + j) * (1 + j + d))) := by
    field_simp; ring
  have b1 : 1 / ((2 + (j : ℚ)) * (2 + j + d)) ≤ 1 / ((r + 3) ^ 2) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have b2 : (r : ℚ) / (2 * (1 + j) * (1 + j + d)) ≤ r / (2 * (r + 2) ^ 2) :=
    div_le_div_of_nonneg_left hr (by positivity) (by nlinarith)
  have b3 : 1 / ((r : ℚ) + 3) ^ 2 + r / (2 * (r + 2) ^ 2) ≤ 1 / (2 * (1 + r)) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (r : ℚ), mul_nonneg hr (sq_nonneg (r : ℚ)), mul_nonneg hr hr]
  have : 0 ≤ (d : ℚ) * (1 / (2 * (1 + (r : ℚ))) - 1 / ((2 + j) * (2 + j + d)) - r / (2 * (1 + j) * (1 + j + d))) :=
    mul_nonneg hd (by linarith)
  linarith

/-- `χ(k) = (k+1)/(r+2) + 2/(k+1) + r/k`. -/
def chi (r k : ℕ) : ℚ := ((k : ℚ) + 1) / ((r : ℚ) + 2) + 2 / ((k : ℚ) + 1) + (r : ℚ) / k

theorem chi_step {r k : ℕ} (hk : r + 2 ≤ k) : chi r k ≤ chi r (k + 1) := by
  unfold chi
  have hk' : (r : ℚ) + 2 ≤ k := by exact_mod_cast hk
  have hr : (0 : ℚ) ≤ r := Nat.cast_nonneg r
  have hk0 : (k : ℚ) ≠ 0 := ne_of_gt (by linarith)
  push_cast
  have key : (((k : ℚ) + 1 + 1) / ((r : ℚ) + 2) + 2 / ((k : ℚ) + 1 + 1) + r / ((k : ℚ) + 1)) -
      (((k : ℚ) + 1) / ((r : ℚ) + 2) + 2 / ((k : ℚ) + 1) + r / k) =
      1 / ((r : ℚ) + 2) - 2 / ((k + 1) * (k + 2)) - r / (k * (k + 1)) := by
    field_simp; ring
  have b1 : 2 / (((k : ℚ) + 1) * (k + 2)) ≤ 2 / ((r + 3) * (r + 4)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have b2 : (r : ℚ) / (k * (k + 1)) ≤ r / ((r + 2) * (r + 3)) :=
    div_le_div_of_nonneg_left hr (by positivity) (by nlinarith)
  have b3 : (r : ℚ) / ((r + 2) * (r + 3)) + 2 / ((r + 3) * (r + 4)) ≤ 1 / (r + 2) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hr hr, mul_nonneg hr (mul_nonneg hr hr)]
  linarith

theorem chi_mono {r k : ℕ} (hk : r + 2 ≤ k) : chi r (r + 2) ≤ chi r k := by
  induction k, hk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact ih.trans (chi_step hk)

theorem chi_base (r : ℕ) : 2 < chi r (r + 2) := by
  unfold chi
  have hr : (0 : ℚ) ≤ r := Nat.cast_nonneg r
  push_cast
  have e : ((r : ℚ) + 2 + 1) / ((r : ℚ) + 2) + 2 / ((r : ℚ) + 2 + 1) + r / ((r : ℚ) + 2) =
      2 + ((r : ℚ) + 1) / ((r + 2) * (r + 3)) := by field_simp; ring
  rw [e]
  have : 0 < ((r : ℚ) + 1) / ((r + 2) * (r + 3)) := by positivity
  linarith

/-- Lemma 5, case `j ≥ r + 1`. -/
theorem lemma5_lt {j d e r : ℕ} (hjr : r + 1 ≤ j) : 2 < Psi j d e r := by
  have h1 := e_part (e := e) hjr
  have h2 := psi_mono (d := d) hjr
  have h3 := chi_mono (r := r) (k := j + 1) (by omega)
  have h4 := chi_base r
  have h5 : 2 < chi r (j + 1) := lt_of_lt_of_le h4 h3
  unfold chi at h5
  unfold Psi
  push_cast at h5
  have e1 : 1 / ((j : ℚ) + d + 2) = 1 / (2 + (j : ℚ) + d) := by ring_nf
  have e2 : (r : ℚ) / ((j : ℚ) + 1) = r / (2 * (1 + j)) + r / (2 * (1 + j)) := by field_simp; ring
  have e3 : ((j : ℚ) + 1 + 1) / ((r : ℚ) + 2) = 2 / ((r : ℚ) + 2) + j / ((r : ℚ) + 2) := by field_simp; ring
  have e4 : 2 / ((j : ℚ) + 1 + 1) = 1 / (2 + (j : ℚ)) + 1 / (2 + (j : ℚ)) := by field_simp; ring
  rw [e1]
  linarith

/-- **Lemma 5** (g3hp §3). For integers `j, d, e ≥ 0` and `r ≥ 1`: `Ψ(j,d,e,r) > 2`. -/
theorem lemma5 {j d e r : ℕ} (hr : 1 ≤ r) : 2 < Psi j d e r := by
  rcases le_or_gt j r with h | h
  · exact lemma5_ge hr h
  · exact lemma5_lt (by omega)

/-! ## Lemma 9 (arithmetic part) -/

/-- The lower bound for `S1` of g3hp Lemma 3 with every `d_A(z) ≤ 1 + r` on `J_1` (`|J_1| = j`), as used in the
proof of Lemma 9: `1/(2+j+d) + 1/(2+r) + 1/(2(2+j)) + j/(2(2+r)) + d/(2(1+r)) + r/(2(1+j+d))`. -/
def L9 (j d r : ℕ) : ℚ :=
  1 / (2 + (j : ℚ) + d) + 1 / (2 + (r : ℚ)) + 1 / (2 * (2 + (j : ℚ))) + (j : ℚ) / (2 * (2 + (r : ℚ))) +
    (d : ℚ) / (2 * (1 + (r : ℚ))) + (r : ℚ) / (2 * (1 + (j : ℚ) + d))

/-- `L9 ≥ 1 + 1/(2(2+j))` when `r ≥ j` (the pairing of Lemma 5). -/
theorem L9_ge {j d r : ℕ} (hrj : j ≤ r) : 1 + 1 / (2 * (2 + (j : ℚ))) ≤ L9 j d r := by
  unfold L9
  have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
  have hd : (0 : ℚ) ≤ d := Nat.cast_nonneg d
  have hrj' : (j : ℚ) ≤ r := by exact_mod_cast hrj
  set Pd : ℚ := 1 + j + d with hPd
  have hPd1 : 1 + (j : ℚ) ≤ Pd := by rw [hPd]; linarith
  have hPd0 : Pd ≠ 0 := ne_of_gt (by linarith)
  have hPd2 : Pd + 1 ≠ 0 := ne_of_gt (by linarith)
  have pd := amgm_pair (x := Pd) (y := (r : ℚ) + 1) (by linarith) (by linarith)
  have ed : (d : ℚ) / (2 * (1 + r)) + r / (2 * Pd) =
      (Pd / (2 * ((r : ℚ) + 1)) + ((r : ℚ) + 1) / (2 * Pd)) - (1 + j) / (2 * (1 + r)) - 1 / (2 * Pd) := by
    rw [hPd]; field_simp; ring
  have e1 : 1 / (2 + (j : ℚ) + d) = 1 / (Pd + 1) := by rw [hPd]; ring_nf
  have k1 : 1 / (2 + (r : ℚ)) + (j : ℚ) / (2 * (2 + r)) - (1 + j) / (2 * (1 + r)) =
      (r - j) / (2 * (1 + r) * (2 + r)) := by
    field_simp; ring
  have k2 : 0 ≤ ((r : ℚ) - j) / (2 * (1 + r) * (2 + r)) := div_nonneg (by linarith) (by positivity)
  have k3 : 1 / (Pd + 1) - 1 / (2 * Pd) = (Pd - 1) / (2 * Pd * (Pd + 1)) := by
    field_simp; ring
  have k4 : 0 ≤ (Pd - 1) / (2 * Pd * (Pd + 1)) := div_nonneg (by linarith) (by positivity)
  rw [e1]
  linarith

/-- **Lemma 9, arithmetic part** (g3hp §5). Let `S1 ≥ L9 j d r` (Lemma 3 with `d_A ≤ 1 + r` on `J_1`) and `r ≥ 1`.
If `T1` is deficient (`S1 < 13/12`), then `j ≥ 2`; if moreover `r ≥ j`, then `j ≥ 5` and `S1 − 1 ≥ 1/(2(2+j))`. -/
theorem lemma9_arith {j d r : ℕ} (hr : 1 ≤ r) {S1 : ℚ} (hS : L9 j d r ≤ S1) (hdef : S1 < 13 / 12) :
    2 ≤ j ∧ (j ≤ r → 5 ≤ j ∧ 1 / (2 * (2 + (j : ℚ))) ≤ S1 - 1) := by
  have key : j ≤ r → 5 ≤ j ∧ 1 / (2 * (2 + (j : ℚ))) ≤ S1 - 1 := by
    intro hrj
    have h := L9_ge (d := d) hrj
    refine ⟨?_, by linarith⟩
    by_contra hj
    have hj4 : (j : ℚ) ≤ 4 := by exact_mod_cast (show j ≤ 4 by omega)
    have : (1 : ℚ) / 12 ≤ 1 / (2 * (2 + (j : ℚ))) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    linarith
  refine ⟨?_, key⟩
  rcases le_or_gt j r with h | h
  · have := (key h).1; omega
  · omega

end G3hpArith
end Erdos643R3
