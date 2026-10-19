import Mathlib
import Openmath.Erdos643R3.Pw2312Defs

/-!
# pw2312 §4: the elementary inequalities (E1)–(E4) and the analytic cases of Theorem 2

the 23/12 argument §4 (SHA-256 `0617f8ac…`). All variables are natural numbers cast to `ℚ` (the text's
`p, q, x, y ≥ 0` integers), except in (E3), which is stated for rationals `p, q ≥ 0`.

* (E1) `E1`: `p ≥ 1 ⟹ S(p,q,y) ≥ p/(2(1+q)) − y/(2(1+q)²)`.
* (E2) `S_mono_p`, `S_anti_q`, `S_anti_y`: `S` is nondecreasing in `p`, nonincreasing in `q` and in `y`.
* (E3) `E3`; (E4) `E4`: `p, q ≥ 1 ⟹ S(p,q,y) + S(q,p,x) ≥ E4R p q x y`, where
  `E4R p q x y = 1 − (1/2)(1/(1+p) + 1/(1+q)) − y/(2(1+q)²) − x/(2(1+p)²)`; `E4R_mono` (nondecreasing in `p`, `q`).
* One-sided reduction: `S_93`, `S_one_sided` (`S(93,22,11) = 8649/4300 > 23/12`).
* Case I: `caseI_rel01` (relations `ρ_0`, `ρ_1` big ⟹ `Φ ≥ 23/12`).
* Case III: `kappa p u s = 1/(1+p+u) − 1/(2(1+p)) − s/(2(1+p)²)`, `K_ge` (`K ≥ 1 + κ + κ`), `kappa_anti_u`,
  `kappa_nonneg` (`κ(p;u,s) ≥ 0` when `1 + p ≥ u + 2s`).
-/

set_option autoImplicit false

namespace Erdos643R3
namespace Pw2312

/-! ## (E2) monotonicity of `S` -/

theorem S_mono_p {p p' : ℕ} (q y : ℕ) (h : p ≤ p') : S p q y ≤ S p' q y := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; rw [S_zero]; exact S_nonneg _ _ _
  unfold S
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp
  have hpp : (p : ℚ) ≤ p' := by exact_mod_cast h
  have hq : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  have hy : (0 : ℚ) ≤ y := Nat.cast_nonneg y
  rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
  have h1 : (0 : ℚ) ≤ (p' : ℚ) - p := by linarith
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg h1 (by linarith : (0 : ℚ) ≤ p)) (by linarith : (0:ℚ) ≤ p'))
    (by linarith : (0 : ℚ) ≤ 1 + q), mul_nonneg (mul_nonneg h1 hy) (by linarith : (0 : ℚ) ≤ p + p')]

theorem S_anti_q (p : ℕ) {q q' : ℕ} (y : ℕ) (h : q ≤ q') : S p q' y ≤ S p q y := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp [S_zero]
  unfold S
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp
  have hqq : (q : ℚ) ≤ q' := by exact_mod_cast h
  have hq : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  have hy : (0 : ℚ) ≤ y := Nat.cast_nonneg y
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

theorem S_anti_y (p q : ℕ) {y y' : ℕ} (h : y ≤ y') : S p q y' ≤ S p q y := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp [S_zero]
  unfold S
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp
  have hyy : (y : ℚ) ≤ y' := by exact_mod_cast h
  have hq : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  have hy : (0 : ℚ) ≤ y := Nat.cast_nonneg y
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

/-- (E2) in one step: `S` at a corner with smaller `p`, larger `q`, `y`. -/
theorem S_corner {p p' q q' y y' : ℕ} (hp : p ≤ p') (hq : q' ≤ q) (hy : y' ≤ y) :
    S p q y ≤ S p' q' y' :=
  (S_anti_y p q hy).trans ((S_anti_q p y' hq).trans (S_mono_p q' y' hp))

/-! ## (E1), (E3), (E4) -/

/-- (E1) `p ≥ 1 ⟹ S(p,q,y) ≥ p/(2(1+q)) − y/(2(1+q)²)`. -/
theorem E1 {p : ℕ} (q y : ℕ) (hp : 1 ≤ p) :
    (p : ℚ) / (2 * (1 + q)) - y / (2 * (1 + q) ^ 2) ≤ S p q y := by
  unfold S
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp
  have hq : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  have hy : (0 : ℚ) ≤ y := Nat.cast_nonneg y
  have e : (p : ℚ) / (2 * (1 + q)) - y / (2 * (1 + q) ^ 2) = (p * (1 + q) - y) / (2 * (1 + q) ^ 2) := by
    field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (y : ℚ), mul_nonneg hy hy]

/-- (E3) for rationals `p, q ≥ 0`. -/
theorem E3 {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    1 - (1 / 2) * (1 / (1 + p) + 1 / (1 + q)) ≤ (1 / 2) * (p / (1 + q) + q / (1 + p)) := by
  have h1 : (0 : ℚ) < 1 + p := by linarith
  have h2 : (0 : ℚ) < 1 + q := by linarith
  have key : (2 : ℚ) ≤ (1 + p) / (1 + q) + (1 + q) / (1 + p) := by
    rw [div_add_div _ _ h2.ne' h1.ne', le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (p - q)]
  have e1 : (1 + p) / (1 + q) = p / (1 + q) + 1 / (1 + q) := by field_simp; ring
  have e2 : (1 + q) / (1 + p) = q / (1 + p) + 1 / (1 + p) := by field_simp; ring
  rw [e1, e2] at key
  linarith

/-- The right side of (E4). -/
def E4R (p q x y : ℕ) : ℚ :=
  1 - (1 / 2) * (1 / (1 + (p : ℚ)) + 1 / (1 + (q : ℚ))) - y / (2 * (1 + (q : ℚ)) ^ 2) -
    x / (2 * (1 + (p : ℚ)) ^ 2)

/-- (E4) `p, q ≥ 1 ⟹ S(p,q,y) + S(q,p,x) ≥ 1 − (1/2)(1/(1+p) + 1/(1+q)) − y/(2(1+q)²) − x/(2(1+p)²)`. -/
theorem E4 {p q : ℕ} (x y : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) : E4R p q x y ≤ S p q y + S q p x := by
  have h1 := E1 q y hp
  have h2 := E1 p x hq
  have h3 := E3 (Nat.cast_nonneg p : (0 : ℚ) ≤ p) (Nat.cast_nonneg q : (0 : ℚ) ≤ q)
  unfold E4R
  have e : (1 / 2 : ℚ) * ((p : ℚ) / (1 + q) + q / (1 + p)) = (p : ℚ) / (2 * (1 + q)) + q / (2 * (1 + p)) := by
    field_simp
  linarith

theorem E4R_mono {p p' q q' : ℕ} (x y : ℕ) (hp : p ≤ p') (hq : q ≤ q') : E4R p q x y ≤ E4R p' q' x y := by
  unfold E4R
  have hp' : (p : ℚ) ≤ p' := by exact_mod_cast hp
  have hq' : (q : ℚ) ≤ q' := by exact_mod_cast hq
  have hp0 : (0 : ℚ) ≤ p := Nat.cast_nonneg p
  have hq0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  have hx : (0 : ℚ) ≤ x := Nat.cast_nonneg x
  have hy : (0 : ℚ) ≤ y := Nat.cast_nonneg y
  have a1 : 1 / (1 + (p' : ℚ)) ≤ 1 / (1 + p) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have a2 : 1 / (1 + (q' : ℚ)) ≤ 1 / (1 + q) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have a3 : (y : ℚ) / (2 * (1 + q') ^ 2) ≤ y / (2 * (1 + q) ^ 2) :=
    div_le_div_of_nonneg_left hy (by positivity) (by nlinarith)
  have a4 : (x : ℚ) / (2 * (1 + p') ^ 2) ≤ x / (2 * (1 + p) ^ 2) :=
    div_le_div_of_nonneg_left hx (by positivity) (by nlinarith)
  linarith

/-! ## Nonnegativity of the terms of `Φ` -/

theorem Phi_ge_t (π : Profile) : ((π.t0 : ℚ) + π.t1 + π.t2) / 6 ≤ Phi π := by
  unfold Phi
  have := S_nonneg π.f0 π.g1 π.t1; have := S_nonneg π.g1 π.f0 π.t0
  have := S_nonneg π.f1 π.g2 π.t2; have := S_nonneg π.g2 π.f1 π.t1
  have := S_nonneg π.f2 π.g0 π.t0; have := S_nonneg π.g0 π.f2 π.t2
  have : (0 : ℚ) ≤ 1 / (1 + (π.f0 : ℚ) + π.g0 + π.t0) := by positivity
  have : (0 : ℚ) ≤ 1 / (1 + (π.f1 : ℚ) + π.g1 + π.t1) := by positivity
  have : (0 : ℚ) ≤ 1 / (1 + (π.f2 : ℚ) + π.g2 + π.t2) := by positivity
  linarith

/-- `Φ ≥ t/6`, so `t ≥ 12` gives `Φ ≥ 2 ≥ 23/12`. -/
theorem Phi_of_t_ge (π : Profile) (h : 12 ≤ π.t0 + π.t1 + π.t2) : 23 / 12 ≤ Phi π := by
  have := Phi_ge_t π
  have h' : (12 : ℚ) ≤ (π.t0 : ℚ) + π.t1 + π.t2 := by exact_mod_cast h
  linarith

/-- Every single S-term is at most `Φ`. -/
theorem S_le_Phi (π : Profile) :
    S π.f0 π.g1 π.t1 ≤ Phi π ∧ S π.g1 π.f0 π.t0 ≤ Phi π ∧ S π.f1 π.g2 π.t2 ≤ Phi π ∧
      S π.g2 π.f1 π.t1 ≤ Phi π ∧ S π.f2 π.g0 π.t0 ≤ Phi π ∧ S π.g0 π.f2 π.t2 ≤ Phi π := by
  have := Phi_ge_t π
  have := S_nonneg π.f0 π.g1 π.t1; have := S_nonneg π.g1 π.f0 π.t0
  have := S_nonneg π.f1 π.g2 π.t2; have := S_nonneg π.g2 π.f1 π.t1
  have := S_nonneg π.f2 π.g0 π.t0; have := S_nonneg π.g0 π.f2 π.t2
  have : (0 : ℚ) ≤ ((π.t0 : ℚ) + π.t1 + π.t2) / 6 := by positivity
  have : (0 : ℚ) ≤ 1 / (1 + (π.f0 : ℚ) + π.g0 + π.t0) := by positivity
  have : (0 : ℚ) ≤ 1 / (1 + (π.f1 : ℚ) + π.g1 + π.t1) := by positivity
  have : (0 : ℚ) ≤ 1 / (1 + (π.f2 : ℚ) + π.g2 + π.t2) := by positivity
  unfold Phi at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The one-sided reduction -/

theorem S_93 : S 93 22 11 = 8649 / 4300 := by unfold S; norm_num

/-- `p ≥ 93`, `q ≤ 22`, `y ≤ 11` ⟹ `S(p,q,y) ≥ S(93,22,11) = 8649/4300 > 23/12`. -/
theorem S_one_sided {p q y : ℕ} (hp : 93 ≤ p) (hq : q ≤ 22) (hy : y ≤ 11) : 23 / 12 < S p q y := by
  have h := S_corner (p := 93) (q := 22) (y := 11) hp hq hy
  rw [S_93] at h
  linarith

/-! ## Case I -/

/-- For a big relation (`p, q ≥ 23`), the two S-terms sum to at least `1 − 1/24 − (x + y)/1152`. -/
theorem big_rel_bound {p q : ℕ} (x y : ℕ) (hp : 23 ≤ p) (hq : 23 ≤ q) :
    1 - 1 / 24 - ((x : ℚ) + y) / 1152 ≤ S p q y + S q p x := by
  refine le_trans ?_ (E4 x y (by omega) (by omega))
  unfold E4R
  have hp' : (23 : ℚ) ≤ p := by exact_mod_cast hp
  have hq' : (23 : ℚ) ≤ q := by exact_mod_cast hq
  have hx : (0 : ℚ) ≤ x := Nat.cast_nonneg x
  have hy : (0 : ℚ) ≤ y := Nat.cast_nonneg y
  have a1 : 1 / (1 + (p : ℚ)) ≤ 1 / 24 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have a2 : 1 / (1 + (q : ℚ)) ≤ 1 / 24 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have a3 : (y : ℚ) / (2 * (1 + q) ^ 2) ≤ y / 1152 :=
    div_le_div_of_nonneg_left hy (by norm_num) (by nlinarith)
  have a4 : (x : ℚ) / (2 * (1 + p) ^ 2) ≤ x / 1152 :=
    div_le_div_of_nonneg_left hx (by norm_num) (by nlinarith)
  linarith

/-- **Case I** for the relations `ρ_0` and `ρ_1`. -/
theorem caseI_rel01 (π : Profile) (h0 : 23 ≤ π.f0 ∧ 23 ≤ π.g1) (h1 : 23 ≤ π.f1 ∧ 23 ≤ π.g2) :
    23 / 12 ≤ Phi π := by
  have e0 := big_rel_bound π.t0 π.t1 h0.1 h0.2
  have e1 := big_rel_bound π.t1 π.t2 h1.1 h1.2
  have := S_nonneg π.f2 π.g0 π.t0; have := S_nonneg π.g0 π.f2 π.t2
  have : (0 : ℚ) ≤ 1 / (1 + (π.f0 : ℚ) + π.g0 + π.t0) := by positivity
  have : (0 : ℚ) ≤ 1 / (1 + (π.f1 : ℚ) + π.g1 + π.t1) := by positivity
  have : (0 : ℚ) ≤ 1 / (1 + (π.f2 : ℚ) + π.g2 + π.t2) := by positivity
  have : (0 : ℚ) ≤ π.t0 := Nat.cast_nonneg _
  have : (0 : ℚ) ≤ π.t1 := Nat.cast_nonneg _
  have : (0 : ℚ) ≤ π.t2 := Nat.cast_nonneg _
  unfold Phi
  linarith

/-! ## Case III: `κ` and `K ≥ 1 + κ + κ` -/

/-- `κ(p; u, s) = 1/(1+p+u) − 1/(2(1+p)) − s/(2(1+p)²)`. -/
def kappa (p u s : ℕ) : ℚ :=
  1 / (1 + (p : ℚ) + u) - 1 / (2 * (1 + (p : ℚ))) - s / (2 * (1 + (p : ℚ)) ^ 2)

/-- `K = 1/(1+n_A) + 1/(1+n_B) + e_c ≥ 1 + κ(ac; u, tA) + κ(bc; v, tB)` with `u = ab + tA`, `v = ba + tB`
(cyclic: `ac = f_0`, `ab = g_0`, `bc = g_1`, `ba = f_1`). -/
theorem K_ge (π : Profile) (hf : 1 ≤ π.f0) (hg : 1 ≤ π.g1) :
    1 + kappa π.f0 (π.g0 + π.t0) π.t0 + kappa π.g1 (π.f1 + π.t1) π.t1 ≤
      1 / (1 + (π.f0 : ℚ) + π.g0 + π.t0) + 1 / (1 + (π.f1 : ℚ) + π.g1 + π.t1) +
        (S π.f0 π.g1 π.t1 + S π.g1 π.f0 π.t0) := by
  have h := E4 π.t0 π.t1 hf hg
  unfold E4R at h
  unfold kappa
  have e1 : (1 : ℚ) + π.f0 + ((π.g0 + π.t0 : ℕ) : ℚ) = 1 + π.f0 + π.g0 + π.t0 := by push_cast; ring
  have e2 : (1 : ℚ) + π.g1 + ((π.f1 + π.t1 : ℕ) : ℚ) = 1 + π.f1 + π.g1 + π.t1 := by push_cast; ring
  rw [e1, e2]
  have e3 : (1 / 2 : ℚ) * (1 / (1 + (π.f0 : ℚ)) + 1 / (1 + (π.g1 : ℚ))) =
      1 / (2 * (1 + (π.f0 : ℚ))) + 1 / (2 * (1 + (π.g1 : ℚ))) := by field_simp
  linarith

theorem kappa_anti_u (p : ℕ) {u u' : ℕ} (s : ℕ) (h : u ≤ u') : kappa p u' s ≤ kappa p u s := by
  unfold kappa
  have hu : (u : ℚ) ≤ u' := by exact_mod_cast h
  have : 1 / (1 + (p : ℚ) + u') ≤ 1 / (1 + p + u) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-- `κ(p; u, s) ≥ 0` when `1 + p ≥ u + 2s` (the tail used for `k(u,s)`). -/
theorem kappa_nonneg {p u s : ℕ} (h : u + 2 * s ≤ 1 + p) : 0 ≤ kappa p u s := by
  unfold kappa
  have hx : ((u : ℚ) + 2 * s) ≤ 1 + p := by exact_mod_cast h
  have hu : (0 : ℚ) ≤ u := Nat.cast_nonneg u
  have hs : (0 : ℚ) ≤ s := Nat.cast_nonneg s
  have hp : (0 : ℚ) ≤ p := Nat.cast_nonneg p
  set x : ℚ := 1 + p with hxdef
  have hx1 : (1 : ℚ) ≤ x := by linarith
  have e : 1 / (x + u) - 1 / (2 * x) - s / (2 * x ^ 2) = (x ^ 2 - (u + s) * x - s * u) / (2 * x ^ 2 * (x + u)) := by
    field_simp; ring
  have e' : (1 : ℚ) + p + u = x + u := by rw [hxdef]
  rw [e', e]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hs (by linarith : (0 : ℚ) ≤ x - u - 2 * s), mul_nonneg (by linarith : (0 : ℚ) ≤ x) hs]

end Pw2312
end Erdos643R3
