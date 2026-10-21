import Mathlib
import Openmath.Erdos643R3.Pw2312

/-!
# Arithmetic of g1 §2–3: (G1)–(G3), Lemma 3g and the Lemma 2g bound

the pointwise argument (G1)–(G3) and the G1 argument Lemma 2g (arithmetic part) and
Lemma 3g, in the profile language of `Pw2312Defs`.

* `gfun p q = (1/2)(p/(1+q) + q/(1+p))`; `S_zero_y`: `S(p,q,0) = p/(2(1+q))`.
* (G1) `G1`: `g(p,q) + 1/(1+p) ≥ 1` for naturals; (G2) `G2`; (G3) `G3`: `x, y ≥ 1 ⟹
  (1/2)(1/(1+x) + 1/(1+y)) − 1/(1+x+y) ≤ 1/4`.
* Lemma 3g `lemma3g`: every feasible profile with `t = 0` has `Φ > 2`.
* Lemma 2g arithmetic: `Delta_step` (`D(i+1) − D(i) ≥ 1/3` for `n ≥ 1`), `Delta_ge_third`, and `lemma2g_profile`:
  a feasible profile in which some group has `n_X ≥ 1` and `i_X ≥ 1` isolated slots has `Φ⁺ ≥ 23/12 + 1/3 = 9/4`.
-/

set_option autoImplicit false

namespace Erdos643R3
namespace G1Arith

open Erdos643R3.Pw2312

/-- `g(p,q) = (1/2)(p/(1+q) + q/(1+p))`. -/
def gfun (p q : ℕ) : ℚ := (1 / 2) * ((p : ℚ) / (1 + q) + (q : ℚ) / (1 + p))

theorem gfun_comm (p q : ℕ) : gfun p q = gfun q p := by unfold gfun; ring

theorem S_zero_y (p q : ℕ) : S p q 0 = (p : ℚ) / (2 * (1 + q)) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp [S]
  unfold S
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have hq : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  field_simp
  ring

/-- With `t = 0` a relation contributes `S(p,q,0) + S(q,p,0) = g(p,q)`. -/
theorem rel_zero (p q : ℕ) : S p q 0 + S q p 0 = gfun p q := by
  rw [S_zero_y, S_zero_y, gfun]
  have : (0 : ℚ) < 1 + q := by positivity
  have : (0 : ℚ) < 1 + p := by positivity
  field_simp

/-- (G1) `g(p,q) + 1/(1+p) ≥ 1` for naturals `p, q` (`(p − q)(p − q − 1) ≥ 0`). -/
theorem G1 (p q : ℕ) : 1 ≤ gfun p q + 1 / (1 + (p : ℚ)) := by
  unfold gfun
  have hp : (0 : ℚ) ≤ p := Nat.cast_nonneg p
  have hq : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  have key : (0 : ℚ) ≤ ((p : ℚ) - q) * ((p : ℚ) - q - 1) := by
    rcases le_or_gt p q with h | h
    · have : (p : ℚ) ≤ q := by exact_mod_cast h
      nlinarith
    · have : (q : ℚ) + 1 ≤ p := by exact_mod_cast h
      nlinarith
  rw [show (1 / 2 : ℚ) * ((p : ℚ) / (1 + q) + (q : ℚ) / (1 + p)) + 1 / (1 + p) =
      ((p : ℚ) * (1 + p) + q * (1 + q) + 2 * (1 + q)) / (2 * (1 + p) * (1 + q)) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- (G2) `g(p,q) ≥ 1 − (1/2)(1/(1+p) + 1/(1+q))` (pw2312 (E3)). -/
theorem G2 (p q : ℕ) : 1 - (1 / 2) * (1 / (1 + (p : ℚ)) + 1 / (1 + (q : ℚ))) ≤ gfun p q :=
  E3 (Nat.cast_nonneg p) (Nat.cast_nonneg q)

/-- (G3) For naturals `x, y ≥ 1`: `(1/2)(1/(1+x) + 1/(1+y)) − 1/(1+x+y) ≤ 1/4`. -/
theorem G3 {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (1 / 2) * (1 / (1 + (x : ℚ)) + 1 / (1 + (y : ℚ))) - 1 / (1 + (x : ℚ) + y) ≤ 1 / 4 := by
  have hx' : (1 : ℚ) ≤ x := by exact_mod_cast hx
  have hy' : (1 : ℚ) ≤ y := by exact_mod_cast hy
  rw [show (1 / 2 : ℚ) * (1 / (1 + (x : ℚ)) + 1 / (1 + (y : ℚ))) - 1 / (1 + (x : ℚ) + y) =
      (((2 + x + y) * (1 + x + y)) - 2 * ((1 + x) * (1 + y))) / (2 * (1 + x) * (1 + y) * (1 + x + y)) by
      field_simp; ring]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ x - 1) (by linarith : (0 : ℚ) ≤ y - 1),
    mul_nonneg (by linarith : (0 : ℚ) ≤ x - 1) (by linarith : (0 : ℚ) ≤ y),
    mul_nonneg (by linarith : (0 : ℚ) ≤ y - 1) (by linarith : (0 : ℚ) ≤ x),
    sq_nonneg ((x : ℚ) - y), mul_nonneg (by linarith : (0 : ℚ) ≤ x) (by linarith : (0 : ℚ) ≤ y)]

/-! ## Lemma 3g -/

/-- `Φ` of a profile with `t = 0`. -/
theorem Phi_t0 (π : Profile) (h0 : π.t0 = 0) (h1 : π.t1 = 0) (h2 : π.t2 = 0) :
    Phi π = 1 / (1 + (π.f0 : ℚ) + π.g0) + 1 / (1 + (π.f1 : ℚ) + π.g1) + 1 / (1 + (π.f2 : ℚ) + π.g2) +
      gfun π.f0 π.g1 + gfun π.f1 π.g2 + gfun π.f2 π.g0 := by
  unfold Phi
  rw [h0, h1, h2, rel_zero, rel_zero, rel_zero]
  push_cast; ring

/-- Lemma 3g with `ρ_1, ρ_2` empty (`r = 1`). -/
theorem lemma3g_r1 (π : Profile) (h0 : π.t0 = 0) (h1 : π.t1 = 0) (h2 : π.t2 = 0)
    (e1 : π.f1 = 0 ∧ π.g2 = 0) (e2 : π.f2 = 0 ∧ π.g0 = 0) : 2 < Phi π := by
  have hP := Phi_t0 π h0 h1 h2
  have hg : gfun 0 0 = 0 := by simp [gfun]
  rw [e1.1, e1.2, e2.1, e2.2, hg] at hP
  simp only [Nat.cast_zero, add_zero, div_one] at hP
  have := G1 π.f0 π.g1
  have : (0 : ℚ) < 1 / (1 + (π.g1 : ℚ)) := by positivity
  linarith

/-- Lemma 3g with `ρ_0` empty (`r ≤ 2`). -/
theorem lemma3g_r2 (π : Profile) (h0 : π.t0 = 0) (h1 : π.t1 = 0) (h2 : π.t2 = 0)
    (e0 : π.f0 = 0 ∧ π.g1 = 0) : 2 < Phi π := by
  have hP := Phi_t0 π h0 h1 h2
  have hg : gfun 0 0 = 0 := by simp [gfun]
  rw [e0.1, e0.2, hg] at hP
  simp only [Nat.cast_zero, add_zero] at hP
  have a := G1 π.f1 π.g2
  have b := G1 π.g0 π.f2
  rw [gfun_comm π.g0 π.f2] at b
  have : (0 : ℚ) < 1 / (1 + (π.f2 : ℚ) + π.g2) := by positivity
  linarith

/-- Lemma 3g with all three relations nonempty (`r = 3`). -/
theorem lemma3g_r3 (π : Profile) (h0 : π.t0 = 0) (h1 : π.t1 = 0) (h2 : π.t2 = 0)
    (a0 : 1 ≤ π.f0) (b0 : 1 ≤ π.g0) (a1 : 1 ≤ π.f1) (b1 : 1 ≤ π.g1) (a2 : 1 ≤ π.f2) (b2 : 1 ≤ π.g2) :
    2 < Phi π := by
  rw [Phi_t0 π h0 h1 h2]
  have r0 := G2 π.f0 π.g1
  have r1 := G2 π.f1 π.g2
  have r2 := G2 π.f2 π.g0
  have c0 := G3 a0 b0
  have c1 := G3 a1 b1
  have c2 := G3 a2 b2
  linarith

/-- **Lemma 3g** (g1 §3). Every feasible profile with `t = 0` has `Φ > 2`. -/
theorem lemma3g (π : Profile) (hF : Feas π) (h0 : π.t0 = 0) (h1 : π.t1 = 0) (h2 : π.t2 = 0) :
    2 < Phi π := by
  obtain ⟨F0, F1, F2⟩ := hF
  rw [h0, h1, Nat.add_zero, Nat.add_zero] at F0
  rw [h1, h2, Nat.add_zero, Nat.add_zero] at F1
  rw [h2, h0, Nat.add_zero, Nat.add_zero] at F2
  have hr := Phi_rot π
  have hrr : Phi (rot (rot π)) = Phi π := by rw [Phi_rot, Phi_rot]
  by_cases z0 : π.f0 = 0
  · have : π.g1 = 0 := by
      rcases Nat.eq_zero_or_pos π.g1 with h | h
      · exact h
      · have := F0.mpr h; omega
    exact lemma3g_r2 π h0 h1 h2 ⟨z0, this⟩
  by_cases z1 : π.f1 = 0
  · have : π.g2 = 0 := by
      rcases Nat.eq_zero_or_pos π.g2 with h | h
      · exact h
      · have := F1.mpr h; omega
    rw [← hr]
    exact lemma3g_r2 (rot π) h1 h2 h0 ⟨z1, this⟩
  by_cases z2 : π.f2 = 0
  · have : π.g0 = 0 := by
      rcases Nat.eq_zero_or_pos π.g0 with h | h
      · exact h
      · have := F2.mpr h; omega
    rw [← hrr]
    exact lemma3g_r2 (rot (rot π)) h2 h0 h1 ⟨z2, this⟩
  exact lemma3g_r3 π h0 h1 h2 (by omega) (F2.mp (by omega)) (by omega) (F0.mp (by omega)) (by omega)
    (F1.mp (by omega))

/-! ## Lemma 2g arithmetic -/

/-- `D(i+1) − D(i) ≥ 1/3` for `n ≥ 1` (g1 §2), in the form `Δ(f,g,t,i+1) ≥ Δ(f,g,t,i) + 1/3`. -/
theorem Delta_step {f g t : ℕ} (hn : 1 ≤ f + g + t) (i : ℕ) :
    Delta f g t i + 1 / 3 ≤ Delta f g t (i + 1) := by
  unfold Delta
  have hn' : (1 : ℚ) ≤ (f : ℚ) + g + t := by exact_mod_cast hn
  have hi : (0 : ℚ) ≤ i := Nat.cast_nonneg i
  set m : ℚ := 1 + (f : ℚ) + g + t + i with hm
  have hm2 : (2 : ℚ) ≤ m := by rw [hm]; linarith
  have e1 : (1 : ℚ) + f + g + t + ((i + 1 : ℕ) : ℚ) = m + 1 := by rw [hm]; push_cast; ring
  rw [e1]
  have key : 1 / m - 1 / (m + 1) ≤ 1 / 6 := by
    rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  push_cast
  linarith

/-- `Δ_X ≥ 1/3` when `n_X ≥ 1` and `i_X ≥ 1`. -/
theorem Delta_ge_third {f g t i : ℕ} (hn : 1 ≤ f + g + t) (hi : 1 ≤ i) : 1 / 3 ≤ Delta f g t i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have := Delta_step hn j
  have := Delta_nonneg f g t j
  linarith

/-- **Lemma 2g, arithmetic part.** For a feasible profile with isolated counts `i₀, i₁, i₂`, if the group `X_0`
has `n_0 ≥ 1` and `i_0 ≥ 1`, then `Φ⁺ ≥ 23/12 + 1/3 = 9/4` (by Theorem 2 and `Δ_0 ≥ 1/3`). -/
theorem lemma2g_profile (π : Profile) (hF : Feas π) (i0 i1 i2 : ℕ) (hn : 1 ≤ π.f0 + π.g0 + π.t0)
    (hi : 1 ≤ i0) : 9 / 4 ≤ PhiPlus π i0 i1 i2 := by
  have h2 := Pw2312Main.theorem2 π hF
  have d0 := Delta_ge_third hn hi
  have d1 := Delta_nonneg π.f1 π.g1 π.t1 i1
  have d2 := Delta_nonneg π.f2 π.g2 π.t2 i2
  unfold PhiPlus
  linarith

end G1Arith
end Erdos643R3
