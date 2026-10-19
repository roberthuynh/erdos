import Mathlib

/-!
# The convexity bound `Φ` (pw2312 §3; Erdős 643, r = 3)

Definitions of the 23/12 argument §3 (SHA-256 `0617f8ac…`), in the cyclic form of the text:
`X_0 = A, X_1 = B, X_2 = C`; `ρ_0 = R_c` joins `X_0, X_1`, `ρ_1 = R_a` joins `X_1, X_2`, `ρ_2 = R_b` joins `X_2, X_0`;
`f_i, g_i` are the type-1 counts of `X_i` in `ρ_i` and `ρ_{i-1}`, `t_i` its type-2 count:
`(f_0, g_0, t_0) = (ac, ab, tA)`, `(f_1, g_1, t_1) = (ba, bc, tB)`, `(f_2, g_2, t_2) = (cb, ca, tC)`.

* `S p q y = p² / (2 (p + p q + y))` over `ℚ`; it is `0` at `p = 0` (`S_zero`), as in the text.
* `Phi π = Σ_i [1/(1 + f_i + g_i + t_i) + t_i/6 + S(f_i, g_{i+1}, t_{i+1}) + S(g_{i+1}, f_i, t_i)]`.
  `Phi_named` checks it against the named display of §3.
* `Feas π` is (F): `f_i + t_i ≥ 1 ↔ g_{i+1} + t_{i+1} ≥ 1` for each `i`. `Feas_named` checks the named form.
* `rot` is the shift `i ↦ i + 1`; `Phi_rot`, `Feas_rot`: both are invariant.
* `PhiPlus π i₀ i₁ i₂ = Phi π + Σ_X Δ_X`, `Δ_X = 1/(1 + n_X + i_X) + i_X/2 − 1/(1 + n_X)` (g1 (0.1)), and
  `Phi_le_PhiPlus`.
-/

set_option autoImplicit false

namespace Erdos643R3
namespace Pw2312

/-- `S(p,q,y) = p²/(2(p + pq + y))` (and `S(0,q,y) = 0`). -/
def S (p q y : ℕ) : ℚ := (p : ℚ) ^ 2 / (2 * ((p : ℚ) + (p : ℚ) * q + y))

theorem S_zero (q y : ℕ) : S 0 q y = 0 := by simp [S]

theorem S_nonneg (p q y : ℕ) : 0 ≤ S p q y := by unfold S; positivity

/-- A profile in the cyclic coordinates of pw2312 §3. -/
structure Profile where
  f0 : ℕ
  g0 : ℕ
  t0 : ℕ
  f1 : ℕ
  g1 : ℕ
  t1 : ℕ
  f2 : ℕ
  g2 : ℕ
  t2 : ℕ

/-- `Φ` in the cyclic form of pw2312 §3. -/
def Phi (π : Profile) : ℚ :=
  1 / (1 + (π.f0 : ℚ) + π.g0 + π.t0) + 1 / (1 + (π.f1 : ℚ) + π.g1 + π.t1) +
    1 / (1 + (π.f2 : ℚ) + π.g2 + π.t2) + ((π.t0 : ℚ) + π.t1 + π.t2) / 6 +
    (S π.f0 π.g1 π.t1 + S π.g1 π.f0 π.t0) + (S π.f1 π.g2 π.t2 + S π.g2 π.f1 π.t1) +
    (S π.f2 π.g0 π.t0 + S π.g0 π.f2 π.t2)

/-- Feasibility (F). -/
def Feas (π : Profile) : Prop :=
  (1 ≤ π.f0 + π.t0 ↔ 1 ≤ π.g1 + π.t1) ∧ (1 ≤ π.f1 + π.t1 ↔ 1 ≤ π.g2 + π.t2) ∧
    (1 ≤ π.f2 + π.t2 ↔ 1 ≤ π.g0 + π.t0)

/-- The cyclic shift `i ↦ i + 1`. -/
def rot (π : Profile) : Profile := ⟨π.f1, π.g1, π.t1, π.f2, π.g2, π.t2, π.f0, π.g0, π.t0⟩

theorem Phi_rot (π : Profile) : Phi (rot π) = Phi π := by
  simp only [Phi, rot]; ring

theorem Feas_rot (π : Profile) : Feas (rot π) ↔ Feas π := by
  simp only [Feas, rot]; tauto

/-- `Φ` exactly as displayed in pw2312 §3 with the named counts. -/
def PhiNamed (ab ac bc ba ca cb tA tB tC : ℕ) : ℚ :=
  1 / (1 + ((ab + ac + tA : ℕ) : ℚ)) + 1 / (1 + ((bc + ba + tB : ℕ) : ℚ)) +
    1 / (1 + ((ca + cb + tC : ℕ) : ℚ)) + ((tA + tB + tC : ℕ) : ℚ) / 6 +
    (S ac bc tB + S bc ac tA) + (S ba ca tC + S ca ba tB) + (S cb ab tA + S ab cb tC)

theorem Phi_named (ab ac bc ba ca cb tA tB tC : ℕ) :
    PhiNamed ab ac bc ba ca cb tA tB tC = Phi ⟨ac, ab, tA, ba, bc, tB, cb, ca, tC⟩ := by
  simp only [PhiNamed, Phi]; push_cast; ring

/-- (F) exactly as stated in pw2312 §3. -/
theorem Feas_named (ab ac bc ba ca cb tA tB tC : ℕ) :
    Feas ⟨ac, ab, tA, ba, bc, tB, cb, ca, tC⟩ ↔
      ((1 ≤ ac + tA ↔ 1 ≤ bc + tB) ∧ (1 ≤ ba + tB ↔ 1 ≤ ca + tC) ∧ (1 ≤ cb + tC ↔ 1 ≤ ab + tA)) :=
  Iff.rfl

/-- `Δ_X = 1/(1 + n_X + i_X) + i_X/2 − 1/(1 + n_X)` with `n_X = f + g + t` (g1 (0.1)). -/
def Delta (f g t i : ℕ) : ℚ :=
  1 / (1 + (f : ℚ) + g + t + i) + (i : ℚ) / 2 - 1 / (1 + (f : ℚ) + g + t)

theorem Delta_nonneg (f g t i : ℕ) : 0 ≤ Delta f g t i := by
  unfold Delta
  set n : ℚ := (f : ℚ) + g + t with hn_def
  have hn : (0 : ℚ) ≤ n := by positivity
  have hi : (0 : ℚ) ≤ i := Nat.cast_nonneg i
  have e1 : (1 : ℚ) + f + g + t + i = 1 + n + i := by rw [hn_def]; ring
  have e2 : (1 : ℚ) + f + g + t = 1 + n := by rw [hn_def]; ring
  rw [e1, e2]
  have key : 1 / (1 + n) - 1 / (1 + n + i) = i / ((1 + n) * (1 + n + i)) := by
    field_simp; ring
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0; simp
  · have hi1 : (1 : ℚ) ≤ i := by exact_mod_cast h0
    have hden : (2 : ℚ) ≤ (1 + n) * (1 + n + i) := by nlinarith
    have : (i : ℚ) / ((1 + n) * (1 + n + i)) ≤ i / 2 :=
      div_le_div_of_nonneg_left hi (by norm_num) hden
    linarith

/-- `Φ⁺ = Φ + Σ_X Δ_X` with the isolated-slot counts `i₀, i₁, i₂` (g1 (0.1)). -/
def PhiPlus (π : Profile) (i0 i1 i2 : ℕ) : ℚ :=
  Phi π + Delta π.f0 π.g0 π.t0 i0 + Delta π.f1 π.g1 π.t1 i1 + Delta π.f2 π.g2 π.t2 i2

theorem Phi_le_PhiPlus (π : Profile) (i0 i1 i2 : ℕ) : Phi π ≤ PhiPlus π i0 i1 i2 := by
  have := Delta_nonneg π.f0 π.g0 π.t0 i0
  have := Delta_nonneg π.f1 π.g1 π.t1 i1
  have := Delta_nonneg π.f2 π.g2 π.t2 i2
  unfold PhiPlus; linarith

end Pw2312
end Erdos643R3
