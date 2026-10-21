import Mathlib
import Openmath.Erdos643R3.Identity



set_option autoImplicit false

namespace Erdos643R3
namespace RedistArith

open Erdos643R3.Identity

/-! ## Lemma P -/

/-- Among three Booleans, the number of unequal pairs is 0 or 2. -/
theorem parity_bool (p q r : Bool) :
    ((if p ≠ q then 1 else 0) + (if q ≠ r then 1 else 0) + (if p ≠ r then 1 else 0) : ℕ) = 0 ∨
      ((if p ≠ q then 1 else 0) + (if q ≠ r then 1 else 0) + (if p ≠ r then 1 else 0) : ℕ) = 2 := by
  cases p <;> cases q <;> cases r <;> simp

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `xs` is light: `k_xs = 2`. -/
def Light (H : Finset (Finset V)) (x s : V) : Prop := codeg H {x, s} = 2

/-- The triple `x + st` is exactly-one-light: exactly one of `xs`, `xt` is light. -/
def ExactlyOneLight (H : Finset (Finset V)) (x s t : V) : Prop := ¬ (Light H x s ↔ Light H x t)

omit [Fintype V] in
open Classical in
/-- **Lemma P** (redist §3). For an apex `x` and base vertices `u, v, w`, the number of the triples `x+uv, x+vw,
x+uw` that are exactly-one-light is 0 or 2. -/
theorem lemma_P (H : Finset (Finset V)) (x u v w : V) :
    ((if ExactlyOneLight H x u v then 1 else 0) + (if ExactlyOneLight H x v w then 1 else 0) +
        (if ExactlyOneLight H x u w then 1 else 0) : ℕ) = 0 ∨
      ((if ExactlyOneLight H x u v then 1 else 0) + (if ExactlyOneLight H x v w then 1 else 0) +
        (if ExactlyOneLight H x u w then 1 else 0) : ℕ) = 2 := by
  have h := parity_bool (decide (Light H x u)) (decide (Light H x v)) (decide (Light H x w))
  have e : ∀ s t : V, ExactlyOneLight H x s t ↔ decide (Light H x s) ≠ decide (Light H x t) := by
    intro s t
    unfold ExactlyOneLight
    by_cases hs : Light H x s <;> by_cases ht : Light H x t <;> simp [hs, ht]
  simp only [e]
  exact h

/-! ## Lemma Q(iii): `F(m₀, m₁) ≥ 0` -/

/-- `F(m₀,m₁) = 1/(2+m₀+m₁) + 1/(2(2+m₁)) + m₀/2 + m₁/4 − 3/4` (`= c(T°) − 1/6` in Lemma Q(iii)). -/
def F (m0 m1 : ℕ) : ℚ :=
  1 / (2 + (m0 : ℚ) + m1) + 1 / (2 * (2 + (m1 : ℚ))) + (m0 : ℚ) / 2 + (m1 : ℚ) / 4 - 3 / 4

/-- **Lemma Q(iii), arithmetic part.** `F(m₀, m₁) ≥ 0` for all naturals `m₀, m₁`. -/
theorem F_nonneg (m0 m1 : ℕ) : 0 ≤ F m0 m1 := by
  unfold F
  have h0 : (0 : ℚ) ≤ m0 := Nat.cast_nonneg m0
  have h1 : (0 : ℚ) ≤ m1 := Nat.cast_nonneg m1
  have p1 : (0 : ℚ) < 1 / (2 + (m0 : ℚ) + m1) := by positivity
  have p2 : (0 : ℚ) < 1 / (2 * (2 + (m1 : ℚ))) := by positivity
  rcases Nat.lt_or_ge m0 2 with a | a <;> rcases Nat.lt_or_ge m1 3 with b | b
  · -- the finite corner m₀ ≤ 1, m₁ ≤ 2
    interval_cases m0 <;> interval_cases m1 <;> norm_num
  · have : (3 : ℚ) ≤ m1 := by exact_mod_cast b
    linarith
  · have : (2 : ℚ) ≤ m0 := by exact_mod_cast a
    linarith
  · have : (3 : ℚ) ≤ m1 := by exact_mod_cast b
    linarith

/-- `F(m₀, m₁) = 0` only at `(0,0)` and `(0,1)` (the equality cases of Lemma Q(iii)). -/
theorem F_eq_zero {m0 m1 : ℕ} (h : F m0 m1 = 0) : m0 = 0 ∧ (m1 = 0 ∨ m1 = 1) := by
  unfold F at h
  have h0 : (0 : ℚ) ≤ m0 := Nat.cast_nonneg m0
  have h1 : (0 : ℚ) ≤ m1 := Nat.cast_nonneg m1
  have p1 : (0 : ℚ) < 1 / (2 + (m0 : ℚ) + m1) := by positivity
  have p2 : (0 : ℚ) < 1 / (2 * (2 + (m1 : ℚ))) := by positivity
  rcases Nat.lt_or_ge m0 2 with a | a <;> rcases Nat.lt_or_ge m1 3 with b | b
  · interval_cases m0 <;> interval_cases m1 <;> (try norm_num at h) <;> norm_num
  · exfalso
    have : (3 : ℚ) ≤ m1 := by exact_mod_cast b
    linarith
  · exfalso
    have : (2 : ℚ) ≤ m0 := by exact_mod_cast a
    linarith
  · exfalso
    have : (3 : ℚ) ≤ m1 := by exact_mod_cast b
    linarith

end RedistArith
end Erdos643R3
