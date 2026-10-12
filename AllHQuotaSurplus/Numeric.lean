/-
Copyright 2026 Robert Huynh.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import AllHQuotaSurplus.Interface

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section

namespace Erdos585.AllHQuotaSurplus

open Classical in
lemma offset_cast (h : ℕ) : (offset h : ℤ) = (h : ℤ) ^ 2 + 5 * h + 8 := by
  simp [offset]

namespace Parameters
variable {h q j : ℕ} (p : Parameters h q j)
include p

open Classical in
lemma height_int : (3 : ℤ) ≤ h := by exact_mod_cast p.height

open Classical in
lemma large_int : 1024 * ((h : ℤ) + 1) ^ 2 ≤ q := by exact_mod_cast p.large

open Classical in
lemma j_pos : 0 < j := by have hj := p.positive; omega

open Classical in
lemma j_bounds : (1 : ℤ) ≤ j ∧ (j : ℤ) ≤ (h : ℤ) - 1 := by
  have hj := p.positive
  have hu := p.surplus
  have hh := p.height
  omega

open Classical in
/-- Consequences of the literal quadratic cutoff; no stronger numerical guard is supplied. -/
lemma numeric :
    4 * (offset h : ℤ) + 100 * (h : ℤ) ^ 2 ≤ q ∧
    5 * (h : ℤ) < offset h ∧
    3 * (j : ℤ) + 2 < offset h ∧
    6 * (h : ℤ) < q ∧
    (offset h : ℤ) + 4 * h < q ∧
    40 * (h : ℤ) ^ 2 < q := by
  have hh := p.height_int
  have hq := p.large_int
  have hj := p.j_bounds
  rw [offset_cast]
  constructor
  · nlinarith [sq_nonneg (h : ℤ)]
  constructor
  · nlinarith [sq_nonneg (h : ℤ)]
  constructor
  · nlinarith [sq_nonneg (h : ℤ)]
  constructor
  · nlinarith [sq_nonneg (h : ℤ)]
  constructor
  · nlinarith [sq_nonneg (h : ℤ)]
  · nlinarith [sq_nonneg (h : ℤ)]

open Classical in
lemma q_pos : 0 < q := by have hn := p.numeric; have hh := p.height; omega

open Classical in
lemma q_ge_height : h + 3 ≤ q := by have hn := p.numeric; have hh := p.height; omega

open Classical in
lemma offset_le_product : offset h ≤ h * q := by
  have hn := p.numeric
  have hh := p.height_int
  have hp : (offset h : ℤ) ≤ (h : ℤ) * q := by
    nlinarith [mul_nonneg (show 0 ≤ (h : ℤ) - 1 by omega) (show 0 ≤ (q : ℤ) by omega)]
  exact_mod_cast hp

open Classical in
lemma constant_cast : (constant h q : ℤ) = (h : ℤ) * q - offset h := by
  unfold constant
  rw [Nat.cast_sub p.offset_le_product, Nat.cast_mul]

open Classical in
lemma scar_lower : (q : ℤ) - offset h ≤
    (h : ℤ) * q - offset h - ((q : ℤ) - 1) * j := by
  have hj := p.j_bounds
  have hq := p.q_pos
  have hm : 0 ≤ ((h : ℤ) - j - 1) * q :=
    mul_nonneg (by omega) (by omega)
  nlinarith

end Parameters
end Erdos585.AllHQuotaSurplus
