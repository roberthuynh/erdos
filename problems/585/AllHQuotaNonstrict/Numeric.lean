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
import AllHQuotaNonstrict.Interface

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section

namespace Erdos585.AllHQuotaNonstrict

namespace Parameters
variable {h q j ξ : ℕ} (p : Parameters h q j ξ)
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
    4 * (ξ : ℤ) + 100 * (h : ℤ) ^ 2 ≤ q ∧
    5 * (h : ℤ) < ξ ∧
    3 * (j : ℤ) + 2 < ξ ∧
    6 * (h : ℤ) < q ∧
    (ξ : ℤ) + 4 * h < q ∧
    40 * (h : ℤ) ^ 2 < q := by
  have hh := p.height_int
  have hq := p.large_int
  have hj := p.j_bounds
  have hlo : (h : ℤ)^2+3*h+8 ≤ ξ := by exact_mod_cast p.lower
  have hhi : (ξ : ℤ) ≤ (h : ℤ)^2+5*h+8 := by exact_mod_cast p.upper
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
lemma offset_le_product : ξ ≤ h * q := by
  have hn := p.numeric
  have hh := p.height_int
  have hp : (ξ : ℤ) ≤ (h : ℤ) * q := by
    nlinarith [mul_nonneg (show 0 ≤ (h : ℤ) - 1 by omega) (show 0 ≤ (q : ℤ) by omega)]
  exact_mod_cast hp

open Classical in
lemma constant_cast : (constant h q ξ : ℤ) = (h : ℤ) * q - ξ := by
  unfold constant
  rw [Nat.cast_sub p.offset_le_product, Nat.cast_mul]

open Classical in
lemma scar_lower : (q : ℤ) - ξ ≤
    (h : ℤ) * q - ξ - ((q : ℤ) - 1) * j := by
  have hj := p.j_bounds
  have hq := p.q_pos
  have hm : 0 ≤ ((h : ℤ) - j - 1) * q :=
    mul_nonneg (by omega) (by omega)
  nlinarith

end Parameters
end Erdos585.AllHQuotaNonstrict
