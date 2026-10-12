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
import AllHQuotaNonstrict.Original
import AllHQuotaNonstrict.UniformEscape

/-! The two arbitrary-ban conclusions on literal original hosts. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section
namespace Erdos585.AllHQuotaNonstrict
open QB4 B5 L34 H3Unequal
universe u

open Classical in
/-- Two-unit escape under ANY residual ban of at most 4h² original columns. -/
theorem original_two_gain (h q j ξ : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (host : Host h q j ξ G A B)
    (K ban : Finset V) (hK : K⊆B) (hl : q-1≤#K)
    (hp : 2≤thetaJ q j G A B K)
    (strict : ∀ T⊆B, K⊆T → K≠T → thetaJ q j G A B T≤thetaJ q j G A B K-1)
    (hban : ban⊆B\K) (hbanCard : #ban≤4*h^2) :
    ∃ z∈B\K, z∉ban ∧ ∀ P⊆B\K, z∈P → 2≤extensionCost q j G A B K P := by
  classical
  exact petal_escape h q j ξ A B K ban host.to_data hK hl hp strict hban hbanCard

open Classical in
/-- The SAME fixed heavy threshold and arbitrary ban survive every owner contraction. -/
theorem original_high_escape (h q j ξ s : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (host : Host h q j ξ G A B)
    (K ban : Finset V) (hK : K⊆B) (hl : q-1≤#K)
    (hp : thetaJ q j G A B K=2*(j:ℤ)+s-1)
    (strict : ∀ T⊆B, K⊆T → K≠T → thetaJ q j G A B T≤thetaJ q j G A B K-1)
    (hban : ban⊆B\K) (hbanCard : #ban≤4*h^2) :
    ∃ z∈B\K, z∉ban ∧ (dg G (weakCore q G A B K) z:ℤ)<(q:ℤ)-((h:ℤ)-j) ∧
      ∀ P⊆B\K, z∈P → (s:ℤ)+1≤extensionCost q j G A B K P := by
  classical
  exact UniformEscape.escape host.to_data s K ban hK hl hp strict hban hbanCard

end Erdos585.AllHQuotaNonstrict
