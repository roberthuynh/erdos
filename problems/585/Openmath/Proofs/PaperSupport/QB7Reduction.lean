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
import Openmath.Proofs.QB5.Defs

/- 



-/

open Finset

namespace Erdos585.QB7Reduction

open QB4 QB5

/-- Exact deficiency arithmetic of the balanced Hall-cut reduction. -/
theorem hall_pattern_arithmetic {b k da db dc r : ℤ}
    (hb : b = 6 ∨ b = 7) (hk : 1 ≤ k)
    (hda : 0 ≤ da) (hdb : 0 ≤ db) (hdc : 0 ≤ dc) (hr : 0 ≤ r)
    (hdef : da + db = b)
    (hspX : b + 1 ≤ 3 * k + dc + r)
    (hspY : b + 1 ≤ 3 * k + db + r)
    (hv : 2 * k + dc + r < da) :
    (b = 6 ∧ k = 2 ∧ da = 6 ∧ db = 0 ∧ dc = 0 ∧ r = 1) ∨
      (b = 7 ∧ k = 2 ∧ da = 7 ∧ db = 0 ∧ dc = 0 ∧ r = 2) ∨
      (b = 7 ∧ k = 3 ∧ da = 7 ∧ db = 0 ∧ dc = 0 ∧ r = 0) := by
  rcases hb with rfl | rfl <;> omega

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Proper-pair sparsity at the literal QB(b), n>=4 threshold. -/
def SparseBound (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) (b : ℤ) : Prop :=
  ∀ X ⊆ U, ∀ Y ⊆ W, 4 ≤ #X + #Y → #X + #Y < #U + #W → 2 * b + 2 ≤ gv G X Y

/-- Sparsity of a minimal counterexample, with the exact smaller-pair induction premise. -/
theorem minimal_sparsity {U W : Finset V} {b : ℤ}
    (ih : ∀ X ⊆ U, ∀ Y ⊆ W, 4 ≤ #X + #Y → #X + #Y < #U + #W →
      gv G X Y ≤ 2 * b → Quartic G X Y)
    (hq : ¬ Quartic G U W) : SparseBound G U W b := by
  intro X hX Y hY hn hlt
  by_contra h
  have hlow : gv G X Y ≤ 2 * b := by
    obtain ⟨r, hr⟩ := even_gv (G := G) X Y
    omega
  exact hq ((ih X hX Y hY hn hlt hlow).mono hX hY)

/-- The exact one-vertex deletion identity raises the minimum degree to four. -/
theorem minimum_four_left {U W : Finset V} {b : ℤ}
    (hsp : SparseBound G U W b) (hg : gv G U W ≤ 2 * b)
    (hn : 5 ≤ #U + #W) {u : V} (hu : u ∈ U) : 4 ≤ dg G W u := by
  have h1 := gv_erase_left (G := G) hu W
  have h2 := card_erase_add_one hu
  have h3 := hsp (U.erase u) (erase_subset u U) W Subset.rfl (by omega) (by omega)
  omega

omit [DecidableEq V] in
/-- The complete shore-deficiency list at b=6 or7, in the smaller-shore orientation. -/
theorem shore_signature {U W : Finset V} {j : ℕ} {b : ℤ}
    (hb : b = 6 ∨ b = 7) (hcard : #W = #U + j)
    (hdU : ∀ u ∈ U, dg G W u ≤ 6) (hg : gv G U W = 2 * b) :
    j ≤ 2 ∧ df G W U = b - 3 * (j : ℤ) := by
  have h1 := gv_eq_right (G := G) U W
  have h2 := df_nonneg hdU
  rcases hb with rfl | rfl <;> omega

/-- Actual graph cut identities force the three exact signatures. The two `gv` premises
are paid by proper-set sparsity in the written minimal-counterexample reduction. -/
theorem balanced_hall_patterns {P Q A C : Finset V} {b : ℤ}
    (hb : b = 6 ∨ b = 7) (hcard : #P = #Q)
    (hdP : ∀ p ∈ P, dg G Q p ≤ 6) (hdQ : ∀ q ∈ Q, dg G P q ≤ 6)
    (hdefP : df G Q P = b) (hdefQ : df G P Q = b)
    (hA : A ⊆ P) (hC : C ⊆ Q)
    (hspX : 2 * b + 2 ≤ gv G A C)
    (hspY : 2 * b + 2 ≤ gv G (P \ A) (Q \ C))
    (hviol : ec G A (Q \ C) + 4 * #C < 4 * #A) :
    (b = 6 ∧ #A = #C + 2 ∧ df G Q A = 6 ∧ df G Q (P \ A) = 0 ∧
      df G P C = 0 ∧ ec G (P \ A) C = 1 ∧ ec G A (Q \ C) = 7 ∧
      gv G A C = 14 ∧ gv G (P \ A) (Q \ C) = 14) ∨
    (b = 7 ∧ #A = #C + 2 ∧ df G Q A = 7 ∧ df G Q (P \ A) = 0 ∧
      df G P C = 0 ∧ ec G (P \ A) C = 2 ∧ ec G A (Q \ C) = 7 ∧
      gv G A C = 16 ∧ gv G (P \ A) (Q \ C) = 16) ∨
    (b = 7 ∧ #A = #C + 3 ∧ df G Q A = 7 ∧ df G Q (P \ A) = 0 ∧
      df G P C = 0 ∧ ec G (P \ A) C = 0 ∧ ec G A (Q \ C) = 11 ∧
      gv G A C = 18 ∧ gv G (P \ A) (Q \ C) = 18) := by
  have hda : 0 ≤ df G Q A := df_nonneg fun p hp => hdP p (hA hp)
  have hdb : 0 ≤ df G Q (P \ A) := df_nonneg fun p hp => hdP p (sdiff_subset hp)
  have hdc : 0 ≤ df G P C := df_nonneg fun q hq => hdQ q (hC hq)
  have hr : (0 : ℤ) ≤ ec G (P \ A) C := Int.natCast_nonneg _
  have hsum : df G Q A + df G Q (P \ A) = b := by
    have := df_sdiff_add (G := G) (S := Q) hA
    omega
  have hslack := ec_sdiff_eq (G := G) hA hC
  have hgX : gv G A C =
      6 * ((#A : ℤ) - #C) + 2 * (df G P C + ec G (P \ A) C) := by
    have e1 := ec_sdiff_add_right (G := G) hA C
    have e2 := ec_comm (G := G) C (P \ A)
    have e3 := ec_comm (G := G) A C
    have e4 := df_eq (G := G) P C
    unfold gv
    omega
  have hcB := card_sdiff_add_card_eq_card hA
  have hcD := card_sdiff_add_card_eq_card hC
  have hgY : gv G (P \ A) (Q \ C) =
      6 * ((#A : ℤ) - #C) + 2 * (df G Q (P \ A) + ec G (P \ A) C) := by
    have e1 := ec_sdiff_add_right (G := G) hC (P \ A)
    have e2 := df_eq (G := G) Q (P \ A)
    unfold gv
    omega
  have hk : 1 ≤ (#A : ℤ) - #C := by omega
  have hv : 2 * ((#A : ℤ) - #C) + df G P C + ec G (P \ A) C < df G Q A := by
    omega
  have hsX : b + 1 ≤ 3 * ((#A : ℤ) - #C) + df G P C + ec G (P \ A) C := by
    omega
  have hsY : b + 1 ≤ 3 * ((#A : ℤ) - #C) + df G Q (P \ A) + ec G (P \ A) C := by
    omega
  obtain h | h | h := hall_pattern_arithmetic hb hk hda hdb hdc hr hsum hsX hsY hv
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

end Erdos585.QB7Reduction
