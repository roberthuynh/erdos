import Mathlib
import Openmath.Erdos643R3.WeightingBound
import Openmath.Erdos643R3.Pw2312

/-!
# Bridge to the formal-conjectures statement of Erdős Problem 643

Upstream source: github.com/google-deepmind/formal-conjectures, branch `main` at commit
`95b199bfbc08f7b1183196bab59ed3b08f27c2c9` (2026-10-19T13:56:39Z), fetched 19 October 2026:
* `FormalConjectures/ErdosProblems/643.lean`, SHA-256 `d9e18a2649b258fd48b6e26195a827c69e0e7a23ab7b8ec223b9dfe979d8ee80`,
  states the problem through `Hypergraph.extremalNumber n t (fun H ↦ ¬ H.HasRepeatedDisjointUnion) + 1`
  (`erdos_643.parts.i`, lines 49–54; `erdos_643.parts.ii`, lines 60–65, the asymptotic `~ C(n, t−1)` for `t ≥ 3`);
* `FormalConjecturesForMathlib/Combinatorics/Hypergraph/Finite.lean`, SHA-256
  `0823fba654c8fd849c821338e6624aefac6935a92836523dde9eb6524874949a`, defines `Finset.IsUniform` (line 52),
  `Finset.HasRepeatedDisjointUnion` (lines 144–148) and `Hypergraph.extremalNumber` (lines 181–185).

The upstream definitions are reconstructed below, character for character, except that the
upstream `module` / `public` / `@[expose]` markers are dropped and the definitions sit in the namespace
`Erdos643R3.FCBridge.FC` (instead of the root namespaces `Finset` and `Hypergraph`) to avoid any clash.
Verbatim upstream text, for comparison:

    namespace Finset
    variable {V : Type*} [DecidableEq V]
    /-- Every edge has exactly `r` vertices. -/
    def IsUniform (H : Finset (Finset V)) (r : ℕ) : Prop := ∀ e ∈ H, e.card = r
    /-- Two distinct disjoint pairs of edges with the same union. -/
    def HasRepeatedDisjointUnion (H : Finset (Finset V)) : Prop :=
      ∃ A ∈ H, ∃ B ∈ H, ∃ C ∈ H, ∃ D ∈ H,
        Disjoint A B ∧ Disjoint C D ∧ A ∪ B = C ∪ D ∧
        A ≠ B ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D
    end Finset
    namespace Hypergraph
    open scoped Classical in
    /-- Maximum number of edges among `r`-uniform families satisfying `P` on `n` labeled vertices.
    The value is zero if no family is admissible. -/
    noncomputable def extremalNumber (n r : ℕ) (P : Finset (Finset (Fin n)) → Prop) : ℕ :=
      (((Finset.univ : Finset (Fin n)).powersetCard r).powerset.filter P).sup Finset.card
    end Hypergraph

Main declarations (namespace `Erdos643R3.FCBridge`):
* `hasRepeatedDisjointUnion_iff_forbidden`: `FC.HasRepeatedDisjointUnion H ↔ Erdos643.HypergraphBasics.Forbidden H`;
* `isUniform_three_iff`: `FC.IsUniform H 3 ↔ Identity.Uniform H`;
* `ex3_le_nine_eighths`, `ex3_le_nine_eighths_rat`: `8·ex_3(n) ≤ 9·C(n,2)` (from `card_le_nine_eighths_choose`);
* `ex3_le_24_23`, `ex3_le_24_23_rat`, `f_le_24_23_real`: `23·ex_3(n) ≤ 24·C(n,2)`, and in the upstream shape
  `((extremalNumber n 3 (¬ HasRepeatedDisjointUnion) + 1 : ℕ) : ℝ) ≤ (24/23)·C(n,2) + 1` (from
  `Pw2312Main.card_le_choose`); here `ex_3(n) = FC.extremalNumber n 3 (fun H ↦ ¬ FC.HasRepeatedDisjointUnion H)`.
-/

set_option autoImplicit false

namespace Erdos643R3
namespace FCBridge

namespace FC

variable {V : Type*} [DecidableEq V]

/-- Every edge has exactly `r` vertices. (Upstream `Finset.IsUniform`.) -/
def IsUniform (H : Finset (Finset V)) (r : ℕ) : Prop := ∀ e ∈ H, e.card = r

/-- Two distinct disjoint pairs of edges with the same union. (Upstream `Finset.HasRepeatedDisjointUnion`.) -/
def HasRepeatedDisjointUnion (H : Finset (Finset V)) : Prop :=
  ∃ A ∈ H, ∃ B ∈ H, ∃ C ∈ H, ∃ D ∈ H,
    Disjoint A B ∧ Disjoint C D ∧ A ∪ B = C ∪ D ∧
    A ≠ B ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D

open scoped Classical in
/-- Maximum number of edges among `r`-uniform families satisfying `P` on `n` labeled vertices.
The value is zero if no family is admissible. (Upstream `Hypergraph.extremalNumber`.) -/
noncomputable def extremalNumber (n r : ℕ) (P : Finset (Finset (Fin n)) → Prop) : ℕ :=
  (((Finset.univ : Finset (Fin n)).powersetCard r).powerset.filter P).sup Finset.card

end FC

open Finset

/-! ## The two predicates -/

/-- The upstream forbidden configuration is exactly this development's `Forbidden` (the six inequalities of
`FourDistinct` in another order). -/
theorem hasRepeatedDisjointUnion_iff_forbidden {V : Type*} [DecidableEq V] (H : Finset (Finset V)) :
    FC.HasRepeatedDisjointUnion H ↔ Erdos643.HypergraphBasics.Forbidden H := by
  constructor
  · rintro ⟨A, hA, B, hB, C, hC, D, hD, hAB, hCD, hu, h1, h2, h3, h4, h5, h6⟩
    exact ⟨A, hA, B, hB, C, hC, D, hD, ⟨h1, h3, h4, h5, h6, h2⟩, hAB, hCD, hu⟩
  · rintro ⟨A, hA, B, hB, C, hC, D, hD, ⟨h1, h3, h4, h5, h6, h2⟩, hAB, hCD, hu⟩
    exact ⟨A, hA, B, hB, C, hC, D, hD, hAB, hCD, hu, h1, h2, h3, h4, h5, h6⟩

/-- `IsUniform H 3` is this development's `Uniform H` (both are `∀ e ∈ H, e.card = 3`). -/
theorem isUniform_three_iff {V : Type*} [DecidableEq V] (H : Finset (Finset V)) :
    FC.IsUniform H 3 ↔ Erdos643R3.Identity.Uniform H := Iff.rfl

/-- An admissible family of `extremalNumber n 3 (¬ HasRepeatedDisjointUnion)` is a uniform avoiding family. -/
theorem admissible {n : ℕ} {H : Finset (Finset (Fin n))}
    (hH : H ⊆ (Finset.univ : Finset (Fin n)).powersetCard 3) (hav : ¬ FC.HasRepeatedDisjointUnion H) :
    Erdos643R3.Identity.Uniform H ∧ ¬ Erdos643.HypergraphBasics.Forbidden H :=
  ⟨fun _ he => (mem_powersetCard.mp (hH he)).2,
    fun h => hav ((hasRepeatedDisjointUnion_iff_forbidden H).mpr h)⟩

/-- `extremalNumber` is bounded by any bound valid for every admissible family. -/
theorem extremalNumber_le {n : ℕ} (f : ℕ → Prop) (hf0 : f 0) (hmax : ∀ a b, f a → f b → f (max a b))
    (hH : ∀ H : Finset (Finset (Fin n)), H ⊆ (Finset.univ : Finset (Fin n)).powersetCard 3 →
      ¬ FC.HasRepeatedDisjointUnion H → f H.card) :
    f (FC.extremalNumber n 3 (fun H => ¬ FC.HasRepeatedDisjointUnion H)) := by
  unfold FC.extremalNumber
  refine Finset.sup_induction (p := f) hf0 (fun a ha b hb => hmax a b ha hb) ?_
  intro H hmem
  simp only [Finset.mem_filter, Finset.mem_powerset] at hmem
  exact hH H hmem.1 hmem.2

/-! ## ex_3(n) ≤ (9/8) C(n,2) -/

theorem ex3_le_nine_eighths (n : ℕ) :
    8 * FC.extremalNumber n 3 (fun H => ¬ FC.HasRepeatedDisjointUnion H) ≤ 9 * n.choose 2 := by
  refine extremalNumber_le (n := n) (fun m => 8 * m ≤ 9 * n.choose 2) (by omega)
    (fun a b ha hb => by show 8 * max a b ≤ 9 * n.choose 2; omega) ?_
  intro H hH hav
  obtain ⟨hu, hf⟩ := admissible hH hav
  have h := Erdos643R3.WeightingBound.card_le_nine_eighths_choose hu hf
  rw [Fintype.card_fin] at h
  have h' : (8 : ℚ) * H.card ≤ 9 * ((n.choose 2 : ℕ) : ℚ) := by linarith
  exact_mod_cast h'

theorem ex3_le_nine_eighths_rat (n : ℕ) :
    ((FC.extremalNumber n 3 (fun H => ¬ FC.HasRepeatedDisjointUnion H) : ℕ) : ℚ) ≤
      9 / 8 * ((n.choose 2 : ℕ) : ℚ) := by
  have h : ((8 * FC.extremalNumber n 3 (fun H => ¬ FC.HasRepeatedDisjointUnion H) : ℕ) : ℚ) ≤
      ((9 * n.choose 2 : ℕ) : ℚ) := by exact_mod_cast ex3_le_nine_eighths n
  push_cast at h
  linarith

/-! ## ex_3(n) ≤ (24/23) C(n,2) -/

theorem ex3_le_24_23 (n : ℕ) :
    23 * FC.extremalNumber n 3 (fun H => ¬ FC.HasRepeatedDisjointUnion H) ≤ 24 * n.choose 2 := by
  refine extremalNumber_le (n := n) (fun m => 23 * m ≤ 24 * n.choose 2) (by omega)
    (fun a b ha hb => by show 23 * max a b ≤ 24 * n.choose 2; omega) ?_
  intro H hH hav
  obtain ⟨hu, hf⟩ := admissible hH hav
  have h := Erdos643R3.Pw2312Main.card_le_choose hu hf
  rw [Fintype.card_fin] at h
  have h' : (23 : ℚ) * H.card ≤ 24 * ((n.choose 2 : ℕ) : ℚ) := by linarith
  exact_mod_cast h'

theorem ex3_le_24_23_rat (n : ℕ) :
    ((FC.extremalNumber n 3 (fun H => ¬ FC.HasRepeatedDisjointUnion H) : ℕ) : ℚ) ≤
      24 / 23 * ((n.choose 2 : ℕ) : ℚ) := by
  have h : ((23 * FC.extremalNumber n 3 (fun H => ¬ FC.HasRepeatedDisjointUnion H) : ℕ) : ℚ) ≤
      ((24 * n.choose 2 : ℕ) : ℚ) := by exact_mod_cast ex3_le_24_23 n
  push_cast at h
  linarith

/-- In the shape of upstream `erdos_643.parts.ii` at `t = 3`: the problem's `f(n;3)`, i.e.
`extremalNumber n 3 (¬ HasRepeatedDisjointUnion) + 1` cast to `ℝ`, is at most `(24/23)·C(n,2) + 1` for every `n`.
(An upper bound only; the upstream statement is the asymptotic equivalence with `C(n,2)`.) -/
theorem f_le_24_23_real (n : ℕ) :
    ((FC.extremalNumber n 3 (fun H => ¬ FC.HasRepeatedDisjointUnion H) + 1 : ℕ) : ℝ) ≤
      24 / 23 * (n.choose (3 - 1) : ℝ) + 1 := by
  have h : ((23 * FC.extremalNumber n 3 (fun H => ¬ FC.HasRepeatedDisjointUnion H) : ℕ) : ℝ) ≤
      ((24 * n.choose 2 : ℕ) : ℝ) := by exact_mod_cast ex3_le_24_23 n
  push_cast at h ⊢
  linarith

end FCBridge
end Erdos643R3
