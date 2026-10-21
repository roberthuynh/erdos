import Mathlib
import Openmath.Erdos643R3.Lemma3
import Openmath.Erdos643R3.PwC1
import Openmath.Erdos643R3.PwC2

/-!
# σ + τ ≥ 23/12 for every triple, and ex_3(n) ≤ (24/23) C(n,2) (pw2312 Theorems 1, 2 and the Corollary)

Formalizes the per-triple inequality and its summed cardinal consequences. For a finite vertex type `V` and `H : Finset (Finset V)`:

* `per_triple` (Theorem 1): `Uniform H`, `¬ Forbidden H`, `T ∈ H` ⟹ `23/12 ≤ σ(T) + τ(T)`;
* `card_le_shadow_colink` (Corollary): `(23/12)|H| ≤ |∂H| + |CL(H)|`;
* `card_le_O`: `|H| ≤ (24/23)|O(H)|`;
* `card_le_choose`: `|H| ≤ (24/23) C(|V|, 2)`; with `V = Fin n` this is `ex_3(n) ≤ (24/23) C(n,2)`.

"3-graph" is `Identity.Uniform H`, "avoiding" is `¬ Erdos643.HypergraphBasics.Forbidden H`, `σ, τ` are
`Weighting.sigmaW, Weighting.tauW`, `∂H, CL(H), O(H)` are `Identity.shadow, Identity.colink, Identity.O` — the same
definitions as the 9/8 theorem `WeightingBound.card_le_nine_eighths_choose`.

Proof map. `theorem2` (Φ ≥ 23/12 for every feasible profile): `t ≥ 12` (`Phi_of_t_ge`); the one-sided reduction
(`rel0_trichotomy`: a relation that is not big has both counts `≤ 92`, or `Φ > 23/12` by `S_one_sided`); Case I
(`caseI_rel01`, two big relations); Case II (no big relation, kernel certificate `PwC1.caseII`); Case III (one big
relation, kernel certificate `PwC2.caseIII`); other relations are reduced to `ρ_0` by the cyclic shift `rot`
(`Phi_rot`, `Feas_rot`). Theorem 1 is `Lemma3.lemma3` plus `theorem2`; the Corollary sums Theorem 1 with
`Weighting.lemma4` (`Σ σ = |∂H|`, `Σ τ = |CL(H)|`).
-/

set_option autoImplicit false

namespace Erdos643R3
namespace Pw2312Main

open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.Pw2312 Erdos643R3.PwCheck

/-! ## Theorem 2 -/

/-- For `ρ_0`: it is big, or it is not big and both its counts are `≤ 92`, or `Φ > 23/12` (one-sided reduction). -/
theorem rel0_trichotomy (π : Profile) (ht : π.t0 + π.t1 + π.t2 ≤ 11) :
    Big0 π ∨ (¬ Big0 π ∧ π.f0 ≤ 92 ∧ π.g1 ≤ 92) ∨ 23 / 12 ≤ Phi π := by
  by_cases hB : Big0 π
  · exact Or.inl hB
  by_cases hs : π.f0 ≤ 92 ∧ π.g1 ≤ 92
  · exact Or.inr (Or.inl ⟨hB, hs⟩)
  right; right
  unfold Big0 at hB
  obtain ⟨-, h2, -, -, -, -⟩ := S_le_Phi π
  obtain ⟨h1, -, -, -, -, -⟩ := S_le_Phi π
  by_cases hf : 93 ≤ π.f0
  · have := S_one_sided (p := π.f0) (q := π.g1) (y := π.t1) hf (by omega) (by omega)
    linarith
  · have := S_one_sided (p := π.g1) (q := π.f0) (y := π.t0) (by omega) (by omega) (by omega)
    linarith

/-- **Theorem 2** (pw2312 §4). `Φ ≥ 23/12` for every profile satisfying (F). -/
theorem theorem2 (π : Profile) (hF : Feas π) : 23 / 12 ≤ Phi π := by
  by_cases ht : 12 ≤ π.t0 + π.t1 + π.t2
  · exact Phi_of_t_ge π ht
  have ht' : π.t0 + π.t1 + π.t2 ≤ 11 := by omega
  have hF1 : Feas (rot π) := (Feas_rot π).mpr hF
  have hF2 : Feas (rot (rot π)) := (Feas_rot (rot π)).mpr hF1
  have e1 : Phi (rot π) = Phi π := Phi_rot π
  have e2 : Phi (rot (rot π)) = Phi π := by rw [Phi_rot, Phi_rot]
  have ht1 : (rot π).t0 + (rot π).t1 + (rot π).t2 ≤ 11 := by simp only [rot]; omega
  have ht2 : (rot (rot π)).t0 + (rot (rot π)).t1 + (rot (rot π)).t2 ≤ 11 := by simp only [rot]; omega
  have T0 := rel0_trichotomy π ht'
  have T1 := rel0_trichotomy (rot π) ht1
  have T2 := rel0_trichotomy (rot (rot π)) ht2
  rw [e1] at T1
  rw [e2] at T2
  simp only [Big0, rot] at T0 T1 T2
  rcases T0 with B0 | ⟨N0, S0⟩ | D0 <;> rcases T1 with B1 | ⟨N1, S1⟩ | D1 <;>
    rcases T2 with B2 | ⟨N2, S2⟩ | D2
  all_goals first
    | assumption
    -- Case I: two big relations (0 and 1, 2 and 0, 1 and 2)
    | exact caseI_rel01 π B0 B1
    | (rw [← e2]; exact caseI_rel01 _ B2 B0)
    | (rw [← e1]; exact caseI_rel01 _ B1 B2)
    -- Case III: exactly one big relation (ρ_0, ρ_1, ρ_2), rotated to ρ_0
    | exact PwC2.caseIII π hF ht' B0.1 B0.2 ⟨S2.2, S1.1, S2.1, S1.2⟩
    | (rw [← e1]; exact PwC2.caseIII _ hF1 ht1 B1.1 B1.2 ⟨S0.2, S2.1, S0.1, S2.2⟩)
    | (rw [← e2]; exact PwC2.caseIII _ hF2 ht2 B2.1 B2.2 ⟨S1.2, S0.1, S1.1, S0.2⟩)
    -- Case II: no big relation
    | (refine PwC1.caseII π hF ht' ⟨S0.1, S2.2, S1.1, S0.2, S2.1, S1.2⟩ ?_
       unfold Big0 Big1 Big2
       omega)

/-! ## Theorem 1 and the Corollary -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Theorem 1** (pw2312). For every finite avoiding 3-graph `H` and every `T ∈ H`: `σ(T) + τ(T) ≥ 23/12`. -/
theorem per_triple {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {T : Finset V} (hT : T ∈ H) :
    23 / 12 ≤ sigmaW H T + tauW H T := by
  obtain ⟨a, b, c, -, -, -, rfl⟩ := card_eq_three.mp (hH T hT)
  obtain ⟨h1, h2⟩ := Lemma3.lemma3 hT hH hav
  exact (theorem2 _ h2).trans h1

/-- **Corollary** (pw2312 §5). `(23/12)|H| ≤ |∂H| + |CL(H)|` for every finite avoiding 3-graph `H`. -/
theorem card_le_shadow_colink {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    23 / 12 * (H.card : ℚ) ≤ ((shadow H).card : ℚ) + ((colink H).card : ℚ) := by
  have h := Finset.sum_le_sum (fun T hT => per_triple hH hav hT)
  rw [sum_const, nsmul_eq_mul, sum_add_distrib, sum_sigmaW, sum_tauW H hH] at h
  linarith

/-- **Corollary.** `|H| ≤ (24/23)|O(H)|` for every finite avoiding 3-graph `H`. -/
theorem card_le_O {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    (H.card : ℚ) ≤ 24 / 23 * ((O H).card : ℚ) := by
  have h := card_le_shadow_colink hH hav
  have h1 : (shadow H).card ≤ (O H).card := card_le_card subset_union_left
  have h2 : (colink H).card ≤ (O H).card := card_le_card subset_union_right
  have h1' : ((shadow H).card : ℚ) ≤ ((O H).card : ℚ) := by exact_mod_cast h1
  have h2' : ((colink H).card : ℚ) ≤ ((O H).card : ℚ) := by exact_mod_cast h2
  linarith

/-- **Corollary.** Every avoiding 3-graph on a finite vertex type `V` has `|H| ≤ (24/23) C(|V|, 2)`; with
`V = Fin n` this is `ex_3(n) ≤ (24/23) C(n, 2)`. -/
theorem card_le_choose {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    (H.card : ℚ) ≤ 24 / 23 * (((Fintype.card V).choose 2 : ℕ) : ℚ) := by
  have h := card_le_shadow_colink hH hav
  have h1 : (shadow H).card ≤ (Fintype.card V).choose 2 := by
    rw [← WeightingBound.card_pairs]; exact card_le_card (shadow_subset_pairs H)
  have h2 : (colink H).card ≤ (Fintype.card V).choose 2 := by
    rw [← WeightingBound.card_pairs]; exact card_le_card (filter_subset _ _)
  have h1' : ((shadow H).card : ℚ) ≤ (((Fintype.card V).choose 2 : ℕ) : ℚ) := by exact_mod_cast h1
  have h2' : ((colink H).card : ℚ) ≤ (((Fintype.card V).choose 2 : ℕ) : ℚ) := by exact_mod_cast h2
  linarith

end Pw2312Main
end Erdos643R3
