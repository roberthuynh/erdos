import Openmath.IncidenceRepair.GeometryCounts
import Openmath.IncidenceRepair.DesignVariance
import Openmath.IncidenceRepair.SourceNumerics

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

lemma sum_indicator_eq_natCard {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (∑ x, if P x then (1 : ℝ) else 0) = Nat.card {x // P x} := by
  classical
  rw [← @Fintype.card_eq_nat_card {x // P x} (Fintype.ofFinite _)]
  simp [Fintype.card_subtype, Finset.sum_boole]

variable {K : Type*} [Field K] [Finite K] {n : ℕ}
local instance : DecidableEq (Point K n) := Classical.decEq _

lemma projective_degree [Fintype (Point K n)] (p : Point K n) :
    ∑ H : Hyperplane K n, incidence Incident p H =
      (((Nat.card K ^ n - 1) / (Nat.card K - 1) : ℕ) : ℝ) := by
  classical
  unfold incidence
  rw [sum_indicator_eq_natCard, incident_hyperplanes_card]

lemma projective_dual_degree [Fintype (Point K n)] (H : Hyperplane K n) :
    ∑ p : Point K n, incidence Incident p H =
      (((Nat.card K ^ n - 1) / (Nat.card K - 1) : ℕ) : ℝ) := by
  classical
  unfold incidence
  rw [sum_indicator_eq_natCard, incident_points_card]

lemma projective_pair_count [Fintype (Point K n)] (p q : Point K n) :
    ∑ H : Hyperplane K n, incidence Incident p H * incidence Incident q H =
      if p = q then (((Nat.card K ^ n - 1) / (Nat.card K - 1) : ℕ) : ℝ)
      else (((Nat.card K ^ (n - 1) - 1) / (Nat.card K - 1) : ℕ) : ℝ) := by
  classical
  have hprod : ∀ H : Hyperplane K n,
      incidence Incident p H * incidence Incident q H =
        if Incident p H ∧ Incident q H then (1 : ℝ) else 0 := by
    intro H
    by_cases hp : Incident p H <;> by_cases hq : Incident q H <;>
      simp [incidence, hp, hq]
  simp_rw [hprod]
  rw [sum_indicator_eq_natCard (fun H : Hyperplane K n => Incident p H ∧ Incident q H)]
  by_cases hpq : p = q
  · subst q
    simp only [and_self, if_true]
    rw [incident_hyperplanes_card]
  · rw [if_neg hpq, common_incident_hyperplanes_card p q hpq]

lemma projective_pair_design [Fintype (Point K n)] (a d lam : ℝ)
    (hd : d = (((Nat.card K ^ n - 1) / (Nat.card K - 1) : ℕ) : ℝ))
    (hlam : lam = (((Nat.card K ^ (n - 1) - 1) / (Nat.card K - 1) : ℕ) : ℝ))
    (hgap : d = a + lam) :
    ∀ p q : Point K n, ∑ H : Hyperplane K n,
      incidence Incident p H * incidence Incident q H =
        (if p = q then a else 0) + lam := by
  intro p q
  rw [projective_pair_count, ← hd, ← hlam]
  split_ifs <;> simp_all

lemma projective_pair_formula [Fintype (Point K n)] (hn : 1 ≤ n) :
    ∀ p q : Point K n, ∑ H : Hyperplane K n,
      incidence Incident p H * incidence Incident q H =
        (if p = q then ((Nat.card K ^ (n - 1) : ℕ) : ℝ) else 0) +
        (((Nat.card K ^ (n - 1) - 1) / (Nat.card K - 1) : ℕ) : ℝ) := by
  apply projective_pair_design _ _ _ rfl rfl
  exact_mod_cast source_degree_split (Nat.card K) n (Finite.one_lt_card (α := K)) hn

end Erdos85.IncidenceRepair
