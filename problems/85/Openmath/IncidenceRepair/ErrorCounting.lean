import Openmath.IncidenceRepair.DesignVariance

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

variable {P H P' H' : Type*} [Fintype P] [Fintype H]
  [DecidableEq P] [DecidableEq H]

/-- Original flags broken by the supplied pair of maps. -/
def brokenFlagSum (I : P → H → Prop) (J : P' → H' → Prop)
    (phi : P → P') (psi : H → H') : ℝ :=
  ∑ p, ∑ h, incidence (fun p h => I p h ∧ ¬ J (phi p) (psi h)) p h

/-- The real-valued sum counts each broken original source flag once. -/
theorem brokenFlagSum_eq_card (I : P → H → Prop) (J : P' → H' → Prop)
    (phi : P → P') (psi : H → H') :
    brokenFlagSum I J phi psi =
      (Nat.card { ph : P × H // I ph.1 ph.2 ∧ ¬ J (phi ph.1) (psi ph.2) } : ℝ) := by
  classical
  unfold brokenFlagSum incidence
  rw [← Fintype.sum_prod_type']
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert Finset.sum_boole (R := ℝ) (fun ph : P × H => I ph.1 ph.2 ∧
    ¬ J (phi ph.1) (psi ph.2)) Finset.univ using 1
  apply Finset.sum_congr rfl
  intro ph _
  by_cases h : I ph.1 ph.2 ∧ ¬ J (phi ph.1) (psi ph.2) <;> simp [h]

theorem brokenFlagSum_nonneg (I : P → H → Prop) (J : P' → H' → Prop)
    (phi : P → P') (psi : H → H') : 0 ≤ brokenFlagSum I J phi psi := by
  rw [brokenFlagSum_eq_card]
  positivity

/-- Disjoint counting of wrong-point/correct-hyperplane and dual errors. -/
theorem disjoint_error_count (I : P → H → Prop) (J : P' → H' → Prop)
    (phi Gp : P → P') (psi Gh : H → H') (S : Finset P) (B : Finset H)
    (hS : ∀ p, p ∈ S ↔ phi p ≠ Gp p)
    (hB : ∀ h, h ∈ B ↔ psi h ≠ Gh h)
    (d lam : ℝ)
    (hdegree : ∀ p, ∑ h, incidence I p h = d)
    (hdual : ∀ h, ∑ p, incidence I p h = d)
    (hpoint : ∀ p ∈ S,
      ∑ h, incidence (fun p h => I p h ∧ J (phi p) (Gh h)) p h ≤ lam)
    (hhyper : ∀ h ∈ B,
      ∑ p, incidence (fun p h => I p h ∧ J (Gp p) (psi h)) p h ≤ lam) :
    (d - lam) * ((S.card : ℝ) + B.card) - 2 * cross I S B ≤
      brokenFlagSum I J phi psi := by
  classical
  let ep : P → H → ℝ := fun p h =>
    incidence (fun p h => p ∈ S ∧ h ∉ B ∧ I p h ∧ ¬ J (phi p) (psi h)) p h
  let eh : P → H → ℝ := fun p h =>
    incidence (fun p h => p ∉ S ∧ h ∈ B ∧ I p h ∧ ¬ J (phi p) (psi h)) p h
  have hp : ∀ p ∈ S, d - lam ≤ (∑ h, ep p h) + ∑ h ∈ B, incidence I p h := by
    intro p hp
    have hs : ∀ h, incidence I p h ≤ ep p h +
        incidence (fun p h => I p h ∧ J (phi p) (Gh h)) p h +
        (if h ∈ B then incidence I p h else 0) := by
      intro h
      by_cases hb : h ∈ B
      · simp [ep, incidence, hp, hb]
        split_ifs <;> simp_all
      · have heq : psi h = Gh h := not_not.mp (fun hn => hb ((hB h).mpr hn))
        simp [ep, incidence, hp, hb, heq]
        split_ifs <;> simp_all
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun h _ => hs h)
    simp only [Finset.sum_add_distrib, hdegree] at hh
    have hf : (∑ h, if h ∈ B then incidence I p h else 0) = ∑ h ∈ B, incidence I p h := by
      simp
    rw [hf] at hh
    linarith [hpoint p hp]
  have hh : ∀ h ∈ B, d - lam ≤ (∑ p, eh p h) + ∑ p ∈ S, incidence I p h := by
    intro h hb
    have hs : ∀ p, incidence I p h ≤ eh p h +
        incidence (fun p h => I p h ∧ J (Gp p) (psi h)) p h +
        (if p ∈ S then incidence I p h else 0) := by
      intro p
      by_cases hp : p ∈ S
      · simp [eh, incidence, hp, hb]
        split_ifs <;> simp_all
      · have heq : phi p = Gp p := not_not.mp (fun hn => hp ((hS p).mpr hn))
        simp [eh, incidence, hp, hb, heq]
        split_ifs <;> simp_all
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hs p)
    simp only [Finset.sum_add_distrib, hdual] at hh
    have hf : (∑ p, if p ∈ S then incidence I p h else 0) = ∑ p ∈ S, incidence I p h := by
      simp
    rw [hf] at hh
    linarith [hhyper h hb]
  have hpall := Finset.sum_le_sum (s := S) hp
  have hhall := Finset.sum_le_sum (s := B) hh
  have hep : (∑ p ∈ S, ∑ h, ep p h) = ∑ p, ∑ h, ep p h := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro p _ hp
    simp [ep, incidence, hp]
  have heh : (∑ h ∈ B, ∑ p, eh p h) = ∑ p, ∑ h, eh p h := by
    rw [Finset.sum_comm (s := Finset.univ)]
    apply Finset.sum_subset (Finset.subset_univ B)
    intro h _ hb
    simp [eh, incidence, hb]
  have hcross : (∑ p ∈ S, ∑ h ∈ B, incidence I p h) = cross I S B := by
    unfold cross load
    rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hpall hhall
  rw [hep, hcross] at hpall
  rw [heh] at hhall
  change (B.card : ℝ) * (d - lam) ≤ (∑ p, ∑ h, eh p h) + cross I S B at hhall
  have hdisj : ∀ p h, ep p h + eh p h ≤
      incidence (fun p h => I p h ∧ ¬ J (phi p) (psi h)) p h := by
    intro p h
    simp only [ep, eh, incidence]
    split_ifs <;> simp_all
  have htotal := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun h _ => hdisj p h))
  simp only [Finset.sum_add_distrib] at htotal
  change (∑ p, ∑ h, ep p h) + (∑ p, ∑ h, eh p h) ≤ brokenFlagSum I J phi psi at htotal
  nlinarith

end Erdos85.IncidenceRepair
