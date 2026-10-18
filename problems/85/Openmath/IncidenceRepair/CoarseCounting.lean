import Openmath.IncidenceRepair.ErrorCounting

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

variable {P H P' H' : Type*} [Fintype P] [Fintype H]
  [DecidableEq P] [DecidableEq H]

/-- Coarse counting on actual subsets of the original incidence relation.
`S` is precisely the point errors inside `U`; `C` is the selected set of
hyperplanes. The surviving-flag estimate compares the embedded point with the
actual hyperplane assignment. Every flag charged is an original source flag. -/
theorem coarse_count (I : P → H → Prop) (J : P' → H' → Prop)
    (phi Gp : P → P') (psi : H → H')
    (U S : Finset P) (C : Finset H) (a c d : ℝ)
    (hSU : S ⊆ U)
    (hS : ∀ p ∈ U, p ∈ S ↔ phi p ≠ Gp p)
    (hdegree : ∀ h ∈ C, ∑ p ∈ U, incidence I p h = a)
    (hrow : ∀ p ∈ S, ∑ h ∈ C, incidence I p h ≤ d)
    (hsurvive : ∀ h ∈ C,
      ∑ p ∈ U, incidence (fun p h => I p h ∧ J (Gp p) (psi h)) p h ≤ c) :
    (a-c) * C.card ≤ brokenFlagSum I J phi psi + d * S.card := by
  classical
  let e : P → H → ℝ := fun p h =>
    incidence (fun p h => I p h ∧ ¬ J (phi p) (psi h)) p h
  have hper : ∀ h ∈ C, a-c ≤ (∑ p ∈ U, e p h) + ∑ p ∈ S, incidence I p h := by
    intro h hh
    have hflag : ∀ p ∈ U, incidence I p h ≤ e p h +
        incidence (fun p h => I p h ∧ J (Gp p) (psi h)) p h +
        (if p ∈ S then incidence I p h else 0) := by
      intro p hp
      by_cases hs : p ∈ S
      · simp [e, incidence, hs]
        split_ifs <;> simp_all
      · have heq : phi p = Gp p := not_not.mp (fun hn => hs ((hS p hp).mpr hn))
        simp [e, incidence, hs, heq]
        split_ifs <;> simp_all
    have hsum := Finset.sum_le_sum hflag
    have hbad : (∑ p ∈ U, if p ∈ S then incidence I p h else 0) =
        ∑ p ∈ S, incidence I p h := by
      rw [← Finset.sum_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hp => ⟨hSU hp, hp⟩⟩
    simp only [Finset.sum_add_distrib, hdegree h hh] at hsum
    rw [hbad] at hsum
    linarith [hsurvive h hh]
  have hall := Finset.sum_le_sum hper
  have herrors : (∑ h ∈ C, ∑ p ∈ U, e p h) ≤ brokenFlagSum I J phi psi := by
    rw [Finset.sum_comm]
    change (∑ p ∈ U, ∑ h ∈ C, e p h) ≤ ∑ p, ∑ h, e p h
    have he : ∀ p h, 0 ≤ e p h := by
      intro p h
      simp only [e, incidence]
      split_ifs <;> positivity
    calc
      _ ≤ ∑ p ∈ U, ∑ h, e p h := by
        apply Finset.sum_le_sum
        intro p hp
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
          (fun h _ _ => he p h)
      _ ≤ ∑ p, ∑ h, e p h :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
          (fun p _ _ => Finset.sum_nonneg (fun h _ => he p h))
  have hbadtotal : (∑ h ∈ C, ∑ p ∈ S, incidence I p h) ≤ d*S.card := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ p ∈ S, d := Finset.sum_le_sum hrow
      _ = d*S.card := by simp [mul_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hall
  nlinarith

/-- Affine part of §7.1 with the source intersection cap a/q. -/
theorem coarse_affine_count (I : P → H → Prop) (J : P' → H' → Prop)
    (phi Gp : P → P') (psi : H → H')
    (U S : Finset P) (C : Finset H) (a q d : ℝ)
    (hSU : S ⊆ U)
    (hS : ∀ p ∈ U, p ∈ S ↔ phi p ≠ Gp p)
    (hdegree : ∀ h ∈ C, ∑ p ∈ U, incidence I p h = a)
    (hrow : ∀ p ∈ S, ∑ h ∈ C, incidence I p h ≤ d)
    (hsurvive : ∀ h ∈ C,
      ∑ p ∈ U, incidence (fun p h => I p h ∧ J (Gp p) (psi h)) p h ≤ a/q) :
    (a-a/q) * C.card ≤ brokenFlagSum I J phi psi + d * S.card :=
  coarse_count I J phi Gp psi U S C a (a/q) d hSU hS hdegree hrow hsurvive

/-- Infinity-point part of §7.2, obtained by dualizing the same actual flags. -/
theorem coarse_infinity_count (I : P → H → Prop) (J : P' → H' → Prop)
    (phi : P → P') (psi Gh : H → H')
    (U B : Finset H) (S : Finset P) (a d lam : ℝ)
    (hBU : B ⊆ U)
    (hB : ∀ h ∈ U, h ∈ B ↔ psi h ≠ Gh h)
    (ha : a = d-lam)
    (hdegree : ∀ p ∈ S, ∑ h ∈ U, incidence I p h = d-1)
    (hrow : ∀ h ∈ B, ∑ p ∈ S, incidence I p h ≤ lam)
    (hsurvive : ∀ p ∈ S,
      ∑ h ∈ U, incidence (fun p h => I p h ∧ J (phi p) (Gh h)) p h ≤ lam) :
    (a-1) * S.card ≤ brokenFlagSum I J phi psi + lam * B.card := by
  have hc := coarse_count (fun h p => I p h) (fun h p => J p h)
    psi Gh phi U B S (d-1) lam lam hBU hB hdegree hrow hsurvive
  have hdual : brokenFlagSum (fun h p => I p h) (fun h p => J p h) psi phi =
      brokenFlagSum I J phi psi := by
    unfold brokenFlagSum incidence
    rw [Finset.sum_comm]
  rw [hdual] at hc
  rw [ha]
  convert hc using 1 <;> ring

end Erdos85.IncidenceRepair
