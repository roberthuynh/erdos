import Mathlib

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

variable {P H : Type*} [Fintype P] [Fintype H] [DecidableEq P]

/-- The original incidence indicator; no corrected incidences are counted. -/
def incidence (I : P → H → Prop) (p : P) (h : H) : ℝ :=
  @ite ℝ (I p h) (Classical.propDecidable _) 1 0

/-- Number of points of S on a source hyperplane. -/
def load (I : P → H → Prop) (S : Finset P) (h : H) : ℝ :=
  ∑ p ∈ S, incidence I p h

/-- Actual source incidences between S and B. -/
def cross (I : P → H → Prop) (S : Finset P) (B : Finset H) : ℝ :=
  ∑ h ∈ B, load I S h

theorem load_sum (I : P → H → Prop) (S : Finset P) (d : ℝ)
    (hdegree : ∀ p, ∑ h, incidence I p h = d) :
    ∑ h, load I S h = d * S.card := by
  unfold load
  rw [Finset.sum_comm]
  simp [hdegree, mul_comm]

theorem load_second_moment (I : P → H → Prop) (S : Finset P) (a lam : ℝ)
    (hpair : ∀ p q, ∑ h, incidence I p h * incidence I q h =
      (if p = q then a else 0) + lam) :
    ∑ h, (load I S h)^2 = a * S.card + lam * (S.card : ℝ)^2 := by
  classical
  calc
    _ = ∑ h, ∑ p ∈ S, ∑ q ∈ S, incidence I p h * incidence I q h := by
      apply Finset.sum_congr rfl
      intro h hh
      simp only [load, pow_two, Finset.sum_mul_sum]
    _ = ∑ p ∈ S, ∑ q ∈ S, ∑ h, incidence I p h * incidence I q h := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ = ∑ p ∈ S, ∑ q ∈ S, ((if p = q then a else 0) + lam) := by
      simp only [hpair]
    _ = a * S.card + lam * (S.card : ℝ)^2 := by
      simp [Finset.sum_add_distrib, Finset.sum_ite_eq', mul_comm]
      ring

/-- The design parameter relation follows from both degree counts and codegrees. -/
theorem design_parameters [Nonempty P] (I : P → H → Prop) (a d lam N : ℝ)
    (hN : N = Fintype.card P)
    (hdegree : ∀ p, ∑ h, incidence I p h = d)
    (hdual : ∀ h, ∑ p, incidence I p h = d)
    (hpair : ∀ p q, ∑ h, incidence I p h * incidence I q h =
      (if p = q then a else 0) + lam) :
    d^2 = a + lam * N := by
  classical
  let p : P := Classical.choice inferInstance
  have h := congrArg (fun f : P → ℝ => ∑ q, f q) (funext (hpair p))
  rw [Finset.sum_comm] at h
  simp only [← Finset.mul_sum, hdual] at h
  rw [← Finset.sum_mul, hdegree] at h
  simpa [Finset.sum_add_distrib, ← hN, pow_two, mul_comm] using h

/-- Variance computed from the source design, rather than assumed. -/
theorem design_variance (I : P → H → Prop) (S : Finset P) (a d lam N : ℝ)
    (hN : N = Fintype.card H) (hNpos : 0 < N)
    (hdegree : ∀ p, ∑ h, incidence I p h = d)
    (hpair : ∀ p q, ∑ h, incidence I p h * incidence I q h =
      (if p = q then a else 0) + lam)
    (hparameters : d^2 = a + lam * N) :
    ∑ h, (load I S h - d * S.card / N)^2 =
      a * S.card * (1 - S.card / N) := by
  have hfirst := load_sum I S d hdegree
  have hsecond := load_second_moment I S a lam hpair
  have hN0 : N ≠ 0 := ne_of_gt hNpos
  calc
    _ = (∑ h, (load I S h)^2) -
        2 * (d * S.card / N) * (∑ h, load I S h) +
        (Fintype.card H : ℝ) * (d * S.card / N)^2 := by
      simp_rw [show ∀ x : ℝ, (x - d * S.card / N)^2 =
        x^2 - (2 * (d * S.card / N)) * x + (d * S.card / N)^2 by
          intro x; ring]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = a * S.card * (1 - S.card / N) := by
      rw [hfirst, hsecond, ← hN]
      field_simp
      nlinarith [hparameters]

end Erdos85.IncidenceRepair
