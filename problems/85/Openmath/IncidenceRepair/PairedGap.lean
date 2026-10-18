import Openmath.IncidenceRepair.DesignVariance

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

variable {P H : Type*} [Fintype P] [Fintype H] [DecidableEq P] [DecidableEq H]

def memberIndicator (B : Finset H) (h : H) : ℝ := if h ∈ B then 1 else 0

theorem indicator_sum (B : Finset H) : ∑ h, memberIndicator B h = (B.card : ℝ) := by
  simp [memberIndicator]

theorem indicator_variance (B : Finset H) (N : ℝ)
    (hN : N = Fintype.card H) (hNpos : 0 < N) :
    ∑ h, (memberIndicator B h - B.card / N)^2 = B.card * (1 - B.card / N) := by
  have hfirst := indicator_sum B
  have hsecond : ∑ h, (memberIndicator B h)^2 = (B.card : ℝ) := by
    simp [memberIndicator]
  have hN0 : N ≠ 0 := ne_of_gt hNpos
  calc
    _ = (∑ h, (memberIndicator B h)^2) -
        (2 * (B.card / N)) * (∑ h, memberIndicator B h) +
        (Fintype.card H : ℝ) * (B.card / N)^2 := by
      simp_rw [show ∀ x : ℝ, (x - B.card / N)^2 =
        x^2 - (2 * (B.card / N)) * x + (B.card / N)^2 by intro x; ring]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = B.card * (1 - B.card / N) := by
      rw [hfirst, hsecond, ← hN]
      field_simp
      ring

theorem cross_centered (I : P → H → Prop) (S : Finset P) (B : Finset H)
    (d N : ℝ) (hN : N = Fintype.card H) (hNpos : 0 < N)
    (hdegree : ∀ p, ∑ h, incidence I p h = d) :
    ∑ h, (load I S h - d * S.card / N) * (memberIndicator B h - B.card / N) =
      cross I S B - d * S.card * B.card / N := by
  have hfirst := load_sum I S d hdegree
  have hind := indicator_sum B
  have hcross : ∑ h, load I S h * memberIndicator B h = cross I S B := by
    simp [memberIndicator, cross]
  have hN0 : N ≠ 0 := ne_of_gt hNpos
  calc
    _ = (∑ h, load I S h * memberIndicator B h) -
      (B.card / N) * (∑ h, load I S h) -
      (d * S.card / N) * (∑ h, memberIndicator B h) +
      (Fintype.card H : ℝ) * ((d * S.card / N) * (B.card / N)) := by
      simp_rw [show ∀ x y : ℝ, (x - d * S.card / N) * (y - B.card / N) =
        x*y - (B.card / N)*x - (d*S.card/N)*y + (d*S.card/N)*(B.card/N) by
          intro x y; ring]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ = cross I S B - d * S.card * B.card / N := by
      rw [hfirst, hind, hcross, ← hN]
      field_simp
      ring

/-- Centered Cauchy--Schwarz for the actual two source subsets. -/
theorem cross_bound (I : P → H → Prop) (S : Finset P) (B : Finset H)
    (a d lam N : ℝ) (hN : N = Fintype.card H) (hNpos : 0 < N)
    (hdegree : ∀ p, ∑ h, incidence I p h = d)
    (hpair : ∀ p q, ∑ h, incidence I p h * incidence I q h =
      (if p = q then a else 0) + lam)
    (hparameters : d^2 = a + lam * N) :
    cross I S B ≤ d * S.card * B.card / N +
      Real.sqrt (a * S.card * (1 - S.card / N)) *
      Real.sqrt (B.card * (1 - B.card / N)) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun h => load I S h - d * S.card / N)
    (fun h => memberIndicator B h - B.card / N)
  rw [cross_centered I S B d N hN hNpos hdegree,
    design_variance I S a d lam N hN hNpos hdegree hpair hparameters,
    indicator_variance B N hN hNpos] at hcs
  linarith

theorem cross_bound_total (I : P → H → Prop) (S : Finset P) (B : Finset H)
    (a d lam N : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hN : N = Fintype.card H) (hNpos : 0 < N)
    (hdegree : ∀ p, ∑ h, incidence I p h = d)
    (hpair : ∀ p q, ∑ h, incidence I p h * incidence I q h =
      (if p = q then a else 0) + lam)
    (hparameters : d^2 = a + lam * N) :
    cross I S B ≤ d * ((S.card : ℝ) + B.card)^2 / (4*N) +
      Real.sqrt a * (S.card + B.card) / 2 := by
  have hs : 0 ≤ (S.card : ℝ) := by positivity
  have ht : 0 ≤ (B.card : ℝ) := by positivity
  have hsN : 0 ≤ (S.card : ℝ)/N := div_nonneg hs hNpos.le
  have htN : 0 ≤ (B.card : ℝ)/N := div_nonneg ht hNpos.le
  have hsbound : a * S.card * (1 - S.card / N) ≤ a * S.card := by
    nlinarith [mul_nonneg (mul_nonneg ha hs) hsN]
  have htbound : (B.card : ℝ) * (1 - B.card / N) ≤ B.card := by
    nlinarith [mul_nonneg ht htN]
  have hrad := mul_le_mul (Real.sqrt_le_sqrt hsbound) (Real.sqrt_le_sqrt htbound)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [Real.sqrt_mul ha] at hrad
  have ham : Real.sqrt (S.card : ℝ) * Real.sqrt (B.card : ℝ) ≤
      ((S.card : ℝ) + B.card)/2 := by
    nlinarith [sq_nonneg (Real.sqrt (S.card : ℝ) - Real.sqrt (B.card : ℝ)),
      Real.sq_sqrt hs, Real.sq_sqrt ht]
  have hrad2 := mul_le_mul_of_nonneg_left ham (Real.sqrt_nonneg a)
  have hmean : d * S.card * B.card / N ≤
      d * ((S.card : ℝ) + B.card)^2 / (4*N) := by
    have h := mul_nonneg (div_nonneg hd hNpos.le)
      (sq_nonneg ((S.card : ℝ) - B.card))
    simp only [div_eq_mul_inv, mul_inv_rev] at h ⊢
    norm_num at h ⊢
    nlinarith
  have hcross := cross_bound I S B a d lam N hN hNpos hdegree hpair hparameters
  nlinarith

/-- Section 8's paired gap. The remaining input is the independently counted
    disjoint broken-flag lower bound, not a variance or mixing assumption. -/
theorem paired_gap (I : P → H → Prop) (S : Finset P) (B : Finset H)
    (a d lam N T : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hN : N = Fintype.card H) (hNpos : 0 < N)
    (hdegree : ∀ p, ∑ h, incidence I p h = d)
    (hpair : ∀ p q, ∑ h, incidence I p h * incidence I q h =
      (if p = q then a else 0) + lam)
    (hparameters : d^2 = a + lam * N)
    (hbroken : a * ((S.card : ℝ) + B.card) - 2 * cross I S B ≤ T) :
    (a - Real.sqrt a - d*((S.card : ℝ) + B.card)/(2*N)) *
      ((S.card : ℝ) + B.card) ≤ T := by
  have hc := cross_bound_total I S B a d lam N ha hd hN hNpos
    hdegree hpair hparameters
  simp only [div_eq_mul_inv, mul_inv_rev] at hc ⊢
  norm_num at hc ⊢
  nlinarith

end Erdos85.IncidenceRepair
