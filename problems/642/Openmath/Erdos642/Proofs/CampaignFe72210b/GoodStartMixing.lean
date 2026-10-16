import Openmath.Erdos642.Proofs.CampaignFe72210b.GoodStarts

namespace Erdos642.FiniteMarkov.Chain
open PathCoordinates
variable {V : Type*} [Fintype V] [DecidableEq V] (C : Chain V)

/-- An actual endpoint event has the transition-power marginal. -/
theorem endpoint_eventMass (k : ℕ) (B : V → Prop) [DecidablePred B] (x : V) :
    C.eventMass k (fun z p => B (C.endpoint z p)) x =
      ∑ y, if B y then (C.transition^k) x y else 0 := by
  classical
  calc
    C.eventMass k (fun z p => B (C.endpoint z p)) x =
        ∑ p : Path V k, ∑ y : V,
          if C.endpoint x p = y then (if B y then C.weight x p else 0) else 0 := by
      unfold eventMass
      apply Finset.sum_congr rfl
      intro p _
      simp
    _ = ∑ y : V, ∑ p : Path V k,
          if C.endpoint x p = y then (if B y then C.weight x p else 0) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ y, if B y then (C.transition^k) x y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hb : B y
      · simp only [hb, if_true]
        exact C.endpoint_marginal k x y
      · simp [hb]

/-- Mixing controls the mass of literal bad endpoints. -/
theorem endpoint_bad_mass_le_mixing (k : ℕ) (β H M N : ℝ) (A : Finset V)
    (hmix : ∀ x y, (C.transition^k) x y ≤ M/N) (x : V) :
    C.eventMass k (fun z p => ¬ C.Good k β H A (C.endpoint z p)) x ≤
      (M/N) * ((C.badStarts k β H A).card : ℝ) := by
  classical
  rw [C.endpoint_eventMass k (fun y => ¬ C.Good k β H A y) x]
  calc
    (∑ y, if ¬ C.Good k β H A y then (C.transition^k) x y else 0) ≤
        ∑ y, if ¬ C.Good k β H A y then M/N else 0 := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hg : C.Good k β H A y
      · simp [hg]
      · simpa only [hg, not_false_eq_true, if_true] using hmix x y
    _ = (M/N) * ((C.badStarts k β H A).card : ℝ) := by
      unfold badStarts
      rw [← Finset.sum_filter]
      simp [mul_comm]

/-- The order premise forces the actual endpoint failure probability below beta. -/
theorem endpoint_bad_mass_le_beta (k q : ℕ) (β H M N R : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hlocal : ∀ v (S : Finset V), S.card ≤ k → C.eventMass k (actualHit S) v ≤ H)
    (hcol : ∀ t ∈ Finset.Icc 1 k, ∀ a, ∑ v, (C.transition^t) v a ≤ R)
    (hmix : ∀ x y, (C.transition^k) x y ≤ M/N)
    (horder : M*R*(k:ℝ)*((q*k+1:ℕ):ℝ) ≤ β^2*N)
    (A : Finset V) (hA : A.card ≤ q*k+1) (x : V) :
    C.eventMass k (fun z p => ¬ C.Good k β H A (C.endpoint z p)) x ≤ β := by
  have hb := C.badStart_card_le k β H R hβ hlocal hcol A
  have hA' : (A.card:ℝ) ≤ ((q*k+1:ℕ):ℝ) := by exact_mod_cast hA
  have hMRk : 0 ≤ M*R*(k:ℝ) := mul_nonneg (mul_nonneg hM hR) (Nat.cast_nonneg k)
  have ho := (mul_le_mul_of_nonneg_left hA' hMRk).trans horder
  have hmul := mul_le_mul_of_nonneg_left hb hM
  have hbound : M*((C.badStarts k β H A).card:ℝ) ≤ β*N := by
    apply (mul_le_mul_iff_right₀ hβ).mp
    nlinarith
  have hdiv : (M/N)*((C.badStarts k β H A).card:ℝ) ≤ β := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hN).mpr
    nlinarith
  exact (C.endpoint_bad_mass_le_mixing k β H M N A hmix x).trans hdiv
end Erdos642.FiniteMarkov.Chain
