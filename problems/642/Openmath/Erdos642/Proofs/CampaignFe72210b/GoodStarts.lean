import Openmath.Erdos642.Proofs.CampaignFe72210b.PathCoordinates

namespace Erdos642.FiniteMarkov.Chain
open PathCoordinates
variable {V : Type*} [Fintype V] [DecidableEq V] (C : Chain V)

/-- A good start avoids every extension by at most k exposed vertices. -/
def Good (k : ℕ) (β H : ℝ) (A : Finset V) (v : V) : Prop :=
  ∀ S : Finset V, S.card ≤ k →
    1-β-H ≤ C.eventMass k (fun x p => ¬ actualHit (A ∪ S) x p) v

theorem actualHit_union_mass_le (k : ℕ) (A S : Finset V) (v : V) :
    C.eventMass k (actualHit (A ∪ S)) v ≤
      C.eventMass k (actualHit A) v + C.eventMass k (actualHit S) v := by
  classical
  apply (C.eventMass_mono (actualHit (A ∪ S))
    (fun x p => actualHit A x p ∨ actualHit S x p) ?_ v).trans
    (C.eventMass_union_le (actualHit A) (actualHit S) v)
  intro x p hp
  obtain ⟨a, ha, hAS⟩ := hp
  rcases Finset.mem_union.mp hAS with hA | hS
  · exact Or.inl ⟨a, ha, hA⟩
  · exact Or.inr ⟨a, ha, hS⟩

theorem hit_le_beta_implies_good (k : ℕ) (β H : ℝ)
    (hlocal : ∀ v (S : Finset V), S.card ≤ k → C.eventMass k (actualHit S) v ≤ H)
    (A : Finset V) (v : V) (hv : C.eventMass k (actualHit A) v ≤ β) :
    C.Good k β H A v := by
  intro S hS
  rw [C.eventMass_compl]
  have hu := C.actualHit_union_mass_le k A S v
  have hs := hlocal v S hS
  linarith

theorem notGood_implies_hit_gt_beta (k : ℕ) (β H : ℝ)
    (hlocal : ∀ v (S : Finset V), S.card ≤ k → C.eventMass k (actualHit S) v ≤ H)
    (A : Finset V) (v : V) (hv : ¬ C.Good k β H A v) :
    β < C.eventMass k (actualHit A) v := by
  by_contra h
  exact hv (C.hit_le_beta_implies_good k β H hlocal A v (le_of_not_gt h))

theorem sum_actualHit_le (k : ℕ) (R : ℝ)
    (hcol : ∀ t ∈ Finset.Icc 1 k, ∀ a, ∑ v, (C.transition^t) v a ≤ R)
    (A : Finset V) :
    (∑ v, C.eventMass k (actualHit A) v) ≤ R * (k : ℝ) * (A.card : ℝ) := by
  classical
  calc
    (∑ v, C.eventMass k (actualHit A) v) ≤
        ∑ v, ∑ t ∈ Finset.Icc 1 k, ∑ a ∈ A, (C.transition^t) v a := by
      apply Finset.sum_le_sum
      intro v _
      exact C.actualHit_mass_le k A v
    _ = ∑ t ∈ Finset.Icc 1 k, ∑ a ∈ A, ∑ v, (C.transition^t) v a := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_comm]
    _ ≤ ∑ t ∈ Finset.Icc 1 k, ∑ _a ∈ A, R := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro a _
      exact hcol t ht a
    _ = R * (k : ℝ) * (A.card : ℝ) := by
      simp [Nat.card_Icc]
      ring

noncomputable def badStarts (k : ℕ) (β H : ℝ) (A : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ¬ C.Good k β H A v

theorem badStart_card_le (k : ℕ) (β H R : ℝ) (_hβ : 0 < β)
    (hlocal : ∀ v (S : Finset V), S.card ≤ k → C.eventMass k (actualHit S) v ≤ H)
    (hcol : ∀ t ∈ Finset.Icc 1 k, ∀ a, ∑ v, (C.transition^t) v a ≤ R)
    (A : Finset V) :
    β * ((C.badStarts k β H A).card : ℝ) ≤
      R * (k : ℝ) * (A.card : ℝ) := by
  classical
  let B := Finset.univ.filter fun v => ¬ C.Good k β H A v
  have hB : (∑ v ∈ B, β) ≤ ∑ v ∈ B, C.eventMass k (actualHit A) v := by
    apply Finset.sum_le_sum
    intro v hv
    exact (C.notGood_implies_hit_gt_beta k β H hlocal A v
      (Finset.mem_filter.mp hv).2).le
  have hsub : (∑ v ∈ B, C.eventMass k (actualHit A) v) ≤
      ∑ v, C.eventMass k (actualHit A) v := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
    intro v _ _
    exact C.eventMass_nonneg k (actualHit A) v
  have h := hB.trans (hsub.trans (C.sum_actualHit_le k R hcol A))
  simpa [B, badStarts, mul_comm] using h

theorem good_empty (k : ℕ) (β H : ℝ) (hβ : 0 ≤ β)
    (hlocal : ∀ v (S : Finset V), S.card ≤ k → C.eventMass k (actualHit S) v ≤ H)
    (v : V) : C.Good k β H ∅ v := by
  apply C.hit_le_beta_implies_good k β H hlocal ∅ v
  simpa [eventMass, actualHit] using hβ
end Erdos642.FiniteMarkov.Chain
