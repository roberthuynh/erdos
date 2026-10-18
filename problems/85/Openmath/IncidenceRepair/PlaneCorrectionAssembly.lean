import Openmath.IncidenceRepair.Pexider
import Openmath.IncidenceRepair.AllSlopes
import Openmath.IncidenceRepair.PlaneGeometry

/-! Assembly of additive correction and actual target-line counting.
All geometric error bounds remain explicit inputs; no field embedding is assumed. -/
noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair.Plane
attribute [local instance] Classical.propDecidable
variable {K L : Type*} [Field K] [Fintype K] [Field L]

lemma count_eq_filter_card {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p] :
    count p = ((Finset.univ.filter p).card : ℝ) := by
  classical
  simp only [count, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p x <;> simp [hx]

lemma count_pair_second (p : K → Prop) :
    count (fun z : K × K => p z.2) = count p * Fintype.card K := by
  have he := count_equiv (Equiv.prodComm K K) (fun z : K × K => p z.1)
  exact he.trans (Pexider.count_pair_first p)

lemma corrected_affine_count (φ : Point K 2 → Point L 2) (f g h : K → L) :
    count (fun z : K × K => φ (affine z.1 z.2) ≠ affine (h z.1) (h z.2)) ≤
      count (fun z : K × K => φ (affine z.1 z.2) ≠ affine (f z.1) (g z.2)) +
      (count (fun x => f x ≠ h x) + count (fun y => g y ≠ h y)) * Fintype.card K := by
  classical
  let p : K × K → Prop := fun z => φ (affine z.1 z.2) ≠ affine (f z.1) (g z.2)
  let r : K × K → Prop := fun z => f z.1 ≠ h z.1
  let s : K × K → Prop := fun z => g z.2 ≠ h z.2
  have hm : count (fun z : K × K => φ (affine z.1 z.2) ≠ affine (h z.1) (h z.2))
      ≤ count (fun z => p z ∨ r z ∨ s z) := by
    apply count_mono
    intro z hz
    by_contra hn
    simp only [not_or, not_not, p, r, s] at hn
    exact hz (by rw [hn.1, hn.2.1, hn.2.2])
  have h1 := count_or_le p (fun z => r z ∨ s z)
  have h2 := count_or_le r s
  have hr : count r = count (fun x => f x ≠ h x) * Fintype.card K :=
    Pexider.count_pair_first (fun x : K => f x ≠ h x)
  have hs : count s = count (fun y => g y ≠ h y) * Fintype.card K :=
    count_pair_second (fun x : K => g x ≠ h x)
  dsimp [p] at h1
  rw [hr, hs] at h2
  nlinarith

/-- For each fixed slope, the intercept/parameter pair traverses each affine point once. -/
lemma line_parameter_reindex (a : K) (p : K → K → Prop) :
    (∑ b : K, count (fun x => p x (a*x+b))) =
      count (fun z : K × K => p z.1 z.2) := by
  classical
  let e : K × K ≃ K × K :=
    { toFun := fun z => (z.2, a*z.2+z.1)
      invFun := fun z => (z.2-a*z.1, z.1)
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp }
  rw [← count_prod (fun b x : K => p x (a*x+b))]
  exact count_equiv e (fun z : K × K => p z.1 z.2)

/-- Summing over slopes uses every affine point exactly q times. -/
lemma line_parameter_total (p : K → K → Prop) :
    (∑ a : K, ∑ b : K, count (fun x => p x (a*x+b))) =
      Fintype.card K * count (fun z : K × K => p z.1 z.2) := by
  simp_rw [line_parameter_reindex]
  simp

/-- The plane correction after the geometric support/product/Pexider estimates.
Line exceptions here are the actual broken incidences with the supplied target line map. -/
theorem corrected_field_embedding
    (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2)
    (f g c : K → L) (η : ℝ) (hη : 0 ≤ η) (hsmall : η ≤ 1/10000000)
    (herr : Pexider.errorCount f g c ≤ (36*η) * (Fintype.card K : ℝ)^2)
    (hrow : ∀ i : K, i = 0 ∨ i = 1 →
      count (fun b => g (i+b) ≠ f i+c b) ≤ 20*η*Fintype.card K)
    (hdiag : count (fun x => g x ≠ f x) ≤ 36*η*Fintype.card K)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hproduct : count (fun z : K × K =>
      φ (affine z.1 z.2) ≠ affine (f z.1) (g z.2)) ≤ 35*η*(Fintype.card K : ℝ)^2)
    (hflags : (∑ a : K, ∑ b : K, count (fun x =>
      ¬ Incident (φ (affine x (a*x+b))) (ψ (slope a b)))) ≤
        η*(Fintype.card K : ℝ)^3) :
    ∃ σ : K →+* L,
      count (fun x => f x ≠ σ x) ≤ 288*η*Fintype.card K ∧
      count (fun x => g x ≠ σ x) ≤ 648*η*Fintype.card K ∧
      count (fun z : K × K => φ (affine z.1 z.2) ≠ affine (σ z.1) (σ z.2))
        ≤ 971*η*(Fintype.card K : ℝ)^2 := by
  classical
  obtain ⟨h, h1, hf, hg⟩ := Pexider.protected_pexider f g c η hη hsmall
    herr hrow hdiag hf0 hf1
  have hq : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hpoints : count (fun z : K × K => φ (affine z.1 z.2) ≠ affine (h z.1) (h z.2))
      ≤ 971*η*(Fintype.card K : ℝ)^2 := by
    have hp := corrected_affine_count φ f g h
    have hf' := mul_le_mul_of_nonneg_right hf (le_of_lt hq)
    have hg' := mul_le_mul_of_nonneg_right hg (le_of_lt hq)
    nlinarith
  let marked : K → K → K → Prop := fun a b x =>
    φ (affine x (a*x+b)) ≠ affine (h x) (h (a*x+b)) ∨
      ¬ Incident (φ (affine x (a*x+b))) (ψ (slope a b))
  have hmarks : (∑ a : K, ∑ b : K, count (marked a b)) ≤
      972*η*(Fintype.card K : ℝ)^3 := by
    have hbound : (∑ a : K, ∑ b : K, count (marked a b)) ≤
        (∑ a : K, ∑ b : K, count (fun x => φ (affine x (a*x+b)) ≠
          affine (h x) (h (a*x+b)))) +
        (∑ a : K, ∑ b : K, count (fun x =>
          ¬ Incident (φ (affine x (a*x+b))) (ψ (slope a b)))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro b _
      exact count_or_le _ _
    rw [line_parameter_total (fun x y => φ (affine x y) ≠ affine (h x) (h y))] at hbound
    have hp := mul_le_mul_of_nonneg_left hpoints (le_of_lt hq)
    nlinarith
  have hfew : 4 * (∑ a : K, ∑ b : K, (Finset.univ.filter (marked a b)).card) <
      Fintype.card K ^ 3 := by
    have heq : (∑ a : K, ∑ b : K, count (marked a b)) =
        ((∑ a : K, ∑ b : K, (Finset.univ.filter (marked a b)).card : ℕ) : ℝ) := by
      simp only [count_eq_filter_card, Nat.cast_sum]
    rw [heq] at hmarks
    have hpow : (0 : ℝ) < (Fintype.card K : ℝ)^3 := pow_pos hq _
    have hh := mul_le_mul_of_nonneg_right hsmall (le_of_lt hpow)
    have : (4 : ℝ) * (∑ a : K, ∑ b : K, (Finset.univ.filter (marked a b)).card) <
        (Fintype.card K : ℝ)^3 := by nlinarith
    exact_mod_cast this
  obtain ⟨σ, hσ⟩ := exists_ringHom_of_few_line_exceptions h h1 marked
    (fun a b => (ψ (slope a b)).rep 0)
    (fun a b => (ψ (slope a b)).rep 1)
    (fun a b => -(ψ (slope a b)).rep 2)
    (by intro a b; simpa using coefficients_nonzero (ψ (slope a b)))
    (by
      intro a b x hx
      have hp : φ (affine x (a*x+b)) = affine (h x) (h (a*x+b)) := by
        exact not_ne_iff.mp (not_or.mp hx).1
      have hi := (not_or.mp hx).2
      rw [hp] at hi
      exact (affine_incident_iff _ _ _).mp (not_not.mp hi)) hfew
  refine ⟨σ, ?_, ?_, ?_⟩
  · simpa only [hσ] using hf
  · simpa only [hσ] using hg
  · simpa only [hσ] using hpoints
end Erdos85.IncidenceRepair.Plane
