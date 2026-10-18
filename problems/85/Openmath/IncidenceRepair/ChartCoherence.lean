import Openmath.IncidenceRepair.AdditiveCorrection
import Openmath.IncidenceRepair.FieldCoherence

/-! Common-pencil scalar coherence and coordinate budgets. -/
noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair.Chart
attribute [local instance] Classical.propDecidable
variable {K L J : Type*} [Field K] [Fintype K] [Field L] [Fintype J]

omit [Field K] in
lemma count_eq_card (p : K → Prop) [DecidablePred p] :
    count p = ((Finset.univ.filter p).card : ℝ) := by
  classical
  simp only [count, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p x <;> simp [hx]

/-- Chart embeddings agree because they approximate the same first function. -/
theorem embeddings_cohere (j₀ : J) (σ : J → K →+* L) (f₁ : K → L) (η : J → ℝ)
    (hη : ∀ j, 0 ≤ η j) (hsum : (∑ j, η j) ≤ 1/10000000)
    (hfirst : ∀ j, count (fun x => f₁ x ≠ σ j x) ≤ 288*η j*Fintype.card K) :
    ∀ j, σ j = σ j₀ := by
  classical
  have hq : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hj (j : J) : η j ≤ ∑ k, η k :=
    Finset.single_le_sum (fun k _ => hη k) (Finset.mem_univ j)
  intro j
  by_cases heq : j = j₀
  · subst j; rfl
  have hb₁ := hfirst j
  have hb₂ := hfirst j₀
  have hr : 2 * (count (fun x => f₁ x ≠ σ j x) +
      count (fun x => f₁ x ≠ σ j₀ x)) < Fintype.card K := by
    have hbudget := mul_le_mul_of_nonneg_right hsum (le_of_lt hq)
    have hjq := mul_le_mul_of_nonneg_right (hj j) (le_of_lt hq)
    have hj₀q := mul_le_mul_of_nonneg_right (hj j₀) (le_of_lt hq)
    nlinarith
  have hnat : 2 * ((Finset.univ.filter fun x => σ j x ≠ f₁ x).card +
      (Finset.univ.filter fun x => σ j₀ x ≠ f₁ x).card) < Fintype.card K := by
    simp only [count_eq_card] at hr
    have hswap (k : J) : (Finset.univ.filter fun x => f₁ x ≠ σ k x) =
        (Finset.univ.filter fun x => σ k x ≠ f₁ x) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_comm]
    rw [hswap j, hswap j₀] at hr
    exact_mod_cast hr
  have ha := additive_eq_of_common_approximation
    (σ j).toAddMonoidHom (σ j₀).toAddMonoidHom f₁ hnat
  ext x
  exact congrArg (fun h : K →+ L => h x) ha

def coordinates (f₁ : K → L) (f : J → K → L) : Option J → K → L
  | none => f₁
  | some j => f j

def properCoordinates (p₁ : Finset K) (p : J → Finset K) : Option J → Finset K
  | none => p₁
  | some j => p j

/-- The first coordinate is charged once to j₀, others to their own chart. -/
theorem coordinate_budget (j₀ : J) (σ : K →+* L)
    (f₁ : K → L) (f : J → K → L) (p₁ : Finset K) (p : J → Finset K)
    (η : J → ℝ) (hη : ∀ j, 0 ≤ η j)
    (hp₁ : ((Finset.univ \ p₁).card : ℝ) ≤ 17*η j₀*Fintype.card K)
    (hp : ∀ j, ((Finset.univ \ p j).card : ℝ) ≤ 17*η j*Fintype.card K)
    (hf₁ : count (fun x => f₁ x ≠ σ x) ≤ 288*η j₀*Fintype.card K)
    (hf : ∀ j, count (fun x => f j x ≠ σ x) ≤ 648*η j*Fintype.card K) :
    (∑ i : Option J, ((Finset.univ \ properCoordinates p₁ p i).card : ℝ)) ≤
        34*(∑ j, η j)*Fintype.card K ∧
    (∑ i : Option J, ((Finset.univ.filter
      (fun x => coordinates f₁ f i x ≠ σ x)).card : ℝ)) ≤
        936*(∑ j, η j)*Fintype.card K := by
  classical
  have hj : η j₀ ≤ ∑ k, η k :=
    Finset.single_le_sum (fun k _ => hη k) (Finset.mem_univ j₀)
  have hq : (0 : ℝ) ≤ Fintype.card K := by positivity
  have hjq := mul_le_mul_of_nonneg_right hj hq
  have hps : (∑ j, ((Finset.univ \ p j).card : ℝ)) ≤
      17*(∑ j, η j)*Fintype.card K := by
    calc
      _ ≤ ∑ j, 17*η j*Fintype.card K := Finset.sum_le_sum (fun j _ => hp j)
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hfs : (∑ j, count (fun x => f j x ≠ σ x)) ≤
      648*(∑ j, η j)*Fintype.card K := by
    calc
      _ ≤ ∑ j, 648*η j*Fintype.card K := Finset.sum_le_sum (fun j _ => hf j)
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  constructor
  · simp only [Fintype.sum_option, properCoordinates]
    nlinarith
  · have hb : (∑ i : Option J, count (fun x => coordinates f₁ f i x ≠ σ x)) ≤
        936*(∑ j, η j)*Fintype.card K := by
      rw [Fintype.sum_option]
      change count (fun x => f₁ x ≠ σ x) +
        (∑ j, count (fun x => f j x ≠ σ x)) ≤ _
      nlinarith
    calc
      _ = ∑ i : Option J, count (fun x => coordinates f₁ f i x ≠ σ x) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (count_eq_card _).symm
      _ ≤ _ := hb

/-- Scalar coherence and both coordinate budgets in §6. -/
theorem coherent_coordinate_budget (j₀ : J) (σ : J → K →+* L)
    (f₁ : K → L) (f : J → K → L) (p₁ : Finset K) (p : J → Finset K)
    (η : J → ℝ) (hη : ∀ j, 0 ≤ η j) (hsum : (∑ j, η j) ≤ 1/10000000)
    (hfirst : ∀ j, count (fun x => f₁ x ≠ σ j x) ≤ 288*η j*Fintype.card K)
    (hp₁ : ((Finset.univ \ p₁).card : ℝ) ≤ 17*η j₀*Fintype.card K)
    (hp : ∀ j, ((Finset.univ \ p j).card : ℝ) ≤ 17*η j*Fintype.card K)
    (hf : ∀ j, count (fun x => f j x ≠ σ j x) ≤ 648*η j*Fintype.card K) :
    (∀ j, σ j = σ j₀) ∧
    (∑ i : Option J, ((Finset.univ \ properCoordinates p₁ p i).card : ℝ)) ≤
        34*(∑ j, η j)*Fintype.card K ∧
    (∑ i : Option J, ((Finset.univ.filter
      (fun x => coordinates f₁ f i x ≠ σ j₀ x)).card : ℝ)) ≤
        936*(∑ j, η j)*Fintype.card K := by
  classical
  have hc := embeddings_cohere j₀ σ f₁ η hη hsum hfirst
  refine ⟨hc, coordinate_budget j₀ (σ j₀) f₁ f p₁ p η hη hp₁ hp (hfirst j₀) ?_⟩
  intro j
  simpa only [hc j] using hf j

end Erdos85.IncidenceRepair.Chart
