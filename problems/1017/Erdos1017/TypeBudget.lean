import Erdos1017.TypeInflation
import Erdos1017.RectangleAffine
import Erdos1017.TriangleHomogeneous

namespace Erdos1017
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def typeBudget (x : ι → ℝ) : ℝ :=
  (1-Real.sqrt 7/3)*(∑ i,x i)^2/4+(Real.sqrt 7/3)*(∑ i,(x i)^2)/2

theorem typeBudget_rename (x : ι → ℝ) (e : κ ≃ ι) :
    typeBudget (fun i => x (e i))=typeBudget x := by
  simp only [typeBudget,e.sum_comp x,e.sum_comp (fun i => (x i)^2)]

theorem typeBudget_option (a : ℝ) (x : ι → ℝ) :
    typeBudget (fun o : Option ι => o.elim a x)=
      (1-Real.sqrt 7/3)*(a+∑ i,x i)^2/4+(Real.sqrt 7/3)*(a^2+∑ i,(x i)^2)/2 := by
  simp only [typeBudget,Fintype.sum_option,Option.elim_none,Option.elim_some]

theorem rooted_budget_scaling (a : ℝ) (ha : 0 < a) (x : ι → ℝ) :
    a^2*normalizedAffineBudget (∑ i,x i/a) (∑ i,(x i/a)^2)=
      typeBudget (fun o : Option ι => o.elim a x) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hn : a*((∑ i,x i/a)+1)=a+∑ i,x i := by
    rw [mul_add,Finset.mul_sum,mul_one]
    have he (i : ι) : a*(x i/a)=x i := by field_simp
    simp_rw [he]
    ring
  have hQ : a^2*(∑ i,(x i/a)^2)=∑ i,(x i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hn2 := congrArg (fun z : ℝ => z^2) hn
  have hn2' : a^2*((∑ i,x i/a)+1)^2=(a+∑ i,x i)^2 := by nlinarith
  rw [typeBudget_option]
  unfold normalizedAffineBudget
  have h1 := congrArg (fun z : ℝ => (1-Real.sqrt 7/3)*z/4) hn2'
  have h2 := congrArg (fun z : ℝ => (Real.sqrt 7/3)*z/2) hQ
  nlinarith

/-- The independent cost a² suffices when the largest weight is at most 2/9. -/
theorem low_type_budget (a : ℝ) (ha : 0 ≤ a) (x : ι → ℝ)
    (hx : ∀ i,0 ≤ x i) (hsize : 9*a ≤ 2*(a+∑ i,x i)) :
    a^2 ≤ typeBudget (fun o : Option ι => o.elim a x) := by
  let n := a+∑ i,x i
  have hn : 0 ≤ n := add_nonneg ha (Finset.sum_nonneg (fun i _ => hx i))
  have hs2 : 81*a^2 ≤ 4*n^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsize) (show 0 ≤ 2*n+9*a by positivity)]
  have hsq : (Real.sqrt 7)^2=7 := Real.sq_sqrt (by norm_num)
  have hr : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg _
  have hrmax : Real.sqrt 7 ≤ (195:ℝ)/73 := by nlinarith
  have hc : 0 ≤ 1-Real.sqrt 7/6 := by nlinarith
  have hweighted := mul_le_mul_of_nonneg_left hs2 hc
  have hmargin := mul_nonneg (show 0 ≤ 195-73*Real.sqrt 7 by linarith) (sq_nonneg n)
  have hQ : 0 ≤ (Real.sqrt 7/3)*(∑ i,(x i)^2) := mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun i _ => sq_nonneg (x i)))
  rw [typeBudget_option]
  change a^2 ≤ (1-Real.sqrt 7/3)*n^2/4+(Real.sqrt 7/3)*(a^2+∑ i,(x i)^2)/2
  nlinarith

end Erdos1017
