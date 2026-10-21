import Erdos1017.TypeTriangle
import Erdos1017.TypeInflationScalar

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The only recursive sector invokes a partition of the strictly smaller minor index type. -/
theorem inflation_type_partition (a : ℝ) (ha : 0 < a) (x : ι → ℝ)
    (hx : ∀ i,0 ≤ x i) (hmax : ∀ i,x i ≤ a)
    (hab : 2*a ≤ ∑ i,x i) (hsize : 8*(∑ i,x i) ≤ 17*a)
    (P : TypePartition x) (hP : P.cost x ≤ typeBudget x) :
    ∃ R : TypePartition (fun o : Option ι => o.elim a x),
      R.cost _ ≤ typeBudget (fun o : Option ι => o.elim a x) := by
  let b := ∑ i,x i
  let Q := ∑ i,(x i)^2
  let τ := 2*a/b
  have hb : 0 < b := by linarith
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hτ : 0 ≤ τ := div_nonneg (by positivity) hb.le
  have hτ1 : τ ≤ 1 := (div_le_one hb).mpr hab
  have hτa : τ*(b/2)=a := by dsimp [τ]; field_simp
  obtain ⟨T⟩ := partial_triangle_supply_exists x hx (b/2) hb le_rfl (by linarith)
    (fun i => (hmax i).trans (by linarith))
  obtain ⟨R,hR⟩ := triangle_type_partition_bound (b/2) x hb T
  have hRc : R.cost _ ≤ b^2/6+Q/3 := by
    change R.cost _ ≤ (b/2)*b-(2*(b/2)+b)*(b^2-Q)/(6*b) at hR
    have he : (b/2)*b-(2*(b/2)+b)*(b^2-Q)/(6*b)=b^2/6+Q/3 := by field_simp; ring
    rwa [he] at hR
  refine ⟨inflateTypePartition a (b/2) τ x hτ hτ1 hτa R P,?_⟩
  rw [inflateTypePartition_cost,typeBudget_option]
  have hR' := mul_le_mul_of_nonneg_left hRc hτ
  have hP' := mul_le_mul_of_nonneg_left hP (sub_nonneg.mpr hτ1)
  have H := type_inflation_scalar a b Q ha.le hb hQ hsize
  dsimp [typeBudget] at hP'
  change τ*R.cost _+(1-τ)*P.cost x ≤
    (1-Real.sqrt 7/3)*(a+b)^2/4+(Real.sqrt 7/3)*(a^2+Q)/2
  nlinarith

end Erdos1017
