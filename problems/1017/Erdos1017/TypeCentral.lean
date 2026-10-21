import Erdos1017.CentralSector
import Erdos1017.TypeBudget

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem low_type_partition (a : ℝ) (ha : 0 < a) (x : ι → ℝ)
    (hx : ∀ i,0 ≤ x i) (hmax : ∀ i,x i ≤ a) (hsize : 9*a ≤ 2*(a+∑ i,x i)) :
    ∃ P : TypePartition (fun o : Option ι => o.elim a x),
      P.cost _ ≤ typeBudget (fun o : Option ι => o.elim a x) := by
  let y : Option ι → ℝ := fun o => o.elim a x
  have hy : ∀ i,0 ≤ y i := by intro i; cases i; exact ha.le; exact hx _
  have hymax : ∀ i,y i ≤ a := by intro i; cases i; exact le_rfl; exact hmax _
  refine ⟨independentTypePartition a ha y hy hymax,?_⟩
  rw [independentTypePartition_cost]
  exact low_type_budget a ha.le x hx hsize

theorem central_type_partition (a : ℝ) (ha : 0 < a) (x : ι → ℝ)
    (hx : ∀ i,0 ≤ x i) (hmax : ∀ i,x i ≤ a)
    (hSl : (17:ℝ)/8 ≤ ∑ i,x i/a) (hSh : (∑ i,x i/a) ≤ (7:ℝ)/2) :
    ∃ P : TypePartition (fun o : Option ι => o.elim a x),
      P.cost _ ≤ typeBudget (fun o : Option ι => o.elim a x) := by
  let p : ι → ℝ := fun i => x i/a
  let q := ∑ i,(p i)^2
  have hp : ∀ i,0 ≤ p i := fun i => div_nonneg (hx i) ha.le
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _ => sq_nonneg (p i))
  rcases le_total q ((16:ℝ)/25) with hsmall | hlarge
  · let m := Real.sqrt q
    have hm : 0 ≤ m := Real.sqrt_nonneg _
    have hmsq : m^2=q := Real.sq_sqrt hq
    have hpm (i : ι) : p i ≤ m := by
      have hs : (p i)^2 ≤ q := Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
      nlinarith [hp i]
    have hmcap : m ≤ (4:ℝ)/5 := by nlinarith
    obtain ⟨w,hw,hmom,hcost⟩ := continuous_sharp_selector p m hp hpm hmsq.symm hSl hSh hm hmcap
    obtain ⟨P,hP⟩ := type_partition_of_subset_law a ha x w hw hmom
    refine ⟨P,?_⟩
    rw [hP,← rooted_budget_scaling a ha x]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
    simpa only [hmsq] using hcost
  · let y : Option ι → ℝ := fun o => o.elim a x
    have hy : ∀ i,0 ≤ y i := by intro i; cases i; exact ha.le; exact hx _
    have hymax : ∀ i,y i ≤ a := by intro i; cases i; exact le_rfl; exact hmax _
    refine ⟨independentTypePartition a ha y hy hymax,?_⟩
    rw [independentTypePartition_cost,← rooted_budget_scaling a ha x]
    have h := large_square_normalized_budget (∑ i,p i) q hSl hlarge
    simpa using mul_le_mul_of_nonneg_left h (sq_nonneg a)

end Erdos1017
