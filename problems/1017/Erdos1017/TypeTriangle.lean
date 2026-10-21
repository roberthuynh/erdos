import Erdos1017.TypeBudget
import Erdos1017.PartialTriangleExists
import Erdos1017.TriangleConstructor

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem partial_triangle_type_partition (a : ℝ) (x : ι → ℝ) (t : Finset ι → ℝ)
    (ht : ∀ T,T.card ≠ 3 → t T=0) (ht0 : ∀ T,0 ≤ t T)
    (hpair : ∀ B,B.card=2 → subsetMoment t B ≤ ∏ i ∈ B,x i)
    (hquota : ∀ i,x i*((∑ j,x j)-a-x i) ≤ subsetMoment t {i}) :
    ∃ P : TypePartition (fun o : Option ι => o.elim a x),
      P.cost _=a*(∑ i,x i)-elementarySum Finset.univ x 2+∑ T,t T := by
  let v := partialTriangleMass a x t
  have hv : ∀ T,0 ≤ v T := partialTriangleMass_nonneg a x t ht ht0 hpair hquota
  have hroot (i : ι) : subsetMoment v {i}=a*x i := by
    rw [partialTriangleMass_moment a x t ht {i} (by simp) (by simp),quadraticRootMass_singleton_moment]
  have hminor (i j : ι) (hij : i ≠ j) : subsetMoment v {i,j}=x i*x j := by
    rw [partialTriangleMass_moment a x t ht {i,j} (by simp) (by simp [hij]),
      quadraticRootMass_pair_moment a x {i,j} (by simp [hij]),Finset.prod_pair hij]
  refine ⟨rootedTypePartition a x v hv hroot hminor,?_⟩
  rw [rootedTypePartition_cost]
  exact partialTriangleMass_total a x t ht

theorem triangle_type_partition_bound (a : ℝ) (x : ι → ℝ) (hb : 0 < ∑ i,x i)
    (T : PartialTriangleSupply a x) :
    ∃ P : TypePartition (fun o : Option ι => o.elim a x),
      P.cost _ ≤ a*(∑ i,x i)-(2*a+(∑ i,x i))*((∑ i,x i)^2-∑ i,(x i)^2)/(6*(∑ i,x i)) := by
  obtain ⟨P,hP⟩ := partial_triangle_type_partition a x T.mass T.supported T.nonneg T.pair_cap T.quota
  refine ⟨P,?_⟩
  let b := ∑ i,x i
  let Q := ∑ i,(x i)^2
  have he : elementarySum Finset.univ x 2=(b^2-Q)/2 := by
    have he := elementarySum_two_identity Finset.univ x
    linarith
  rw [he] at hP
  have ht := T.total
  change (∑ S,T.mass S) ≤ (b-a)*(b^2-Q)/(3*b) at ht
  have hid : a*b-(b^2-Q)/2+(b-a)*(b^2-Q)/(3*b)=a*b-(2*a+b)*(b^2-Q)/(6*b) := by
    have hb0 : b ≠ 0 := ne_of_gt hb
    field_simp
    ring
  change P.cost _ ≤ a*b-(2*a+b)*(b^2-Q)/(6*b)
  linarith

theorem high_root_type_partition (a : ℝ) (ha : 0 < a) (x : ι → ℝ)
    (hx : ∀ i,0 ≤ x i) (hmax : ∀ i,x i ≤ a) (hba : (∑ i,x i) ≤ 2*a) :
    ∃ P : TypePartition (fun o : Option ι => o.elim a x),P.cost _ ≤ typeBudget (fun o : Option ι => o.elim a x) := by
  let b := ∑ i,x i
  let Q := ∑ i,(x i)^2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  rcases le_total a b with hab | hab
  · have hb : 0 < b := ha.trans_le hab
    obtain ⟨T⟩ := partial_triangle_supply_exists x hx a hb (by linarith) hab hmax
    obtain ⟨P,hP⟩ := triangle_type_partition_bound a x hb T
    have hQcap : Q ≤ a*b := by
      calc
        _ ≤ ∑ i,a*x i := Finset.sum_le_sum (fun i _ => by nlinarith [hx i,hmax i])
        _ = _ := (Finset.mul_sum _ _ _).symm
    have H := triangle_budget_homogeneous a b Q ha hb hba hab hQ hQcap
    refine ⟨P,?_⟩
    rw [typeBudget_option]
    change P.cost _ ≤ (1-Real.sqrt 7/3)*(a+b)^2/4+(Real.sqrt 7/3)*(a^2+Q)/2
    change P.cost _ ≤ a*b-(2*a+b)*(b^2-Q)/(6*b) at hP
    nlinarith
  · have hquota (i : ι) : x i*(b-a-x i) ≤ subsetMoment (fun _ : Finset ι => (0:ℝ)) {i} := by
      simp only [subsetMoment,ite_self,Finset.sum_const_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (hx i) (by linarith [hx i])
    obtain ⟨P,hP⟩ := partial_triangle_type_partition a x (fun _ => 0)
      (fun _ _ => rfl) (fun _ => le_rfl)
      (fun B _ => by simpa [subsetMoment] using Finset.prod_nonneg (s := B) (f := x) (fun i _ => hx i)) hquota
    have he := elementarySum_two_identity Finset.univ x
    have hE := elementarySum_nonneg Finset.univ x (fun i _ => hx i) 2
    have hr : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg _
    have hrsq : (Real.sqrt 7)^2=7 := Real.sq_sqrt (by norm_num)
    have hr1 : Real.sqrt 7/3 ≤ 1 := by nlinarith
    have hgap : 0 ≤ (1+Real.sqrt 7/3)*(a-b)^2+4*(1-Real.sqrt 7/3)*elementarySum Finset.univ x 2 := by positivity
    refine ⟨P,?_⟩
    rw [typeBudget_option,hP]
    simp only [Finset.sum_const_zero,add_zero]
    change a*b-elementarySum Finset.univ x 2 ≤
      (1-Real.sqrt 7/3)*(a+b)^2/4+(Real.sqrt 7/3)*(a^2+Q)/2
    change 2*elementarySum Finset.univ x 2=b^2-Q at he
    have hew := congrArg (fun z : ℝ => (Real.sqrt 7/3)*z) he
    nlinarith

end Erdos1017
