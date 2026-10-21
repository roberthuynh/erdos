import Erdos1017.TypePartition
import Erdos1017.RootedSelector

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def boolSelected (f : ι → Bool) : Finset ι := Finset.univ.filter (fun i => f i=true)

noncomputable def independentTypePartition (a : ℝ) (ha : 0 < a) (x : ι → ℝ)
    (hx : ∀ i,0 ≤ x i) (hmax : ∀ i,x i ≤ a) : TypePartition x where
  mass := aggregateMass boolSelected (rootedMass a x)
  nonneg := aggregateMass_nonneg boolSelected (rootedMass a x) (rootedMass_nonneg ha x hx hmax)
  pair_exact i j hij := by
    have h := aggregate_observable boolSelected (rootedMass a x)
      (fun S => if i ∈ S ∧ j ∈ S then (1:ℝ) else 0)
    simp only [mul_ite,mul_one,mul_zero] at h
    simp only [subsetMoment,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    rw [h]
    have he := rooted_pair_load (ne_of_gt ha) x i j hij
    have heq (f : ι → Bool) :
        (if i ∈ boolSelected f ∧ j ∈ boolSelected f then rootedMass a x f else 0)=
        rootedMass a x f*((if f i then 1 else 0)*(if f j then 1 else 0)) := by
      cases hi : f i <;> cases hj : f j <;> simp [boolSelected,hi,hj]
    simp_rw [heq]
    exact he

theorem independentTypePartition_cost (a : ℝ) (ha : 0 < a) (x : ι → ℝ)
    (hx : ∀ i,0 ≤ x i) (hmax : ∀ i,x i ≤ a) :
    (independentTypePartition a ha x hx hmax).cost x=a^2 := by
  have h := aggregate_observable boolSelected (rootedMass a x) (fun _ => (1:ℝ))
  simp only [mul_one] at h
  exact h.trans (rooted_total a x)

theorem type_partition_of_subset_law (a : ℝ) (ha : 0 < a) (x : ι → ℝ)
    (w : Finset ι → ℝ) (hw : ∀ T,0 ≤ w T)
    (hmom : ∀ B : Finset ι,B.card ≤ 2 → subsetMoment w B=∏ i ∈ B,x i/a) :
    ∃ P : TypePartition (fun o : Option ι => o.elim a x),
      P.cost _=a^2*(∑ T : Finset ι,if T.Nonempty then w T else 0) := by
  let v : Finset ι → ℝ := fun T => if T.Nonempty then a^2*w T else 0
  have hv (T : Finset ι) : 0 ≤ v T := by
    dsimp [v]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hw T)
    · exact le_rfl
  have hroot (i : ι) : subsetMoment v {i}=a*x i := by
    have h := nonempty_restriction_moment w a {i} (by simp)
    rw [hmom {i} (by simp)] at h
    simp only [Finset.prod_singleton] at h
    change subsetMoment v {i}=a^2*(x i/a) at h
    rw [h]
    field_simp
  have hpair (i j : ι) (hij : i ≠ j) : subsetMoment v {i,j}=x i*x j := by
    have h := nonempty_restriction_moment w a {i,j} (by simp)
    rw [hmom {i,j} (by simp [hij]),Finset.prod_pair hij] at h
    change subsetMoment v {i,j}=a^2*(x i/a*(x j/a)) at h
    rw [h]
    field_simp
  refine ⟨rootedTypePartition a x v hv hroot hpair,?_⟩
  rw [rootedTypePartition_cost,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  dsimp [v]
  split_ifs <;> simp

end Erdos1017
