import Erdos1017.TypeRootLaws

namespace Erdos1017
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def zeroRootTypePartition (x : ι → ℝ) (P : TypePartition x) :
    TypePartition (fun o : Option ι => o.elim 0 x) where
  mass := zeroRootMass P.mass
  nonneg := aggregateMass_nonneg _ P.mass P.nonneg
  pair_exact i j hij := by
    cases i with
    | none =>
      rw [zeroRootMass_root_moment _ _ (by simp)]
      simp
    | some i =>
      cases j with
      | none =>
        rw [zeroRootMass_root_moment _ _ (by simp)]
        simp
      | some j =>
        have h := zeroRootMass_minor_moment P.mass {i,j}
        simp only [Finset.image_insert,Finset.image_singleton] at h
        rw [h]
        exact P.pair_exact i j (fun h => hij (congrArg some h))

theorem zeroRootTypePartition_cost (x : ι → ℝ) (P : TypePartition x) :
    (zeroRootTypePartition x P).cost _=P.cost x := by
  have h := aggregate_observable (fun T : Finset ι => T.image some) P.mass (fun _ => (1:ℝ))
  simpa only [TypePartition.cost,zeroRootTypePartition,zeroRootMass,mul_one] using h

/-- Scale an enlarged-root partition and fill precisely the remaining minor pairs. -/
noncomputable def inflateTypePartition (a A τ : ℝ) (x : ι → ℝ)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (ha : τ*A=a)
    (R : TypePartition (fun o : Option ι => o.elim A x)) (P : TypePartition x) :
    TypePartition (fun o : Option ι => o.elim a x) where
  mass S := τ*R.mass S+(1-τ)*(zeroRootTypePartition x P).mass S
  nonneg S := add_nonneg (mul_nonneg hτ (R.nonneg S))
    (mul_nonneg (sub_nonneg.mpr hτ1) ((zeroRootTypePartition x P).nonneg S))
  pair_exact i j hij := by
    rw [subsetMoment_add,subsetMoment_mul,subsetMoment_mul,R.pair_exact i j hij,
      (zeroRootTypePartition x P).pair_exact i j hij]
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => simp only [Option.elim_none,Option.elim_some]; rw [← ha]; ring
    | some i =>
      cases j with
      | none => simp only [Option.elim_none,Option.elim_some]; rw [← ha]; ring
      | some j => simp only [Option.elim_some]; ring

theorem inflateTypePartition_cost (a A τ : ℝ) (x : ι → ℝ)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (ha : τ*A=a)
    (R : TypePartition (fun o : Option ι => o.elim A x)) (P : TypePartition x) :
    (inflateTypePartition a A τ x hτ hτ1 ha R P).cost _=τ*R.cost _+(1-τ)*P.cost x := by
  change (∑ S : Finset (Option ι), (τ*R.mass S+(1-τ)*((zeroRootTypePartition x P).mass S)))=_
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  change τ*R.cost _+(1-τ)*(zeroRootTypePartition x P).cost _=_
  rw [zeroRootTypePartition_cost]

end Erdos1017
