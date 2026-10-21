import Erdos1017.TypeLift
import Erdos1017.SubsetMoments

namespace Erdos1017
open scoped BigOperators
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

noncomputable def rootedPartSet (T : Finset ι) : Finset (Option ι) :=
  insert none (T.image some)

@[simp] theorem none_mem_rootedPartSet (T : Finset ι) : none ∈ rootedPartSet T := by
  simp [rootedPartSet]

@[simp] theorem some_mem_rootedPartSet (T : Finset ι) (i : ι) : some i ∈ rootedPartSet T ↔ i ∈ T := by
  simp [rootedPartSet]

theorem nonempty_restriction_moment (w : Finset ι → ℝ) (a : ℝ)
    (B : Finset ι) (hB : B.Nonempty) :
    (∑ T : Finset ι, if B ⊆ T then (if T.Nonempty then a^2*w T else 0) else 0) =
      a^2*subsetMoment w B := by
  unfold subsetMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hBT : B ⊆ T
  · simp [hBT, hB.mono hBT]
  · simp [hBT]

/-- An arbitrary correlated minor-subset law lifts with its nonempty cost.
The root is the `none` part; `some i` labels every other nonempty part. -/
theorem multipartite_partition_of_rooted_law (G : SimpleGraph V) (part : V → Option ι)
    (hG : ∀ u v, G.Adj u v ↔ part u ≠ part v)
    (hpos : ∀ i, 0 < partSize part i) (w : Finset ι → ℝ) (hw : ∀ T, 0 ≤ w T)
    (hmom : ∀ B : Finset ι, B.card ≤ 2 → subsetMoment w B =
      ∏ i ∈ B, ((partSize part (some i) : ℝ)/(partSize part none))) :
    ∃ P : FractionalPartition G, P.cost ≤ (partSize part none : ℝ)^2 *
      (∑ T : Finset ι, if T.Nonempty then w T else 0) := by
  let a : ℝ := partSize part none
  have ha : 0 < a := by dsimp [a]; exact_mod_cast hpos none
  let v : Finset ι → ℝ := fun T => if T.Nonempty then a^2*w T else 0
  let W : Finset (Option ι) → ℝ := aggregateMass rootedPartSet v
  have hv (T : Finset ι) : 0 ≤ v T := by
    dsimp [v]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hw T)
    · exact le_rfl
  have hW : ∀ T, 0 ≤ W T := aggregateMass_nonneg rootedPartSet v hv
  have hroot (i : ι) : (∑ T : Finset ι, if i ∈ T then v T else 0) =
      a*(partSize part (some i) : ℝ) := by
    have h := nonempty_restriction_moment w a {i} (Finset.singleton_nonempty i)
    rw [hmom {i} (by simp)] at h
    simp only [Finset.singleton_subset_iff, Finset.prod_singleton] at h
    change _ = a*((partSize part (some i) : ℝ))
    rw [h]
    change a^2*((partSize part (some i) : ℝ)/a) = _
    field_simp
  have hminor (i j : ι) (hij : i ≠ j) :
      (∑ T : Finset ι, if i ∈ T ∧ j ∈ T then v T else 0) =
        (partSize part (some i) : ℝ)*partSize part (some j) := by
    have h := nonempty_restriction_moment w a {i,j} (by simp)
    rw [hmom {i,j} (by simp [hij])] at h
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff] at h
    rw [h]
    simp only [Finset.prod_pair hij]
    change a^2*((partSize part (some i) : ℝ)/a*((partSize part (some j) : ℝ)/a)) = _
    field_simp
  have hload (i j : Option ι) (hij : i ≠ j) :
      (∑ T : Finset (Option ι), if i ∈ T ∧ j ∈ T then W T else 0) =
        (partSize part i : ℝ)*partSize part j := by
    have h := aggregate_observable rootedPartSet v (fun T => if i ∈ T ∧ j ∈ T then (1:ℝ) else 0)
    simp only [mul_ite, mul_one, mul_zero] at h
    change (∑ T : Finset (Option ι), if i ∈ T ∧ j ∈ T then aggregateMass rootedPartSet v T else 0) = _
    rw [h]
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => simpa only [none_mem_rootedPartSet, some_mem_rootedPartSet, true_and] using hroot j
    | some i =>
      cases j with
      | none => simpa only [none_mem_rootedPartSet, some_mem_rootedPartSet, and_true, mul_comm] using hroot i
      | some j =>
        simpa only [some_mem_rootedPartSet] using hminor i j (fun h => hij (congrArg some h))
  obtain ⟨P,hP⟩ := multipartite_partition_of_type_masses G part hG hpos W hW hload
  refine ⟨P, hP.trans_eq ?_⟩
  have h := aggregate_observable rootedPartSet v (fun _ => (1:ℝ))
  simp only [mul_one] at h
  change (∑ T : Finset (Option ι), aggregateMass rootedPartSet v T) = _
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  dsimp [v,a]
  split_ifs <;> simp

end Erdos1017
