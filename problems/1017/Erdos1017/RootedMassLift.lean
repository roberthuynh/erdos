import Erdos1017.RootedTypeLift

namespace Erdos1017
open scoped BigOperators
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- Unnormalized rooted masses require the individual edge loads only. -/
theorem multipartite_partition_of_rooted_masses (G : SimpleGraph V) (part : V → Option ι)
    (hG : ∀ u v, G.Adj u v ↔ part u ≠ part v)
    (hpos : ∀ i, 0 < partSize part i) (v : Finset ι → ℝ) (hv : ∀ T, 0 ≤ v T)
    (hroot : ∀ i, (∑ T : Finset ι, if i ∈ T then v T else 0) =
      (partSize part none : ℝ)*partSize part (some i))
    (hminor : ∀ i j, i ≠ j → (∑ T : Finset ι, if i ∈ T ∧ j ∈ T then v T else 0) =
      (partSize part (some i) : ℝ)*partSize part (some j)) :
    ∃ P : FractionalPartition G, P.cost ≤ ∑ T,v T := by
  let W : Finset (Option ι) → ℝ := aggregateMass rootedPartSet v
  have hW : ∀ T, 0 ≤ W T := aggregateMass_nonneg rootedPartSet v hv
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
  simpa only [mul_one] using h

end Erdos1017
