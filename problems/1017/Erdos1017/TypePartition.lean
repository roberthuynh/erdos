import Erdos1017.RootedMassLift
import Erdos1017.TrianglePackingTransport

namespace Erdos1017
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Fractional product-capacity partitions on finite part labels. Small sets may
carry mass; they add cost and carry no pair, so the graph lift may discard them. -/
structure TypePartition (x : ι → ℝ) where
  mass : Finset ι → ℝ
  nonneg : ∀ T,0 ≤ mass T
  pair_exact : ∀ i j,i ≠ j → subsetMoment mass {i,j}=x i*x j

noncomputable def TypePartition.cost (x : ι → ℝ) (P : TypePartition x) : ℝ := ∑ T,P.mass T

noncomputable def TypePartition.rename (x : ι → ℝ) (e : κ ≃ ι) (P : TypePartition x) :
    TypePartition (fun i => x (e i)) where
  mass S := P.mass (e.finsetCongr S)
  nonneg S := P.nonneg _
  pair_exact i j hij := by
    rw [renamed_subsetMoment]
    simpa only [Equiv.finsetCongr_apply,Finset.map_insert,Finset.map_singleton,
      Equiv.toEmbedding_apply] using P.pair_exact (e i) (e j) (fun h => hij (e.injective h))

theorem TypePartition.rename_cost (x : ι → ℝ) (e : κ ≃ ι) (P : TypePartition x) :
    (P.rename x e).cost _=P.cost x := e.finsetCongr.sum_comp P.mass

/-- Lift arbitrary real type masses to an actual complete multipartite graph. -/
theorem TypePartition.to_graph {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (part : V → ι) (hG : ∀ u v,G.Adj u v ↔ part u ≠ part v)
    (hpos : ∀ i,0 < partSize part i) (P : TypePartition (fun i => (partSize part i : ℝ))) :
    ∃ Q : FractionalPartition G,Q.cost ≤ P.cost _ := by
  apply multipartite_partition_of_type_masses G part hG hpos P.mass P.nonneg
  intro i j hij
  simpa only [subsetMoment,Finset.insert_subset_iff,Finset.singleton_subset_iff] using P.pair_exact i j hij

noncomputable def rootedTypePartition (a : ℝ) (x : ι → ℝ) (v : Finset ι → ℝ)
    (hv : ∀ T,0 ≤ v T) (hroot : ∀ i,subsetMoment v {i}=a*x i)
    (hpair : ∀ i j,i ≠ j → subsetMoment v {i,j}=x i*x j) :
    TypePartition (fun o : Option ι => o.elim a x) where
  mass := aggregateMass rootedPartSet v
  nonneg := aggregateMass_nonneg rootedPartSet v hv
  pair_exact i j hij := by
    have h := aggregate_observable rootedPartSet v
      (fun S => if i ∈ S ∧ j ∈ S then (1:ℝ) else 0)
    simp only [mul_ite,mul_one,mul_zero] at h
    simp only [subsetMoment,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    rw [h]
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
        simpa only [none_mem_rootedPartSet,some_mem_rootedPartSet,true_and,Option.elim_none,
          Option.elim_some,subsetMoment,Finset.singleton_subset_iff] using hroot j
    | some i =>
      cases j with
      | none =>
        simpa only [none_mem_rootedPartSet,some_mem_rootedPartSet,and_true,Option.elim_none,
          Option.elim_some,subsetMoment,Finset.singleton_subset_iff,mul_comm] using hroot i
      | some j =>
        simpa only [some_mem_rootedPartSet,Option.elim_some,subsetMoment,
          Finset.insert_subset_iff,Finset.singleton_subset_iff] using hpair i j (fun h => hij (congrArg some h))

theorem rootedTypePartition_cost (a : ℝ) (x : ι → ℝ) (v : Finset ι → ℝ)
    (hv : ∀ T,0 ≤ v T) (hroot : ∀ i,subsetMoment v {i}=a*x i)
    (hpair : ∀ i j,i ≠ j → subsetMoment v {i,j}=x i*x j) :
    (rootedTypePartition a x v hv hroot hpair).cost _=∑ T,v T := by
  have h := aggregate_observable rootedPartSet v (fun _ => (1:ℝ))
  simpa only [TypePartition.cost,rootedTypePartition,mul_one] using h

end Erdos1017
